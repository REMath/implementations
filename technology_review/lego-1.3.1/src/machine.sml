(* machine.ml *)

val mach_debug = ref false
val gen_debug = ref false

functor FunMachine (structure Error:ERROR) (* : MACHINE *) =
struct
  type cnstr = cnstr
  type projSort = projSort
  type binding = binding

  fun ConsiderVar n t = (Var(n,t),coerceGe t)
  fun ConsiderProp() = (Prop,mkTyp(uconst 0))
  fun ConsiderTheory() = (Theory,mkTyp(uconst 0))

  fun ConsiderType(s) =
    let
      fun typez i = 
	case theory()
	  of xtndCC => (mkTyp(i),mkTyp(uvar "" [UniGt i]))
	   | _      => bug"typez"
    in typez (uvar s [])
    end

  fun ConsiderTypen(n) = (mkTyp(uconst n),mkTyp(uconst (n+1)));

  fun arg_occur (Bind ((Pi,_),_,dom,ran)) br =
      depends br dom orelse arg_occur ran br
    | arg_occur _ _ = false

  fun letize (V,T) br =
    let val ((_,vis),s,c,_) = ref_bd br
    in (MkBind((Let,vis),s,c,subst2 br V),
	coerceGe(MkBind((Let,vis),s,c,subst2 br T)))
    end;

  fun abstract (V,T) br =
    let
      val ((_,vis),s,c,t) = ref_bd br
      val vis = if vis = VBot
                then if arg_occur T br then Hid else Vis
                else vis
      fun abstr() = (MkBind((Lda,vis),s,c,subst2 br V),
		     MkBind((Pi,vis),s,c,subst2 br T))
      fun fail1() = (prs("attempt to abstract "^s^" : "); prnt_vt_expand c t;
		     failwith"LF: only a Prop may be the domain of a function")
      fun fail2() = (prs"attempt to abstract over ";prnt_vt_expand V (whnf T);
		     failwith"Pure CC: Type may not be the range of a function")
    in case theory()
	 of pureCC => (case whnf T
			 of (Type _) => fail2()
			  | _        => abstr())
	  | xtndCC => abstr()
	  | lf     => if t = Prop then abstr() else fail1()
    end;

  fun generalize (V,T) br =
    let
      val _ = if !gen_debug then (prs("\n** gen debug ** "^ref_nam br^", ");
				  prnt_vt V T)
	      else()
      val ((_,vis),s,c,t) = ref_bd br
      val vis = if vis = VBot
                then if arg_occur V br then Hid else Vis
                else vis
      val typ =
	case (t,whnf T)
	  of (_,Prop)          => Prop
	   | (Prop,Type(i))    => mkTyp(i)  (* new level var NOT needed here *)
	   | (Type(j),Type(i)) => mkTyp(uvar "" [UniGe(i),UniGe(j)])
	   | _ => (prs"attempt to generalize over "; prnt_vt_expand V T;
		   failwith "only a Prop or a Type may be the range of a product")
      fun genlz() = (MkBind((Pi,vis),s,c,subst2 br V),typ)
      fun failure() = (prs("Attempt to generalize "^s^" : ");
		       prnt_vt_expand c t;
		       failwith"LF: only a Prop may be the domain of a function")
    in case theory() of xtndCC => genlz()
  | pureCC => genlz()
  | lf     => if t = Prop then genlz() else failure()
    end;

  fun sigize (V,T) br =
    let
      val ((_,vis),s,c,t) = ref_bd br
      val typ =
	case (t,whnf T)
	  of (Prop,Prop) => if (!PredicativeSums) then mkTyp(uconst 0)
			    else Prop
	   | (Prop,Ti as Type(i)) => Ti
	   | (Ti as Type(i),Prop) => Ti
	   | (Type(j),Type(i)) => mkTyp(uvar "" [UniGe(i),UniGe(j)])
	   | (t,T) => (message"Error typechecking SIGMA:";
		       prnt_vt V T; legoprint T;
		       failwith"the domain and range of SIGMA must be Props or Types")
      fun sigz() = (MkBind((Sig,vis),s,c,subst2 br V),typ)
      fun failure() = failwith"No SIGMA in current theory"
    in case theory()
	 of xtndCC => sigz()
	  | pureCC => failure()
	  | lf     => failure()
    end;


  fun Apply sbst mkVar pv (VTf as (Vf,Tf)) (VTa as (Va,Ta)) =
    let val Tf = whnf (sub sbst Tf)
    in case (pv,Tf,VTa)
	 of (ShowNorm,Bind((Pi,Hid),nam,dom,rng),_) =>
	   let val var = mkVar dom
	     val newVf = App((Vf,[var]),[NoShow])
	   in Apply sbst mkVar ShowNorm (newVf,coerceGe (subst1 var rng)) VTa
	   end
	  | (ShowForce,Bind((Pi,Hid),nam,dom,rng),_)  =>
	      Apply sbst mkVar ShowForce (Vf,Bind((Pi,Vis),nam,dom,rng)) VTa
	  | (NoShow,Bind((Pi,Hid),nam,dom,rng),_)  =>
	      Apply sbst mkVar NoShow (Vf,Bind((Pi,Vis),nam,dom,rng)) VTa
	  | (pv,Bind((Pi,Vis),_,dom,_),(Bot,Bot)) =>
	      Apply sbst mkVar pv VTf (mkVar dom,dom)
	  | (pv,Bind((Pi,Vis),nam,dom,rng),_) =>
	      let
		val _ = if not (!mach_debug) then ()
			else (message"** mach_deb; App";
			      legoprint Vf; legoprint Va)
	      in case par_unif sbst Ta dom of
		SOME(s) => ((MkApp((Vf,[Va]),[pv]),coerceGe (subst1 Va rng)),s)
	      | NONE => raise Error.error (Error.APPLNTYPE,NONE,
					   [Vf,dnf dom,Va,dnf Ta])
	      end
	  | (_,Bind((Pi,_),_,_,_),_) => bug"Apply; unknown Pi"
	  | _  => raise Error.error (Error.APPLNNFUN,NONE,[Vf, dnf Tf])
    end;

  (* (eager) Projections of Sigma *)
  fun Projection proj (V,T) =
    case whnf T of
      Bind((Sig,_),s,d,r) =>
	(case (V,proj)
	   of (Tuple(_,c::cs),Fst) => (c,d)
	    | (Tuple(_,c::cs),Snd) => let val r = subst1 c r
				      in  (MkTuple(r,cs),r)
				      end
	    | (_,Fst) => (MkProj(proj,V),d)
	    | (_,Snd) => (MkProj(proj,V),MkBind((Let,Def),s,MkProj(Fst,V),r))
	    | _ => bug"Projection1")
    | whnfT => (prs"\nattempt to project\n  ";
		prnt_vt_expand V (dnf whnfT);
		failwith"Projection: type of body not a SIG");
(***********************************************
  (* Projections of Sigma *)
  fun Projection proj (V,T) = 
    case whnf T
      of Bind((Sig,_),s,d,r)
        => let val X = case proj
                         of Fst => d
                          | Snd => MkBind((Let,Def),s,MkProj(Fst,V),r)
                          | Labl _ => bug"Projection"
           in  (MkProj(proj,V),coerceGe X) end
      | _  => (prs"\nattempt to project\n  ";
               prnt_vt_expand V (dnf (whnf T));
               failwith"Projection: type of body not a SIG");
*********************************************)



    (**   tuples  **)
  local
    (* for our tuple representation we need a "Sigma normal form": all
     * rightmost Sigmas must be explicit *)
    fun errRpt t T lr = (message"constructing tuple:";
			 legoprint t; 
			 message"isn't a specialization of";
			 legoprint T;
			 failwith("tuple doesn't have purported type on "^lr))
    fun chkTpl (T:cnstr) (vts:(cnstr*cnstr)list) sbst = 
      case (whnf T,vts)
	of (Bind((Sig,_),_,tl,tr),(v,t)::(vts as _::_)) =>
	  (case par_unif sbst t tl
	     of SOME(sbst) => chkTpl (subst1 v tr) vts sbst
	      | NONE => errRpt t tl "left")
	 | (T,[(v,t)]) => (case par_unif sbst t T
			     of SOME(sbst) => sbst
			      | NONE =>  errRpt t T "right")
	 | _ => failwith"tuple doesn't have a Sigma type"
  in
    fun tuplize sbst Bot (vts as _::_::_) =  (* infer the flat product.. *)
      let fun mkT t T = Bind((Sig,VBot),"",t,T)
	val T = foldr1 mkT (map snd vts) handle Empty _ => bug"tuplize"
	val _ = type_of_constr T     (* check T has a type *)
      in  tuplize sbst T vts
      end
      | tuplize sbst T (vts as _::_::_) = (* .. or use the given Sigma type *)
	let val sbst = chkTpl T vts sbst
	in  ((MkTuple(T,map fst vts),T),sbst)
	end
      | tuplize _ _ _ = bug"tuplizec"
  end;

end (* FunMachine *)
