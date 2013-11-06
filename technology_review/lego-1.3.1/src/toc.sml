(* toc.ml   compute type of an closed abstract construction *)


fun kind T = case whnf T of Prop => true | Type(_) => true | _ => false;

fun coerceGe c = c;

  (* projections from Theories: shared with machine *)
fun TheoryProject(V,n) =
  case thryUMwhnf V of  (* theory must be in whnf to see it's labels *)
    Bind((Thry,_),_,_,CnLst lvts) => 
      let 
	fun assoc (LabVT(Name l,_,A)::rest) = if n=l then A else assoc rest
	  | assoc [] = failwith("label `"^n^"' doesn't occur in Theory")
	  | assoc _ = bug"TheoryProject; assoc"
	val A = assoc lvts
      in (Proj(Labl n,V),subst1 V A)
      end
(********************************
     | Bind(bvs as (Lda,vs),nam,lft,rht) =>    (* !!not checked!! *)
	 let val (V,T) = TheoryProject(rht,n)
	 in  (Bind(bvs,nam,lft,V),Bind((Pi,vs),nam,lft,T))
	 end
*****************)
     | _ => (message("Cannot theory project \""^n^"\" from ");
		     legoprint V;
		     failwith"Theory projection fails")


(* Compute the type of an (abstract) construction.
 * Fix an (abstract) construction after reduction may have
 * destroyed its "visibility" incorrect
 *)
val toc_debug = ref false;
local
  fun assume d cxt = d::cxt
  and typ n cxt = lift n (nth cxt n handle Nth _ => bug"toc: Nth raised")
  and toc cxt c =
    let
      val t = toc_rec cxt c handle Failure s =>
	(prs"\ntoc fail on: "; legoprint c; failwith s)
      val _ = if (!toc_debug) then (prs"*toc1* "; prnt_vt c t)
	      else()
    in t
    end
  and toc_rec cxt =
    let
    in 
      fn Ref(br)       => ref_typ br
       | Prop          => mkTyp(uconst 0)
       | Theory        => mkTyp(uconst 0)
       | Type(Uconst n)=> mkTyp(uconst (n+1))
       | Type(n)       => mkTyp(uvar "" [UniGt(n)])
       | Var(_,c)      => c
       | Rel(n)        => typ n cxt
       | Bind((Let,_),_,v,b) => toc cxt (subst1 v b)
                      (** old:  toc (assume (toc cxt v) cxt) b   **)
       | Bind((Thry,_),_,_,_) => Theory
       | LabVT(_,_,T) => T
       | appTrm as (App((f,cs),_)) =>
	   let val _ = if (!toc_debug) then (prs"*tocApp* "; legoprint appTrm)
                       else()
             fun toa ft a =
	     let
               val whnfft = whnf ft
	       val t = 
                 case whnfft
		   of Bind((Pi,_),_,_,r) => subst1 a r
	            | _ => (prs"*tocAppErr* ";legoprint whnfft;
                            bug"toc:application of a non-function")
	       val _ = if (!toc_debug) then (prs"*tocApp1* "; legoprint t)
		       else()
	     in t
	     end
	   in foldl toa (toc cxt f) cs
	   end
       | Bind((Lda,v),n,d,r) =>
	   MkBind((Pi,v),n,d,toc (assume d cxt) r)
       | Bind((Pi,_),n,d,r) =>
	   (case (whnf(toc cxt d),whnf(toc (assume d cxt) r)) 
	      of (_,Prop)          => Prop
	       | (Prop,Ti as (Type i)) => Ti
	       | (Type(j),Type(i)) => mkTyp(uvar "" [UniGe(i),UniGe(j)])
	       | _                 => bug"type_of_constr;Pi")
       | Bind((Sig,_),_,d,r) =>
	   (case (whnf (toc cxt d),whnf (toc (d::cxt) r))
	      of (Prop,Prop) => if (!PredicativeSums) then mkTyp(uconst 0)
				else Prop
	       | (Prop,Ti as Type(_)) => Ti
	       | (Ti as Type(_),Prop) => Ti
	       | (Type(j),Type(i)) => mkTyp(uvar "" [UniGe(i),UniGe(j)])
	       | _                 => bug"type_of_constr;Sig")
       | Tuple(T,_) => T
       | Proj(Labl(l),V) => snd (TheoryProject(V,l))  (*****)
       | Proj(p,c) =>
	   (case whnf (toc cxt c)
	      of Bind((Sig,_),_,d,r) => if p=Fst then d
					else subst1 (MkProj(Fst,c)) r
	       | _                   => bug"type_of_constr;Proj")
       | RedTyp(iNrml,c) => UMnorm(toc cxt c)         (**** temp *****)
       | CnLst _ => bug"type_of_constr:CnLst"
       | Bot           => bug"type_of_constr:Bot"
    end
in
  fun type_of_constr c =
    let
      val _ = if not (!toc_debug) then ()
	      else (prs"*toc* input "; legoprint c)
      val T = toc [] c
      val _ = if not (!toc_debug) then ()
	      else (prs"*toc* output "; legoprint T)
    in  T
    end
(********  trying to fix up implicits after reduction  ********
  fun fixImplicits c =
    let
      fun fiRec cxt =
	fn t as (App(bod as ((fa as (f,_)),v::vs))) =>
	case (toc cxt f,v) of
	  (Bind((_,Vis),_,_,_),_) => mkApp (toc cxt) bod
	| (Bind((_,Hid),_,_,_),Vis) => mkApp (toc cxt) (fa,ShowForce::vs)
	| _ => (prs"\n"; print_expand t; bug"fixImplicits")
**************************************************************)

end;
      
toc:= type_of_constr   (* fix foward referencing used in esUM *)
