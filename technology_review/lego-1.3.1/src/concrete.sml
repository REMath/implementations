(* concrete.sml *)

val eval_debug = ref false;
val hold_T = ref Bot;
val hold_cnj = ref Bot;


functor FunConcrete (structure Namespace:NAMESPACE
		     structure Machine:MACHINE)
(* : CONCRETE *)
  =
struct
(* La syntaxe concrete *)
datatype cnstr_c =
  Prop_c
| Theory_c
| Type_c of string
| TypeAbs_c of int
| Ref_c  of string
| App_c  of prntVisSort * cnstr_c * cnstr_c
| Bind_c of binder_c * cnstr_c
| Tuple_c of (cnstr_c list) * cnstr_c
| Proj_c of projSort * cnstr_c
| Ctxt_c of ctxt_c * cnstr_c
| Cast_c of cnstr_c * cnstr_c       (* strong cast *)
| wCast_c of cnstr_c * cnstr        (* weak cast *)
| Case_c of cnstr_c * (ctxt_c * cnstr_c * cnstr_c) list  (* case *)
| Red_c of ctxt_c * ((cnstr_c*cnstr_c) list)
| Var_c  of int  (* metavars for use in refinements *)
| NewVar_c       (* make a new metavar *)
| Normal_c of cnstr_c
| Hnf_c of int * cnstr_c
| Dnf_c of cnstr_c
| RedTyp_c of instrs * cnstr_c
| TypeOf_c of cnstr_c
| Gen_c of cnstr_c * string
| Bot_c
withtype binder_c =
  bindSort * visSort * frzLocGlob * string list * string list * cnstr_c
and  ctxt_c = binder_c list;

val red_cache = ref (([]:binder_c list),([]:(cnstr_c*cnstr_c) list));

fun prt_concrete c =
  let val prb =
    fn Lda => "Lda" | Pi => "Pi" | Sig => "Sig"
     | Let => "Let" | Thry => "Thry"
  in  case c of
    Prop_c => "Prop"
  | Theory_c => "Theory"
  | Type_c(_) => "Type"
  | TypeAbs_c(n) =>  "(Type"^makestring n^")"
  | Ref_c(s)  => "(Ref "^s^")"
  | App_c(_,f,a)  => "("^prt_concrete f^" "^prt_concrete a^")"
  | Bind_c((bs,_,_,_,ns,c),d) => "("^prb bs^")"
  | Tuple_c(cs,c) => "(Tup "^concat_sep "," (map prt_concrete cs)^")"
  | Proj_c(Fst,c) => "("^prt_concrete c^".1)"
  | Proj_c(Snd,c) => "("^prt_concrete c^".2)"
  | Proj_c(Labl(l),c) => "("^prt_concrete c^"^"^l^")"
  | Ctxt_c(_) => "Ctxt"
  | Cast_c(c,d) => "(Cast "^prt_concrete c^prt_concrete d^")"
  | wCast_c(c,v) => "(Cast "^prt_concrete c^",_)"
  | Red_c(_) => "Red"
  | Var_c(n)  => "(Var"^makestring n^")"
  | NewVar_c => "NewVar"
  | Normal_c(_) => "Norm"
  | Hnf_c(_) => "Hnf"
  | Dnf_c(_) => "Dnf"
  | RedTyp_c(_) => "RedTyp"
  | TypeOf_c(_) => "TypeOf"
  | Gen_c(_) => "Gen"
  | Bot_c => "Bot"
  end


local
  fun consider br cxt = (Ref(br),coerceGe(ref_typ br))
in
  fun Consider nam cxt = consider (Namespace.search nam cxt) cxt
end

(* Make concrete from abstract *)
val unEval =
  let
    fun psh_nam n nams =
      if n="" orelse (Namespace.isNewName n andalso not (mem n nams))
	then (n,n::nams)
      else psh_nam (n^"'"^(makestring ((length nams)+1))) nams
    fun uerec nams =
      fn Prop            => Prop_c
       | Theory          => Theory_c
       | Type(n)         => (case n
			       of Uconst(m) => TypeAbs_c(m)
				| Uvar(Unnamed _,_) => Type_c ""
				| Uvar(Named s,_) => Type_c s )
       | Ref(br)         => Ref_c(ref_nam br)
       | Rel(n)          => Ref_c(nth nams n handle Nth _ => bug"uerec")
       | App((f,args),viss) => 
	   let fun app f (arg,vis) = App_c(vis,f,uerec nams arg)
	   in  foldl app (uerec nams f) (ListUtil.zip (args,viss))
	   end
       | LabVT(l,v,t) =>
	   (case l of
	      Name _ => bug"unEval:LabVT Name"
	    | WeakCast => wCast_c(uerec nams v,t)
	    | StrongCast => Cast_c(uerec nams v,uerec nams t)
	    | RedPr => bug"unEval:LabVT RedPr")
       | CnLst _ => bug"uerec:CnLst"
       | Case _ => bug"uerec:Case"
       | Bind((Thry,v),n,c,d) => bug"uerec:Thry"
       | Bind((b,v),n,c,d) =>
	   let val (n,nams') = psh_nam n nams
	   in  Bind_c((b,v,(UnFroz,Local),[],[n],uerec nams c),uerec nams' d)
	   end
       | Tuple(T,ls)     => Tuple_c(map (uerec nams) ls,uerec nams T)
       | Proj(p,c)       => Proj_c(p,uerec nams c)
       | RedTyp(p,c)     => RedTyp_c(p,uerec nams c)
       | Var(n,c)        => Cast_c(Var_c n,uerec nams c)
       | Bot             => bug"uerec:Bot"
  in
    uerec []
  end

fun fEval_ Cxt type_of_var mkVar V_c =
  let
    fun binder (b,v,frz_par_flg,_,nam,d) inner_op cxt sbst =
      let 
	val (VT,sbst) = Eval cxt sbst d
	val cxt = Namespace.extendCxt Bnd (b,v) frz_par_flg [] nam VT cxt
	val (VTr,sbst) = inner_op cxt sbst
	val (VT,_,_) = Namespace.dischCxt VTr cxt
      in  (VT,sbst)
      end
    and Ev_locs locs inner_op cxt sbst =
      case locs
	of (b,v,frz_par_flg,deps,n::ns,d)
	  => binder (b,v,frz_par_flg,deps,n,d)
	    (Ev_locs (b,v,frz_par_flg,deps,ns,d) inner_op)
	    cxt sbst
	| (_,_,_,_,[],_)    => inner_op cxt sbst 
    and EvLocs locs inner_op cxt sbst =
      case locs
	of bnd::bnds => Ev_locs bnd (EvLocs bnds inner_op) cxt sbst
	 | []        => inner_op cxt sbst

    and Eval cxt sbst c =
      let val (VT,sbst) = eval cxt sbst c
      in (sub_pr sbst VT,sbst) end
    and Cval c cxt sbst = Eval cxt sbst c

    and eval cxt sbst c =
      let
	val _ = if (!eval_debug) then message("** eval_deb: "^prt_concrete c)
		else ()
	fun Eval_arg cxt sbst =
	  fn NewVar_c => ((Bot,Bot),sbst)   (* just a marker for Apply *)
	   | x        => Eval cxt sbst x
      in case c of
	Prop_c => (Machine.ConsiderProp(),sbst)
      | Theory_c => (Machine.ConsiderTheory(),sbst)
      | Type_c s => (Machine.ConsiderType s,sbst)
      | TypeAbs_c(n) =>
	     if (n>=0) then (Machine.ConsiderTypen n,sbst)
	     else failwith((string_of_num n)^" not a valid Type level")
      | Ref_c(nam) => (Consider nam cxt,sbst)
      | Bind_c(bnd,r) => Ev_locs bnd (Cval r) cxt sbst
      | App_c(pv,fnn,arg) =>
	  let val (VTfun,sbst) = Eval cxt sbst fnn
	      val (VTarg,sbst) = Eval_arg cxt sbst arg
	  in  Machine.Apply sbst mkVar pv VTfun VTarg
	  end
      | Tuple_c(cs,t) =>
	  let val ((T,_),sbst) = if t = Bot_c then ((Bot,Bot),sbst)
				 else Eval cxt sbst t
	      fun ev c (vts,sbst) = let val (vt,sbst) = Eval cxt sbst c
				    in  (vt::vts,sbst)
				    end
	      val (vts,sbst) = foldr ev ([],sbst) cs
	  in  Machine.tuplize sbst T vts
	  end
      | Proj_c(p,c) =>
	  (case (Eval cxt sbst c,p)
	     of (((V,_),sbst),Labl l) => (TheoryProject(V,l),sbst)
	      | ((VT,sbst),_) => ((Machine.Projection p VT),sbst))
      | Case_c(v,branches) =>
	  (case Eval cxt sbst v of
	     ((V,T),sbst) => ((Case(V,EvCase T branches cxt),T),sbst))
      | RedTyp_c(i,c)  => (case Eval cxt sbst c of   (****  temporary  *****)
			     ((v,t),sbst) => ((RedTyp(i,v),UMnorm t),sbst))
      | Cast_c(c,t)    => typecheck cxt sbst c t
      | wCast_c(c,t)   => typchk cxt sbst c t
      | Ctxt_c(locs,c) => EvLocs locs (Cval c) cxt sbst
      | Red_c(red)     => EvRed red cxt
      | Var_c(n)       => ((Machine.ConsiderVar n (type_of_var n)),sbst)
      | NewVar_c       => failwith"new scheme vars not allowed here"
      | Bot_c          => bug"fEval_:Bot_c"
      | Normal_c(c)    => (case Eval cxt sbst c of
			     ((v,t),sbst) => ((UMnorm v,UMnorm t),sbst))
      | Hnf_c(n,c)     => (case Eval cxt sbst c of
			     ((v,t),sbst) => ((UMwhnf v,UMwhnf t),sbst))
      | Dnf_c(c)       => (case Eval cxt sbst c of
			     ((v,t),sbst) => ((UMdnf v,UMdnf t),sbst))
      | TypeOf_c(c)    => (case Eval cxt sbst c of
			     ((v,t),sbst) => ((t,type_of_constr t),sbst))
      | Gen_c(c,back)  => (case Eval cxt sbst c of
			     (vt,sbst) => (Namespace.lclGen vt back,sbst))
      end
	 
    and chk_unresolved (VT as (V,T)) =
      if (semi_pure V) andalso (semi_pure T)
	then VT
      else (prnt_vt_expand V T; failwith "unresolved metavars")
    and fEv V_c cxt sbst = let val (VT,sbst) = Eval cxt sbst V_c
			   in ((chk_unresolved VT),sbst) end
    and typecheck cxt sbst pr cnj =  (* concrete conjecture *)
      let val ((Vcnj,_),sbst) = fEv cnj cxt sbst
      in  typchk cxt sbst pr Vcnj
      end
    and typchk cxt sbst pr cnj =     (* abstract conjecture *)
      case pr
	of NewVar_c => ((mkVar cnj,cnj),sbst)
	 | _        =>
	     let
	       val ((V,T),sbst) = fEv pr cxt sbst
	       val _ = if not(!eval_debug) then ()
		       else (message"**ev_deb: typchk ";
			     hold_T:= T; legoprint T;
			     hold_cnj:= cnj; legoprint cnj)
	     in case par_unif sbst T cnj
		  of SOME(s) => ((V,cnj),s)
		   | NONE => (message"typechecking error.."; legoprint V;
			      message"has type.."; legoprint T;
			      message"which doesn't convert with..";
			      legoprint cnj;
			      failwith "term doesn't have purported type")
(*******************  time slice? 
	     in case par_tm (sub sbst T) (sub sbst cnj)
		  of true => ((V,cnj),sbst)
		   | false => (message"typechecking error.."; legoprint V;
			       message"has type.."; legoprint T;
			       message"which doesn't convert with..";
			       legoprint cnj;
			       failwith "term doesn't have purported type")
************************)
	     end
    and chkPr lcl cxt sbst (lhs,rhs) =
      let
	val lclCxt = first_n lcl cxt
	val ((vlhs,tlhs),_) = Eval cxt sbst lhs
	val ((vrhs,trhs),_) = Eval cxt sbst rhs
	val _ = if (UMtype_match tlhs trhs) then ()
		else (message"reduction LHS has type ";legoprint tlhs;
		      message"reduction RHS has type ";legoprint trhs;
		      failwith"LHS and RHS types don't convert")
	fun chkVarLR (b as (SOME _)) br = b
	  | chkVarLR NONE br =
	    if depends br vrhs andalso not (depends br vlhs)
	      then SOME(ref_nam br) else NONE
	val _ = case foldl chkVarLR NONE lclCxt
		  of NONE => ()
		   | SOME(s) =>
		       (message("reduction RHS mentions variable "^s);
			legoprint vrhs;
			message"reduction LHS does not ";legoprint vlhs;
			failwith"unbound variable in RHS")
      in LabVT(RedPr,vlhs,vrhs)
      end
    and EvRed (locs,pairs) cxt =
      let
	val _ = if !eval_debug then red_cache:= (locs,pairs) else ()
	fun er cxt sbst =    (** `CnLst' is a trick for discharge **)
	  ((CnLst(map (chkPr (length locs) cxt sbst) pairs),Bot),[])
      in
	EvLocs locs er cxt []
      end
    and EvCase T branches cxt =
      let
	fun mk1Branch (locs,lhs,rhs) =
	  let
	    fun chkBranch cxt sbst =
	      ((chkPr (length locs) cxt sbst (lhs,rhs),T),[])
	  in
	    EvLocs locs chkBranch cxt []
	  end
	fun mk2Branch ((v,t),_) =
	  if UMtype_match t T then v
	  else (message"Case body has type "; legoprint T;
		message"Case branch has type "; legoprint t;
		failwith"body and branch types don't convert")
	val branches = map (mk2Branch o mk1Branch) branches
      in CnLst(branches)
      end

  in
    fEv V_c Cxt []
  end;


fun parser_var_pack() =
      let val NUN = ref(0)
      in  fn c => (NUN:= !NUN-1; Var(!NUN,c))
      end;


fun no_metavars n = 
  (failwith ("found metavar "^
	     (string_of_num n) ^"; metavars not allowed here")):cnstr
fun no_new_vars _ = failwith"`?` not allowed in here";

fun fEvalCxt cxt V_c = fst (fEval_ cxt no_metavars (parser_var_pack()) V_c);

(***
NOTICE that the following two definitions need to be functional,
 because Namespace.getSpace has side effects
***)
fun fEval V_c = fEvalCxt (Namespace.getNamespace()) V_c
fun EvalRefine type_of_var = fEval_ (Namespace.getNamespace()) type_of_var

end;
