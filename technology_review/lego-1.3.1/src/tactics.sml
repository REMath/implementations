(* 
   tactics 
   $Log: tactics.sml,v $
   Revision 1.10  1997/11/24 11:01:59  tms
   merged immed-may-fail with main branch

   Revision 1.9  1997/08/25 11:00:22  tms
   Immed fails if no progress has been achieved

   Revision 1.8  1997/07/11 13:29:24  tms
   Qrepl will fail if the LHS does not occur in the goal

   Revision 1.7  1997/07/02 16:03:17  rap
   esUMopen.sml: better diagnostics for "sameTerm"
   tactics.sml: random changes: no change to functionality I hope!

   Revision 1.6  1997/05/28 10:35:11  tms
   Tactic Assumption prints out identification

   Revision 1.5  1997/05/08 13:42:56  tms
   added support for adding tactics

   Revision 1.4  1997/02/17 17:43:08  tms
   o reimplemented Assumption so that it aborts with
       an error message if unsuccessful

   o internal immed_tac function can now be configured to raise the
        exception Immed_tac if no progress has been achieved
*)

val repl_debug = ref false

functor FunTactics (structure Toplevel:TOPLEVEL
		    structure Namespace : NAMESPACE
		    structure Concrete:CONCRETE
		    sharing type Toplevel.cnstr_c=Concrete.cnstr_c
		    structure Synt:SYNT
		    structure Error:ERROR
		    	)
     : TACTICS  =
    struct
	local
	    open Concrete
	in
	    type cnstr_c=Concrete.cnstr_c

(* Only one UNDO per IMMED *)
exception Immed_tac;

fun immed_tac ex n = 
    let fun it_rec (B::l) = 
	if sameRef B (hd (Namespace.getContextBeforeProof()))
	    then if ex then raise Immed_tac else ()
	else if Toplevel.SolveTacn n 0 (Ref_c(ref_nam B))
		 then ()		(* successful exit *)
		   else it_rec l
          | it_rec []   = bug"immed_tac"
     in it_rec (Namespace.getNamespace()) end;


(** Immed [] is successful if at least one goal could be resolved. We
check on progress by comparing the number of open goals before and
after applying the Immed tactic. Alternatively, one could have flagged
a successful exit of immed_tac -tms **)
fun immed l =
    ( message"Immediate";
     if l = []
	 then let
		  val goals = fst o Namespace.goals
		  val visible_goals_before = goals ()
	      in
		  (do_list (immed_tac false o fst) (rev (visible_goals_before));
		   if ((length (goals())) = length (visible_goals_before))
		       then raise Error.error (Error.IMMED,NONE,[])
		   else ())
	      end
     else do_list (fn (n,s) => Toplevel.RefineTac_c n 0 (Ref_c s)
		   (!Toplevel.AutoTac)) l );

val Immed = Toplevel.smallAppTac immed;
    

(*** Convenient for proof by pointing ***)
fun Assumption n
    = ((message "Assumption..";Toplevel.smallAppTac (immed_tac true) n))
    handle Immed_tac => raise Error.error (Error.ASSUMPTION,SOME n,[])


fun andElim n v_c =
    ( Toplevel.RefineTac_c n 2 v_c
           (fn(l:substitution) => (Toplevel.IntrosTac (fst(hd l)) ["",""] true;()));
      message"and Elim" )
and andIntro n = (Toplevel.RefineTac_c n 4 (Ref_c "pair") Toplevel.nullTac; message"and Intro")
and orElim n v_c = (Toplevel.RefineTac_c n 2 v_c Toplevel.nullTac; message"or Elim")
and orIntroL n = (Toplevel.RefineTac_c n 3 (Ref_c "inl") Toplevel.nullTac; message"or Intro L")
and orIntroR n = (Toplevel.RefineTac_c n 3 (Ref_c "inr") Toplevel.nullTac; message"or Intro R")
and notElim n v_c = (Toplevel.RefineTac_c n 2 v_c Toplevel.nullTac; message"not Elim")
and notIntro n = (Toplevel.IntrosTac n [""] true; message"not Intro")
and exElim n v_c = (Toplevel.RefineTac_c n 2 v_c Toplevel.nullTac; message"Ex Elim")
and exIntro n P_c =
    (Toplevel.RefineTac_c n 2 (App_c(ShowNorm,Ref_c "ExIntro",P_c))
     Toplevel.nullTac;
    message"Exist Intro")
and allIntro n = (Toplevel.IntrosTac n [""] true; message"imp/All Intro")
and allElim n v_c =
    ((Toplevel.RefineTac_c n 1 v_c Toplevel.nullTac
      handle Failure"doesn't solve goal"
          => Toplevel.RefineTac_c n 1 (App_c(ShowNorm,Ref_c "cut",
                                   (App_c(ShowNorm,v_c,NewVar_c)))) Toplevel.nullTac);
    message"imp/All Elim");

fun AndElim n = Toplevel.AppTac (andElim n);
val AndIntro = Toplevel.AppTac andIntro;
fun OrElim n = Toplevel.AppTac (orElim n);
val OrIntroL = Toplevel.AppTac orIntroL;
val OrIntroR = Toplevel.AppTac orIntroR;
fun NotElim n = Toplevel.AppTac (notElim n);
val NotIntro = Toplevel.AppTac notIntro;
fun ExElim n = Toplevel.AppTac (exElim n);
fun ExIntro n = Toplevel.AppTac (exIntro n);
val AllIntro = Toplevel.AppTac allIntro;
fun AllElim n = Toplevel.AppTac (allElim n);



(* a replace-by-equality tactic *)
local
  val leibniz = {typeName= Ref_c "Q",
		 substitution= Bot_c,
		 symmetry = Ref_c "Q_sym"}
  val params = ref leibniz
in
  fun Config_Qrepl (tn,subst,sym) =
    (params:= (if tn = "" then leibniz
	       else {typeName= Ref_c tn,
		     substitution= Ref_c subst,
		     symmetry= Ref_c sym});
     Namespace.addConfig ("Qrepl",tn,subst,sym) ;
     message"'Qrepl' configured")
  fun replace n v_c =
    let
 (* the conditional equation is the type of v_c *)
	val ((V,T),_) = Concrete.EvalRefine Synt.type_of_Var
	    (Concrete.parser_var_pack()) v_c
      fun replErr msg = (message"Replace error:"; prnt_vt V T; failwith msg)
 (* split into conditions and equation.
  * Note the equation may not depend on the conditions,
  * but the conditions may depend on other conditions. *)
      val (nbr_conditions,equation) =
	let
	  fun conds (n,ceq) =
	    case ceq   (** this doesn't work right; need (whnf ceq), but
                        *  then reduces too far in case of leibniz *)
	      of Bind((Pi,_),_,S,U) => conds(n+1,U)
	      | eqn as (App _) =>
		  ((n, lift (~n) eqn)
		   handle Lift => replErr "equation depends on conditions")
	      | _ => replErr "not a conditional equation"
	in conds (0,T)
	end
      val _ = if (!repl_debug)
		then message("*rpl-nbr_conds* "^makestring nbr_conditions)
	      else ()
 (* make a concrete template for the equation *)
      val tpl_c = App_c(ShowNorm,
			App_c(ShowNorm,
			      App_c(ShowForce,#typeName(!params),NewVar_c),
			      NewVar_c),
			NewVar_c)
 (* compute the abstract template and find out
  * which variables are in which positions *)
      val (mkVar,_,close) = Namespace.manageVars()
      val ((tpl as (App((_,[Var(TTn,_),Var(lhsn,_),Var(rhsn,_)]),_)),_),_) =
	Concrete.EvalRefine (fn n => bug("replaceER "^makestring n)) mkVar tpl_c
	handle Match => bug"replace;tpl"
      val _ = if (!repl_debug) then (prs"*rplt* ";
				     pri TTn; prs" ";
				     pri lhsn; prs" ";
				     pri rhsn; prs"\n")
	      else ()
      val _ = close()
 (* unify equation with abstract template to verify
  * it is an equation, and get the types of the lhs and rhs *)
      val bngs = case type_match_unif [] equation tpl
		   of SOME(bngs) => bngs
		    | NONE => replErr"not the expected equality"
      val _ = if (!repl_debug)
		then do_list (fn (n,c) => (prs"*rpl* ";
					   pri n; prs" "; legoprint c))
		             bngs
	      else ()
      (* next binding is written to be independent of order
       * unification solves variables *)
      val [TT,lhs,rhs] = map (fn v => assoc v bngs) [TTn,lhsn,rhsn]
	handle _ => bug"computing lhs and rhs of equation"
      val (nn,goal) = Synt.goaln n
      fun make_abstrn k goal =
	if UMtype_match lhs goal then Rel k  (*** par_tm ? ***)
	else case goal
	       of App b => umkApp (make_abstrn k) b
		| Bind b => umkBind make_abstrn k b
		| Tuple b => umkTuple (make_abstrn k) b
		| CnLst b => umkCnLst (make_abstrn k) b
		| Proj c => umkProj (make_abstrn k) c
		| RedTyp c => umkRedTyp (make_abstrn k) c
		| LabVT b => umkLabVT (make_abstrn k) b
		| x => x
      val pre_abstrn = make_abstrn 1 goal
      val abstrn = Bind((Lda,Vis),"z",TT,pre_abstrn)
      val _ = if (!repl_debug) then legoprint abstrn else ()
      val _ = if (var_occur pre_abstrn) then ()   (* check lhs occurs in goal *)
	      else (raise Error.error (Error.REPLLHS,SOME nn,[lhs]))
      fun refine n v_c = (Toplevel.RefineTac_c n 1 v_c Toplevel.nullTac;
			  print_qrepl V lhs rhs)
      fun substitution_operator u =
	let val subst = #substitution(!params)
	in  if subst = Bot_c then u else App_c(ShowNorm,subst,u)
	end
 (* make conditional equation into an equation by applying it to
  * the right number of unknowns *)
      val equation =
	let fun mk_equation 0 = v_c
	      | mk_equation n =
		if n>0
		  then App_c(ShowForce,mk_equation (n-1),NewVar_c)
		else bug"mk_equation"
	in  mk_equation nbr_conditions
	end
    in
      Toplevel.smallAppTac (refine n)
         (App_c(ShowNorm,
		substitution_operator
		(App_c(ShowNorm,#symmetry (!params),equation)),
		unEval abstrn))
    end
end

(** Support for domain-specific tacticals added by users **)

(* database of user-defined tacticals *)
val UTACDB = ref [] : (string*(unit->unit)) list ref

fun add_tactic id f = UTACDB:=(id,f)::(!UTACDB)


fun member id (x,_) = x=id

fun lookup_tactic id = case ListUtil.findOne (member id) (!UTACDB) of
                         (SOME (_,f)) => SOME f
		       | NONE => NONE

fun ExecUserTac id = case lookup_tactic id of
                       (SOME f) => (message ("Executing UserTac "^id); f())
		     | NONE => message ("UserTac "^id^" not found!")
    
fun remove_tactic id = UTACDB := filter_neg (member id) (!UTACDB)

end (* local *)
end (* struct *)
