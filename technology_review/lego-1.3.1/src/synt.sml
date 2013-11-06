(* Time-stamp: <30 Dec 95 tms /home/lego/SOURCES/NEW/synt.sml> *)

val resolve_debug = ref false;
val Resolve_debug = ref false;

functor FunSynt (structure Concrete:CONCRETE
		 structure Namespace:NAMESPACE
		     ) (* : SYNT *) =
    struct
	type cnstr_c=Concrete.cnstr_c
type question=Namespace.question

fun type_of_Var n = 
    let fun tov_rec (Namespace.Unknown(l)::q) = ((assoc n l) handle _ =>  (tov_rec q))
          | tov_rec (_::q) = tov_rec q
          | tov_rec [] = failwith("Undefined metavar: ?"^(string_of_num n))
     in tov_rec (Namespace.getCurrentGoals()) end;

fun type_of_Var_restricted m n =
    if m = n then failwith("use of ?"^(string_of_num m)^" out of scope")
             else type_of_Var n;

fun goaln n = if n=(~9999) then #1 (Namespace.subgoals())
              else (n,assoc n (fst (Namespace.goals()))
                    handle _ =>  
                      failwith("goal "^(string_of_num n)^" not found"))

fun goal_rel (reverse,n) =
    let val (h,t,_) = Namespace.subgoals()
        val l = (h::t)
    in nth (if reverse then rev l else l) (n+1)
	handle Nth _ => failwith("goal "^(if reverse then "-" else "+")^
				 (string_of_num n)^" not found")
    end
	    


(* The principal function: try to solve the current goal against the
 * (type of) v_c.  The match is first tried against the entire TYP.
 * If that fails, TYP is progressively unwound (by explicit). *)
local
  exception Explicit of cnstr * cnstr;
  (* unroll a construction to make a refinement rule of it.
   * maintain invariant a achieves c with Namespace.subgoals newVars
   * (see resolve).
   *)
  fun explicit mkVar (a,c) =
    case whnf c
      of Bind((Pi,v),_,d,e) => let val V = mkVar d
			       in  (MkApp((a,[V]),[prVis v]),subst1 V e)
			       end
       | _ => raise Explicit(a,c);
  fun resolve_abstract explicit VT p c =
    let
      fun resolve_rec (a1,c1) =
	let
	  val _ = if (!resolve_debug) then (prs"*res1* "; prnt_vt a1 c1)
		  else ()
	in case par_unif [] c1 c of
	  SOME(s) => compose sub [(p,sub s a1)] s
	| NONE => resolve_rec (explicit (a1,c1))
	end
    in
      resolve_rec VT handle Explicit(_) => failwith"doesn't solve goal"
    end
  fun subPrfCxt s (nsp as (b::l)) =
        if sameRef b (hd (Namespace.getContextBeforeProof())) then nsp
       else ref_updat_vt b (pair_apply (sub s) (ref_vt b))::(subPrfCxt s l)
    | subPrfCxt s [] = bug"subPrfCxt"
in
  fun resolve_c n m v_c =      (* when v_c is a concrete term *)
    let val (mkVar,eraseNew,close) = Namespace.manageVars()
      val (l,q) = Namespace.goals()
      val (n,goal) = goaln n
      val ((VT as (V,T)),sbst) =
	Concrete.EvalRefine (type_of_Var_restricted n) mkVar v_c
      val _ = if (!resolve_debug) then (prs"*resc1* "; prnt_vt V T)
	      else()
      val (VT as (V,T)) = 
	(eraseNew sbst;
	 (Repeat m (explicit mkVar) VT
	  handle Explicit(_) => failwith"too much cut"))
      val _ = if (!resolve_debug) then (prs"*resc2* "; prnt_vt V T)
	      else()
      val s = resolve_abstract (explicit mkVar) VT n goal
      val new = eraseNew s
      val prftrm = sub s (Namespace.getProofTerm())
      val _ = if (!Resolve_debug) then print_expand prftrm else ()
    in  (subPrfCxt s (Namespace.getNamespace()),
	 new,
	 prftrm,
	 Namespace.Unknown(Namespace.erase_replace s n new l)::(Namespace.eraseq s q),
	 close,
	 V)
    end
  fun resolve_a n m V =      (* when V is an abstract term *)
    let val (mkVar,eraseNew,close) = Namespace.manageVars()
      val (l,q) = Namespace.goals()
      val (n,goal) = goaln n
      val T = type_of_constr V
      val _ = if (!resolve_debug) then (prs"*resa1* "; prnt_vt V T)
	      else()
      val (VT as (V,T)) = (Repeat m (explicit mkVar) (V,T)
			   handle Explicit(_) => failwith"too much cut")
      val _ = if (!resolve_debug) then (prs"*resa2* "; prnt_vt V T)
	      else()
      val s = resolve_abstract (explicit mkVar) VT n goal
      val new = eraseNew s
    in  (subPrfCxt s (Namespace.getNamespace()),
	 new,
	 sub s (Namespace.getProofTerm()),
	 Namespace.Unknown(Namespace.erase_replace s n new l)::(Namespace.eraseq s q),
	 close,
	 V)
    end
end
end;
