(* 
 * $Log: lib_nat_plus_thms.sml,v $
 * Revision 1.3  1997/11/24 11:01:23  tms
 * merged immed-may-fail with main branch
 *
 * Revision 1.2.2.2  1997/11/18 16:41:11  tms
 * more of the same
 *
 * Revision 1.2.2.1  1997/10/13 16:21:26  djs
 * Because CVS charmingly breaks code by inserting the wrong comment
 * markers.
 *
 * Revision 1.2  1997/05/28 10:34:03  tms
 * Tactic supports Undo
 *)

signature LIBNATPLUSTHMS =
    sig
	(* replaces all occurrences of (a+b)+c in the current goal
           by a+(b+c) *)
	val RedModPlusAssoc : unit -> unit
    end;

signature LIBNATPLUSTHMSREQ  =
    sig
    type term
        (* replace c uses the theorem c to rewrite the current goal *)
	val replace : term -> unit

        val getCurrentGoal : unit -> term
    end

functor FunLibNatPlusThmsTact (structure Lego:LIBNATPLUSTHMSREQ
			       structure Concrete:CONCRETE
			       sharing type Lego.term=Concrete.cnstr_c)
    : LIBNATPLUSTHMS =
    struct
	open Concrete

	exception nooccur

	fun RedModPlusAssoc () =
	    let
		fun occurrence (App_c(ShowNorm,
				      App_c
				      (ShowNorm,Ref_c "plus",
				       App_c
				       (ShowNorm,
					App_c (ShowNorm,Ref_c "plus",a),b)),c))
		    = App_c (ShowNorm,
			     App_c (ShowNorm,App_c (ShowNorm,
						    Ref_c "plus_assoc",a),b),c)
		  | occurrence (App_c (_,f,args)) =
		     ((occurrence f) handle nooccur => (occurrence args))
		  | occurrence _ = raise nooccur
	    in
		Namespace.tactic_wrapper
		(fn () =>
		 (Lego.replace (occurrence (Lego.getCurrentGoal()));
		  RedModPlusAssoc())
		 handle nooccurr => ()) ()
	    end
    end					(* FunLibNatPlusThmsTact *)

functor funLibNatPlusThmsTactReg (structure Concrete:CONCRETE
				  structure Namespace:NAMESPACE
				  structure Tactics:TACTICS
				  sharing type Concrete.cnstr_c=Tactics.cnstr_c)
    : LIBNATPLUSTHMSREQ  =
    struct
	type term=Concrete.cnstr_c
	val replace = Tactics.replace (~9999)
	fun getCurrentGoal () = case Namespace.getCurrentGoals() of
	    ((Namespace.Unknown((exvar,goal)::_)::_)) => Concrete.unEval goal
	  | _ => bug "getCurrentGoal: no unknown goals found"
    end
	    
structure LibNatPlusThmsTact =
    FunLibNatPlusThmsTact
    (structure Lego=funLibNatPlusThmsTactReg (structure Concrete=Concrete
				     structure Namespace=Namespace
				     structure Tactics=Tactics)
     structure Concrete=Concrete);

Tactics.add_tactic "plus_assoc" LibNatPlusThmsTact.RedModPlusAssoc
