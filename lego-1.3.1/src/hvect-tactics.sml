(* 
   $Log: hvect-tactics.sml,v $
   Revision 1.4  1997/11/24 11:01:03  tms
   merged immed-may-fail with main branch

   Revision 1.3.2.3  1997/10/13 16:47:03  djs
   More problems with the above.

   Revision 1.3.2.2  1997/10/13 16:21:24  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
 
   Revision 1.3.2.1  1997/10/10 17:02:16  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.3  1997/05/28 10:33:49  tms
   Tactic supports Undo
  
   Revision 1.2  1997/05/15 16:28:40  tms
   added support for theorem hvect_nth_update
*)



signature HVECTTACTREQ  =
    sig
    type term
        (* replace c uses the theorem c to rewrite the current goal *)
	val replace : term -> unit

        val getCurrentGoal : unit -> term
    end

functor FunHVectTact (structure Lego:HVECTTACTREQ
		      structure Concrete:CONCRETE
		      sharing type Lego.term=Concrete.cnstr_c) : HVECTTACT =
    struct
	open Concrete
	    
	exception nooccur

	fun ElimUpdate () =
	    let
		fun occurrence (App_c(ShowNorm,
				      App_c
				      (NoShow,
				       App_c
				       (NoShow,Ref_c f,_),_),
				      App_c
				      (ShowNorm,
				       App_c
				       (ShowNorm,
					App_c
					(ShowNorm,
					 App_c
					 (NoShow,
					  App_c
					  (NoShow,Ref_c "hvect_update",_),_),
					 v),x),t))) =

		    let
			val theorem = case f of
			    ("hvect_tail") => "tail_update"
			  | ("hvect_head") => "head_update"
			  | _ => raise nooccur
		    in
			App_c (ShowNorm,
			       App_c (ShowNorm,App_c (ShowNorm,Ref_c theorem,v),
				      x),t)
		    end
		  | occurrence (App_c (ShowNorm,
				       App_c(ShowNorm,
					     App_c
					     (NoShow,
					      App_c
					      (NoShow,Ref_c "hvect_nth",_),_),
					     App_c
					     (ShowNorm,
					      App_c
					      (ShowNorm,
					       App_c
					       (ShowNorm,
						App_c
						(NoShow,
						 App_c
						 (NoShow,
						  Ref_c "hvect_update",_),_),
						v),x),t)),y)) =
		    App_c (ShowNorm,
			   App_c (ShowNorm,
				  App_c (ShowNorm,
					 App_c (ShowNorm,
						Ref_c "hvect_nth_update",v),
					 x),t),y)

		  | occurrence (App_c (_,f,args)) =
		     ((occurrence f) handle _ => (occurrence args))
		  | occurrence (Bind_c ((_,_,_,_,_,t),term)) =
		    ((occurrence t) handle nooccur => (occurrence term))
		  | occurrence _ = (raise nooccur)
	    in
		Namespace.tactic_wrapper
		(fn () =>
		 (Lego.replace (occurrence (Lego.getCurrentGoal()));
		  Top.Expand [] ["hvect_nth_update_rhs",
				 "fin_elim'","fin_elim'_lemma"];
		  ElimUpdate())
		 handle nooccur => ())	()
	    end
    end					(* FunHVectTact *)

functor funHVectTactReg (structure Concrete:CONCRETE
			 structure Namespace:NAMESPACE
			 structure Tactics:TACTICS
			 sharing type Concrete.cnstr_c=Tactics.cnstr_c)
    : HVECTTACTREQ  =
    struct
	type term=Concrete.cnstr_c
	val replace = Tactics.replace (~9999)
	fun getCurrentGoal () = case Namespace.getCurrentGoals() of
	    ((Namespace.Unknown((exvar,goal)::_)::_)) => Concrete.unEval goal
	  | _ => bug "getCurrentGoal: no unknown goals found"
    end
	    
