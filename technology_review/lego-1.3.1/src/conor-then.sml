signature CONORTHEN =
sig
  val InitConorThen : unit -> unit
  val RunLazyTactics : unit -> unit
  val Then : (unit -> unit) -> (unit -> unit) -> (unit -> unit)
end

structure PromptKnotTypes =
struct
  type knot = string
  type entry = unit -> unit
end

structure UndoKnotTypes =
struct
  type knot = string
  type entry = unit -> unit
end

functor FunConorThen(structure Namespace:NAMESPACE
		     structure PromptKnots:CONORKNOTS
		     structure UndoKnots:CONORKNOTS
		     sharing PromptKnots.KT = PromptKnotTypes
		     sharing UndoKnots.KT = UndoKnotTypes) : CONORTHEN =
struct
  local
    structure GoalKnots = FunConorKnots(type knot = int
					type entry = unit -> unit)

    fun subgoal_list () = map (#1) (#1 (Namespace.goals()))

    fun goal_number () = (#1 (#1 (Namespace.subgoals())))

    fun member _ []     = false
      | member i (h::t) = (i=h) orelse member i t

    fun diff []     _ = []
      | diff (h::t) s = if (member h s) then diff t s
			else h::(diff t s)

    fun add_if_missing i l = if (member i l) then l else i::l

    fun handle_knot () =
	if Namespace.activeProofState()
	    then let
		     val g = goal_number ()
		     val tac = GoalKnots.seek_one_knot (fn k => k=g)
		     val _ = GoalKnots.remove_all_knots (fn k => k=g)
		 in
                     (message "executing delayed Then tactic...");
		     (tac ());
		     (handle_knot ())
		 end
	     handle GoalKnots.no_such_knot => ()
	else GoalKnots.remove_all_knots (fn _ => true)
  in
    val RunLazyTactics = handle_knot
    fun InitConorThen () =
	( (PromptKnots.tie_knots RunLazyTactics ["ConorThen"]);
	  (UndoKnots.tie_knots
	   (fn _ => GoalKnots.remove_all_knots (fn _ => true))
	   ["Init"]);
	  (UndoKnots.tie_knots
	   (fn _ => GoalKnots.push_knots ())
	   ["Mark"]);
	  (UndoKnots.tie_knots
	   (fn _ => GoalKnots.undo_knots 1)
	   ["Undo"]);
	  (UndoKnots.tie_knots
	   (fn _ => GoalKnots.discard_knots 1)
	   ["Discard"]) )
    fun Then tac1 tac2 _ =
	let
            val oldNUN = Namespace.getNUN()
	    val old_subgoals = subgoal_list ()
	    val old_subgoal = hd old_subgoals
	    val _ = tac1 ()
	in
	    if Namespace.activeProofState() then
		let (* we may need to do the second tac *)
                    val next_subgoals = subgoal_list ()
		    val next_subgoal = hd next_subgoals
		    val then_list =
			if (next_subgoal>=oldNUN)
                        then diff next_subgoals old_subgoals
			else if (next_subgoal=old_subgoal) then [old_subgoal]
			     else []
		in
		    ((*(map (fn i:int => ((print i);print " "))
		      then_list);
		     (message " being added");*)
		     (map (chain_new_tac tac2) then_list);())
		end
	    else () (* goal already proven *)
	end
    and chain_new_tac t2 g =
	let
	    val t1 = GoalKnots.seek_one_knot (fn k => k=g)
	    val _ = GoalKnots.remove_all_knots (fn k => k=g)
	in
	    GoalKnots.tie_knots (Namespace.no_history (Then t1 t2)) [g]
	end
        handle GoalKnots.no_such_knot =>
	    GoalKnots.tie_knots (Namespace.no_history t2) [g]

  end
end
