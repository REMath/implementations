(*
   $Log: pbp_lib_logic.sml,v $
   Revision 1.4  1997/11/24 11:01:51  tms
   merged immed-may-fail with main branch

   Revision 1.2.2.4  1997/10/13 16:47:18  djs
   More problems with the above.

   Revision 1.2.2.3  1997/10/13 16:21:38  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.2.2.2  1997/10/10 17:02:46  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.2.2.1  1997/08/27 13:11:58  tms
   fixed bug in function pbp_or
  
   Revision 1.2  1997/07/11 13:29:13  tms
   Qrepl will fail if the LHS does not occur in the goal
*)

(* This is an example of a function implementing one of the four rules of
	     proof-by-pointing rules for the and construct 

fun pbp_andr2 NONE (LegoFormat.PrApp (LegoFormat.PrRef "and",[_,(B,_)]))
	     (2::2::path_tail) continuation
	     = SOME (["Refine pair", "Next +1"] @
	     (continuation NONE B path_tail))
	   | pbp_andr2 _ _ _ _ = NONE

	     The following function deals with all four cases. *)

	    fun pbp_and
		(hyp_name: string option)
		(pr_formula:LegoFormat.prCnstr)
		(path: int list)
		(continuation_function: string option 
		 -> LegoFormat.prCnstr -> int list -> string list) =
		(* first make sure you are on the right formula pattern,
		 while you are there, you can also compute the sub-formula that
		     will be treated in the recursive call *)
		case pr_formula of
		    LegoFormat.PrApp(LegoFormat.PrRef "and", [(a,_),(b,_)]) =>
			let val continuation_formula =
			    (case path of (2::1::path_tail) => a
			  | (2::2::path_tail) => b
			  | _ => pr_formula (* this value is irrelevant anyway:
					     there will be no recursive call *))
			in
			    (* then you can retrieve the path that will also be used in the
			     recursive call *)
			    case path of  (_::_::path_tail) =>
				(case hyp_name of
				     SOME hyp_name =>
					 (* if you are in an hypothesis, you are going to
					  break down this hypothesis in two sub-components.
					  you need names for these *)
					 (let val new_name1 = PbpInput.mkNameLoc "H"
					      val new_name2 = PbpInput.mkNameLoc "H"
					      val new_hypothesis =
						  (case path of (2::1::path_tail) => new_name1
						| (2::2::path_tail) => new_name2
						| _ => bug "unexpected path in a conjunction")
					      val cont = continuation_function
						  (SOME new_hypothesis)
						  continuation_formula path_tail
					  in
					      SOME(["Refine " ^ hyp_name,
						    "Intros " ^ new_name1 ^ " " ^ new_name2]
						   @ cont)
					  end)
				   | NONE => 
					 (* if you are in the conclusion, it is much
					  simpler: there is no problem with names and you
					  will proceed directly on the relevant goal
					  (chosen by inserting a "Next +1" when necessary) *)
					 let
					     val cont = continuation_function NONE
						 continuation_formula path_tail
					 in
					     SOME("Refine pair"::
						  ( (case path of (2::1::path_tail) => []
						| (2::2::path_tail) => ["Next +1"]
						| _ => bug "unexpected path in a conjunction") @
							 cont))
					 end)
			  | _ => SOME([]) (* the path is too short, no action is taken *)
			end
		  | _ => NONE


fun pbp_or
    (hyp_name: string option)
    (pr_formula:LegoFormat.prCnstr)
    (path: int list)
    (continuation_function: string option 
     -> LegoFormat.prCnstr -> int list -> string list) =
    case pr_formula of
	LegoFormat.PrApp(LegoFormat.PrRef "or", [(a,_),(b,_)]) =>
	    let val continuation_formula =
		(case path of (2::1::path_tail) => a
	      | (2::2::path_tail) => b
	      | _ => pr_formula (* this value is irrelevant anyway:
				 there will be no recursive call *))
	    in
		(* then you can retrieve the path that will also be used in the
		 recursive call *)
		(case path of
		     (_::_::path_tail) =>
			 (case hyp_name of
			      SOME hyp_name =>
				  (* if you are in an hypothesis, you are going to break down this
				   hypothesis in one sub-component.  you need a name for it *)
				  (let val new_name1 = PbpInput.mkNameLoc "H"
				       val go_to_new_goal =
					   (case path of (2::1::path_tail) => " "
					 | (2::2::path_tail) => "+1"
					 | _ => bug "unexpected path in a disjunction")
				       val cont = continuation_function
					   (SOME new_name1)
					   continuation_formula path_tail
				   in
				       SOME(("Refine or_elim " ^ hyp_name ^ " Then Intros " ^ go_to_new_goal ^ " " ^ new_name1):: cont)
				   end)
			    | NONE => 
				       (* if you are in the conclusion, it is much simpler: there
					is no problem with names and you will proceed directly
					on the relevant goal  *)
				       let val cont = continuation_function NONE
					   continuation_formula path_tail
					   val this_command = (case path of (2::1::path_tail) => "Refine inl"
					 | (2::2::path_tail) => "Refine inr"
					 | _ => bug "unexpected path in a disjunct")
				       in
					   SOME(this_command::cont)
				       end)
		   | _ => SOME([])) (* the path is too short, no action is taken *)
	    end
      | _ => NONE;
	    

fun pbp_Ex  (hyp_name:string option) 
     (Pattern:LegoFormat.prCnstr) (path:int list) 
     (continuation: string option -> LegoFormat.prCnstr -> int list -> string list) =
     case Pattern of
	 LegoFormat.PrApp(LegoFormat.PrRef "Ex", [(LegoFormat.PrBind ([a],_,T,p),_)]) =>
	     (case hyp_name of
		  NONE =>
		      (case path of
			   2::1::3::path_tail =>	(* pointing at p *)
			       SOME (["Refine ExIn", "Next +1"] @
				     (continuation NONE p path_tail))

			 | 2::1::_::path_tail => SOME (["Refine ExIn"] @ (continuation NONE T path_tail))
			 | _ => NONE)
		| SOME hyp =>
		      let
			  val format_commands =
			      ListFormat.formatList
			        {init="",sep=" ",final="",fmt=fn a=>a}
			  val witness = PbpInput.mkNameLoc a
			  val assumpt = PbpInput.mkNameLoc "H"
			  val command = ["Refine ExElim " ^ hyp, format_commands ["Intros",witness,assumpt]]
		      in
			  case path of
			      2::1::3::path_tail => SOME (command @ (continuation (SOME assumpt) p path_tail))
			    | 2::1::_::path_tail => SOME (command @ (continuation (SOME witness) T path_tail))
			    | _ => NONE	(* for effeciency considerations, what might want to choose SOME [] instead *)
		      end)
       | _ => NONE;
			      

Pbp.add_pbp_rule "pbp_and" pbp_and;
Pbp.add_pbp_rule "pbp_or"  pbp_or;
Pbp.add_pbp_rule "pbp_Ex"  pbp_Ex;
