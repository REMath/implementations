(** pbp.sml   Proof by pointing
    Author: Yves Bertot <Yves.Bertot@sophia.inria.fr>
    Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

    $Log: pbp.sml,v $
    Revision 1.17  1997/11/24 11:01:45  tms
    merged immed-may-fail with main branch

    Revision 1.16.2.1  1997/11/06 15:54:14  djs
    Added a Let rules for PBP, and rearranged the rule order so that the
    empty-path rule is tried first, and new rules are always appended.

    Revision 1.16  1997/07/11 13:28:04  tms
    Qrepl will fail if the LHS does not occur in the goal

    Revision 1.15  1997/06/19 18:29:14  djs
    Some changes for script management

    Revision 1.14  1997/03/06 16:03:18  tms
    rules corresponding to lib_logic are now in pbp_lib_eq_basics.sml

    Revision 1.13  1997/03/06 09:55:26  tms
    o implementation of pbptop now records if selected goal is not current
    o introduced signature PBPINPUT

    Revision 1.12  1997/02/25 11:37:52  tms
    *** empty log message ***

    Revision 1.11  1997/02/25 11:33:49  tms
    I have replaced the function

      new_name : string list -> string -> string

    by a name generator

      generate_name : string -> string

    The first argument of new_name is really a cache. This information is
    now kept in

      val pbp_namespace: string list ref = ref []

    It is initialised in pbptop_default and pbphyptop_default.

    The new name generator simplifies writing implementations for new Pbp
    rules, see the diff file to the previous version of pbp.sml.

    Revision 1.10  1997/02/17 17:40:59  tms
    compensated for new semantics of the command Assumption.

    Previous changes:
     3 Dec 1996 Thomas Schreiber <tms@dcs.ed.ac.uk>
                o reimplemented Pi rule
                o better documentation

    16 Nov 1996 Thomas Schreiber <tms@dcs.ed.ac.uk>
                extended the algorithm when no rule matches

    15 Nov 1996 Thomas Schreiber <tms@dcs.ed.ac.uk>
                added rule for existential quantification in the goal

    Documentation:

    The module shar_pretty is responsible for the following annotations:

      o Application f a1 ... an
          Internal Represenation: PrApp (PrRef "f", [("a1",_), ..., ("an",_)])
          Annotations: 1   |-> f
                       2   |-> a1 ... an
                       2 i |-> ai
		       
      o Pi Abstraction {x1,...xn:A}B
	  Internal Represenation: PrBind ([x1,...,xn], (Pi,Vis), A, B) 
	  Annotations: 1   |-> x1,...,xn                
	               1 i |-> xi        if n>1                         
                       2   |-> A                               
                       3   |-> B 

      o Implication A->B
          Internal Represenation: PrBind ([], (Pi,Vis), A, B) 
          Annotations: just like application with (op->) A B i.e.,
                       1   |-> ->
                       2   |-> A B
		       2 1 |-> A
		       2 2 |->   B
**)


signature PBP =
  sig
      val pbptop : int -> int list -> unit;
      val set_pbptop : (int -> int list -> unit) -> unit;
      val pbphyptop : string -> int list -> unit;
      val set_pbphyptop : (string -> int list -> unit) -> unit;
      val pbp_initialize : unit -> unit;
      val remove_pbp_rule : string -> unit;
      val add_pbp_rule : string -> 
           (string option -> LegoFormat.prCnstr -> 
            int list ->
            (string option -> LegoFormat.prCnstr ->
             int list -> string list) -> string list option) -> unit;
  end;

signature PBPINPUT =
    sig
	val mkNameLoc      : string -> string
	val initNameLoc    : unit -> unit
	val getCurrentGoal : unit -> int*LegoFormat.prCnstr
	val getAssumption  : string -> LegoFormat.prCnstr
    end

functor FunPbp (structure PbpInput:PBPINPUT)  : PBP  =
    struct
	local
	    open LegoFormat
	in
            fun output_string_list l = 
                message (fold (fn (a,b)  => a^"; "^b) l "");

	    val format_commands = ListFormat.formatList {init="",sep=" ",final="",fmt=fn a=>a}

	    (**************************************************)
	    (***                                            ***)
	    (*** Dependent Function Spaces                  ***)
	    (***                                            ***)
	    (*** Notice that the tactic allE is not very    ***)
	    (*** well documented in the user manual, here   ***)
	    (*** is a more faithful description:            ***)
	    (***                                            ***)
	    (*** H:{x:A}B,GAMMA |- ?i:C, DELTA              ***)
	    (***   allE H                                   ***)
	    (*** H:{x:A}B,GAMMA |- ?j:A,?k:B[?j/x]->C,DELTA ***)
	    (**************************************************)
	    fun pbp_forall
		(hyp_name: string option)
		(pr_formula:prCnstr)
		(path: int list)
		(continuation: string option 
		 -> prCnstr -> int list -> string list) =
		case pr_formula of
		    PrBind(a::id_list, (Pi,Vis), A, B) =>
			(case path of
			     [1] => pbp_forall hyp_name pr_formula [1,length(a::id_list)] continuation
			   | 2::path_tail =>
				 let
				     val path = 1::length(a::id_list)::path_tail
				 in
				     pbp_forall hyp_name pr_formula path continuation
				 end
			   | _ => 
				 (case hyp_name of
				      SOME hyp_name =>
					  (case path of
					       1::1::path_tail =>
						   SOME (["allE " ^ hyp_name] @ (continuation NONE A path_tail))
					     | _ =>
						   let
						       val new_name1 = PbpInput.mkNameLoc "H"
						       val command = ["allE " ^ hyp_name, "intros +1 " ^ new_name1]

						       (** Notice that we ignore the substitution B[?j/x] **)
						       val formula =
							   case id_list of
							       [] => B
							     | _ => PrBind (id_list, (Pi,Vis), A, B)

						       val path =
							   case path of
							       1::i::path_tail => 1::(i-1)::path_tail
							     | 3::path_tail => (case id_list of [] => path_tail | _ => path)
							     | _ => bug "Unexpected annotation in dependent function space" 

						       val hyp = SOME new_name1

						       val continuation =
							   (* "continuation (SOME new_name1) formula path" works
							    uniformly, but for efficiency reasons, we employ pbp_forall rather
							    than the continuation whenever possible. *)
							   case id_list of
							       [] => continuation hyp formula path
							     | _ => (case (pbp_forall  hyp formula path continuation) of
									 SOME s => s
								       | _ => bug "pbp_forall")
						      
						   in
						       SOME (command @ continuation)
						   end)
				  
				    | NONE =>
					  (let
					       val used_names = ref []
					       fun command i = (do_list (fn x =>
									 used_names := (PbpInput.mkNameLoc x)::(!used_names))
								(rev (first_n i (a::id_list)));
								format_commands ("Intros"::(!used_names)))
					   in
					       case path of
						   1::i::path_tail =>
						       let
							   val command = command i (* generates new used names *)
							   val hyp = SOME (hd (!used_names))
							   val continuation = continuation hyp A path_tail
						       in
							   SOME (command :: continuation)
						       end
						 | 3::path_tail =>
						       let
							   val command = command (length (a::id_list))
							   val continuation = continuation NONE B path_tail
						       in
							   SOME (command :: continuation)
						       end
						 | _ => bug "Unexpected annotation in dependent function space"
					   end)))
		  | _  => NONE


fun pbp_let
    (hyp_name: string option)
    (pr_formula:prCnstr)
    (path: int list)
    (continuation_function: string option  -> prCnstr -> int list -> string list) =
    case pr_formula of
      PrBind(id_list, (Let,_), _, continuation_formula) =>
	(case hyp_name of 
	   SOME hyp_name => 
	     (case path of 
		(3::path_tail) => SOME(continuation_function (SOME hyp_name) continuation_formula path_tail)
	      | _ => SOME([]))
	 | NONE => 	     
	     let 
	       val used_names = ref []	       
	       fun command i = (do_list (fn x =>
					 used_names := (PbpInput.mkNameLoc x)::(!used_names))
				(rev (first_n i id_list));
				format_commands ("intros"::(!used_names)))
	     in (case path of 
		   1::x::path_tail => SOME([command x])
		 | 1::_ => SOME([command (length id_list)])
		 | 2::_ => SOME([command (length id_list)])
		 | 3::path_tail => let val continuation = continuation_function NONE continuation_formula path_tail
				   in SOME((command (length id_list))::continuation)
				   end
		 | _ => bug "Unexpected Annotation in Let")
	     end)
	 | _ => NONE

	    (*
fun pbp_impr2 (SOME H) (PrBind([], (Pi,Vis), _, B))
	     (2::2::path_tail) continuation
	     = let val b = PbpInput.mkNameLoc "b"
      in  SOME (["Refine impl_elim " ^ H,"intros +1 " ^ b] @
		continuation (SOME b) B path_tail)
      end
  | pbp_impr2 _ _ _ _ = NONE

 The following function combines all four rules for implication *)

				     
fun pbp_imply
    (hyp_name: string option)
    (pr_formula:prCnstr)
    (path: int list)
    (continuation_function: string option 
        -> prCnstr -> int list -> string list) =
   case pr_formula of
     PrBind([], (Pi,Vis), type_formula, continuation_formula) =>
    (* then you can retrieve the path that will also be used in the
       recursive call *)
	 let val new_name1 = PbpInput.mkNameLoc "H"
    in
	(case path of  (2::1::path_tail) =>
	     (case hyp_name of
		 SOME hyp_name =>
		     (** This is not quite satisfying, 

		      Gamma,A->B |- C

		      should be tranformed to

		      Gamma,A->B |- A   and   Gamma,A->B,B |- C

		      Instead, we get

		      Gamma,A->B |- A   and   Gamma,A->B |- B->C

		      because LEGO's design insists on sharing contexts **)
		     SOME(["Refine impl_elim " ^ hyp_name] @
			  (continuation_function NONE type_formula
			   path_tail))
	       | NONE => 
		     let 
			 val cont = continuation_function 
			     (SOME new_name1) type_formula path_tail
		     in
			 SOME(("Intros " ^ new_name1)::cont)
		     end)
      | (2::2::path_tail) =>
	    (case hyp_name of
		SOME hyp_name =>
		    SOME(["Refine impl_elim " ^ hyp_name,
			  "intros +1 " ^ new_name1] @
			 continuation_function (SOME new_name1)
			 continuation_formula path_tail)
	      | NONE => 
		    let val cont = continuation_function 
			NONE continuation_formula path_tail
		    in SOME(("Intros " ^ new_name1)::cont) end)
      | _ => NONE			(* SOME [] would increase efficiency *)
	    )
	 end
| _ => NONE;

(*** 

 Yves Bertot and Laurent Théry write:

 "The proof-by-pointing algorithm terminates when no rule matches the
 formula and path given as arguments, most often because the path has
 been reduced to length 0. When this happens, the algorithm must
 provide a command that will be called on the last produced subgoal.
 To generate this command there are two cases:

   - the box may reappear in an assumption. In this case, the command
     should check whether this assumption matches the conclusion so
     that the goal might be closed,

   - the box may reappear in the conclusion. In this case, the command
     should look for an assumption that makes it possible to close the
     goal"

  These cases are handled in the function `pbp_catch_empty_path'
***)

fun pbp_catch_empty_path (SOME hyp_name) _ [] _
    = SOME ["Try Refine " ^ hyp_name]

  | pbp_catch_empty_path NONE _ [] _
    = SOME ["Try Assumption"]

  | pbp_catch_empty_path _ _ _ _
    = NONE

val PBP_RULES = ref ([] : (string *
  (string option -> prCnstr -> 
  int list ->
   (string option -> prCnstr -> int list -> string list)
   -> string list option)) list);



fun remove_pbp_rule s =
    let fun remove_rec ((cpl as (s1,_))::l) = if s1 = s then l else 
              (cpl::(remove_rec l))
          | remove_rec [] = (bug "this rule name does not occur")
    in
      PBP_RULES := (remove_rec (!PBP_RULES))
    end;

fun add_pbp_rule name funct = 
     PBP_RULES := ((!PBP_RULES)@[(name,funct)]);

fun pbp (hyp:string option) (term:prCnstr) (path:int list) =
  let fun try_all_rules rl = 
      case rl of ((_,f)::tl) =>
        (case (f hyp term path pbp) of SOME(command_list) => command_list
           | NONE => (try_all_rules tl))
      | [] => []
  in
      try_all_rules (!PBP_RULES)
  end;


fun pbptop_default goal_no path =
    let
	val _ = PbpInput.initNameLoc()
	val (exvar,goal) = PbpInput.getCurrentGoal()
	val string_list = (if exvar=goal_no
			       then (fn id=>id)
			   else fn res => ("Next " ^makestring goal_no)::res)
	    (pbp NONE goal path)
    in
	(output (std_out, "\250 Pbp result \251\n");
	 output_string_list string_list;
	 output (std_out, "\250 End Pbp result \251\n"))
    end

val PBPTOP_VAR = ref pbptop_default;

fun pbptop goal_and_path = (!PBPTOP_VAR) goal_and_path;

fun set_pbptop f = PBPTOP_VAR := f;

fun pbphyptop_default hyp_name path =
    let
	val _ = PbpInput.initNameLoc()
	val string_list = pbp (SOME hyp_name)
	                      (PbpInput.getAssumption hyp_name) path
    in
     (output (std_out, "\250 Pbp result \251\n");
      output_string_list string_list;
      output (std_out, "\250 End Pbp result \251\n"))
    end;


val PBPHYPTOP_VAR = ref pbphyptop_default;

fun pbphyptop name path= (!PBPHYPTOP_VAR) name path;

fun set_pbphyptop f = PBPHYPTOP_VAR := f;

fun pbp_initialize () =
    (PBP_RULES := [("pbp_catch_empty_path",pbp_catch_empty_path),
		   ("pbp_forall",pbp_forall), 
		   ("pbp_imply", pbp_imply),
		   ("pbp_let", pbp_let)
		   ];
     PBPTOP_VAR := pbptop_default;
     PBPHYPTOP_VAR := pbphyptop_default);




end; (*local*)
end; (*struct*)

functor FunPbpInput (structure Concrete:CONCRETE
		     structure Namespace:NAMESPACE) : PBPINPUT =
    struct
	val initNameLoc = Namespace.initNameLoc
	val mkNameLoc   = Namespace.mkNameLoc
	val NextTac     = Namespace.NextTac

	fun getCurrentGoal () =
	    case Namespace.getCurrentGoals() of
		((Namespace.Unknown((exvar,goal)::_)::_)) =>
		    (exvar,LegoFormat.ffp LegoFormat.implicit false goal)
	      | _ => bug "getCurrentGoal: no unknown goals found"

        fun getAssumption s = LegoFormat.ffp LegoFormat.implicit false
	    (snd (Concrete.fEval (Concrete.Ref_c s)))
    end
