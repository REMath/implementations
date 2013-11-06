(* cml.sml *)

(* code to support parallel (time-sliced) search for conversion tests *)

val partm_debug = ref false;
val parunif_debug = ref false;

val par_tm_switch = ref true;
val par_unif_switch = ref false;

val timeslice = ref 50;

fun par_tm c d =
  (if not(!partm_debug) then ()
   else (message("**partm_deb: switch is "^makestring (!par_tm_switch));
	 prs"** "; legoprint c;
	 prs"** "; legoprint d);
   if not (!par_tm_switch) then UMtype_match c d
   else
     let
       val cml_tm_ans = ref false;
       fun cml_tm () =
	 let
	   val chan = CML.channel()
	   fun whnf_tm() = CML.send(chan,sameTerm c d orelse UMtype_match c d)
	   fun heur_tm() = CML.send(chan,type_match_heur c d)
	   val whnf_tid = CML.spawn whnf_tm
	   val heur_tid  = CML.spawn heur_tm
	   val _ = cml_tm_ans:= CML.accept chan
	 in
	   RunCML.shutdown()
	 end
     in
       (RunCML.doit(cml_tm,SOME(!timeslice)); !cml_tm_ans)
     end);
     
val _ = r_par_tm:= par_tm;  (** setup foward reference **)

fun par_unif s c d =
  (if not(!parunif_debug) then ()
   else (message("**parunif_deb: switch is "^makestring (!par_unif_switch));
	 prs"** "; legoprint c;
	 prs"** "; legoprint d);
   if not (!par_unif_switch) then type_match_unif s c d
   else
     let
       val cml_unif_ans = ref NONE;
       fun cml_unif () =
	 let
	   val chan = CML.channel()
	   fun Whnf_unif() =
	     case whnf_unif s c d of
	       x as (SOME t) => CML.send(chan,x)
	     | NONE => ()
	   fun heur_unif() = CML.send(chan,type_match_unif s c d)
	   val whnf_tid = CML.spawn Whnf_unif
	   val heur_tid  = CML.spawn heur_unif
	   val _ = cml_unif_ans:= CML.accept chan
	 in
	   RunCML.shutdown()
	 end
     in
       (RunCML.doit(cml_unif,SOME(!timeslice)); !cml_unif_ans)
     end);
     
