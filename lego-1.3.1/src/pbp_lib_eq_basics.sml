(*
   $Log: pbp_lib_eq_basics.sml,v $
   Revision 1.3  1997/11/24 11:01:48  tms
   merged immed-may-fail with main branch

   Revision 1.2.2.3  1997/10/13 16:47:17  djs
   More problems with the above.

   Revision 1.2.2.2  1997/10/13 16:21:37  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.2.2.1  1997/10/10 17:02:44  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.2  1997/07/11 13:29:08  tms
   Qrepl will fail if the LHS does not occur in the goal
   *)


(*
    a =b,G |- C[b/a]
   -----------------
   *a*=b,G |- C
*)


fun pbp_repl (SOME eq) (LegoFormat.PrApp (LegoFormat.PrRef Eq,_)) [2,1] _ =
    let val (ConfigEq ,_,_) = Namespace.findConfig "Equality" ("Eq","","")
    in
	if Eq=ConfigEq
	    then SOME ["Qrepl "^eq]
	else NONE
    end
  | pbp_repl _ _ _ _ = NONE;

(* alternative more basic implementation
fun pbp_repl (SOME eq)
             (LegoFormat.PrApp (LegoFormat.PrRef "Eq",_))
             [2,1] _ = SOME ["Qrepl "^eq]
  | pbp_repl _ _ _ _ = NONE;
*)
    
Pbp.add_pbp_rule "pbp_repl" pbp_repl;
