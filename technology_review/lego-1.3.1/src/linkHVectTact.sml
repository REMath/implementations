(* 
   $Log: linkHVectTact.sml,v $
   Revision 1.2  1997/11/24 11:01:26  tms
   merged immed-may-fail with main branch

   Revision 1.1.2.3  1997/10/13 16:47:09  djs
   More problems with the above.

   Revision 1.1.2.2  1997/10/13 16:21:27  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.1.2.1  1997/10/10 17:02:29  djs
   Made everything work on Solaris, by taking out some nested comments.
*)

structure HVectTact =
    FunHVectTact
    (structure Lego=funHVectTactReg (structure Concrete=Concrete
				     structure Namespace=Namespace
				     structure Tactics=Tactics)
     structure Concrete=Concrete);

Tactics.add_tactic "hvect_updateE" HVectTact.ElimUpdate
