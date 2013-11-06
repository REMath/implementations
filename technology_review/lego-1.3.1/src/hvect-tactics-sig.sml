(* 
   $Log: hvect-tactics-sig.sml,v $
   Revision 1.2  1997/11/24 11:01:00  tms
   merged immed-may-fail with main branch

   Revision 1.1.2.3  1997/10/13 16:47:00  djs
   More problems with the above.

   Revision 1.1.2.2  1997/10/13 16:21:22  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.1.2.1  1997/10/10 17:02:13  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   *)
signature HVECTTACT =
    sig
        (* use the theorems tail_update and head_update to eliminate
	 all occurrences of hvect_update in the current goal. More
	 precisely, on discovering a subterm of the form

	   hvect_tail (hvect_update v x t)
	 
         invoke the command 

	   Qrepl tail_update v x t

         Similarily for hvect_head. *)
	 
	val ElimUpdate : unit -> unit
    end
	    
