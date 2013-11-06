(* 
   $Log: type-sig.sml,v $
   Revision 1.2  1997/11/24 11:02:05  tms
   merged immed-may-fail with main branch

   Revision 1.1.2.2  1997/10/13 16:21:44  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.

   Revision 1.1.2.1  1997/10/10 17:02:49  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.1  1997/05/08 13:59:20  tms
   Generalised Expansion Mechanism to Cope with Path information
*)


signature TYPE =
    sig
	val expand : string -> cnstr -> cnstr
     (* expand s c expands all occurrences of s in c *)
   
        val expAll : int -> cnstr -> cnstr
     (* expAll 0 c       = c
        expAll (suc n) c expands all definitions in (expAll n c) *)

        val subtermApp : int list -> (cnstr -> cnstr) -> cnstr -> cnstr
     (* subtermApp p f c uses f to translate a subterm of c. The subterm
        is characterised by the path p; see the module pbp for further 
        details *)
    end
        	
