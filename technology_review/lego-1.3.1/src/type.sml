(* 
   $Log: type.sml,v $
   Revision 1.4  1997/11/24 11:02:09  tms
   merged immed-may-fail with main branch

   Revision 1.3.2.3  1997/10/13 16:47:24  djs
   More problems with the above.

   Revision 1.3.2.2  1997/10/13 16:21:45  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.3.2.1  1997/10/10 17:02:50  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.3  1997/07/11 13:29:28  tms
   Qrepl will fail if the LHS does not occur in the goal
  
   Revision 1.2  1997/05/08 13:59:35  tms
   Generalised Expansion Mechanism to Cope with Path information
*)

functor FunType (Error:ERROR) : TYPE =
    struct

(* constant expansion *)
fun expand nam = 
    let fun exp_rec (Ref br) = 
              if nam=(ref_nam br) andalso ref_isDefnNow br
		then Mod(ref_VAL br) else UMod
          | exp_rec (App b) = mkApp exp_rec b
	  | exp_rec (Bind(b as ((Let,_),lnam,b1,b2))) =
	      if nam=lnam then Mod(subst1 b1 b2)
	      else mkBind2 exp_rec b
          | exp_rec (Bind b) = mkBind2 exp_rec b
          | exp_rec (Tuple b) = mkTuple exp_rec b
          | exp_rec (CnLst b) = mkCnLst exp_rec b
          | exp_rec (Proj b) = mkProj exp_rec b
          | exp_rec (RedTyp b) = mkRedTyp exp_rec b
          | exp_rec _ = UMod
     in share exp_rec end


fun expAll n = 
    let fun eArec n =
      if n <= 0 then (fn (_:cnstr) => UMod)
      else fn Ref(br)  => if ref_isDefnNow br then eArec (n-1) (ref_VAL br)
			  else UMod
            | App(b)   => mkApp (eArec (n-1)) b
	    | Bind(b)  => mkBind2 (eArec (n-1)) b
	    | CnLst(b) => mkCnLst (eArec (n-1)) b
	    | Proj(b)  => mkProj (eArec (n-1)) b
	    | RedTyp(b) => mkRedTyp (eArec (n-1)) b
	    | _        => UMod
    in share (eArec n) end;

(** Apply function to a subterm determined by a path **)
fun subtermApp path f =
    let
	fun subtermAppf [] term = f term
	  | subtermAppf (1::path) (App ((g,x),s))
	    = App ((subtermAppf path g,x),s)
	  | subtermAppf [2] (App ((g,x),s)) = App ((g,map f x),s)
	  | subtermAppf (2::i::path) (App ((g,x),s))
	    =
	    (let
		val (p,q) = ListUtil.split (i-1) x
	    in
		App ((g,p@[subtermAppf path (nth x i)]@(tl q)),s)
	    end handle _ => raise Error.error (Error.PATH,NONE,[App ((g,x),s)]))

	  | subtermAppf (2::path) (Bind (vs,id,A,B))
	    = Bind (vs,id,subtermAppf path A,B)
	  | subtermAppf (3::path) (Bind (vs,id,A,B))
	    = Bind (vs,id,A,subtermAppf path B)
	  | subtermAppf _ term = raise Error.error (Error.PATH,NONE,[term])
    in
	subtermAppf path
    end
end
