
(* 
Pretty printing.  From Paulson, ML for the Working Programmer.
Page 312.  A few things have been changed, to adjust them to my taste:

    1) The type T is now called "block"
    2) The Pretty module is now a structure, instead of functor, to make it 
easy to pretty print with blocks composed out of types from different structures.
    3) The print procedure no longer prints a newline after pretty printing
the block.   This allows blocks to be pretty printed "in line".

author: Tom Gordon <thomas.gordon@gmd.de>

CHANGES
-------

30 Nov 1994 Thomas Schreiber <lego@dcs.ed.ac.uk>
            The variable active dictates wheter pretty printing is desired

20 Dec 1995 Extended the datatype block with linebreaks

28 Dec 1995 supporting multiple print commands in one line 

28 Jun 1996 replacement for BASE's input_line
*)


structure Pretty  : PRETTY =
    struct
	datatype block = 
	    Block of block list * int * int 	(*indentation, length*)
	  | String of string
	  | Linebreak
	  | Annotate of int list
	  | Break of int;			(*length*)

(* Add the lengths of the expressions until the next Break; if no
Break then include "after", to account for text following this block.
*)

	val indent = ref 4  (* spaces *)
	val linelength = ref 78
	val active     = ref true
	val space      = ref (!linelength)

	fun breakdist (Block(_,_,len)::bs, after) = 
	         len + breakdist(bs, after)
	  | breakdist (String s :: bs, after) = 
	         size s + breakdist (bs, after)
	  | breakdist (Annotate _ :: bs, after) = breakdist (bs,after)
	  | breakdist (Break _ :: bs, after) = 0
	  | breakdist (Linebreak :: bs,after) = 0 
	  | breakdist ([], after) = after;

	fun SetLineLength ll = (space := !space + ll - !linelength;
				linelength := ll)

	fun input_line s = let
			       val result = IO.input_line s
			   in
			       space := (!linelength);
			       result
			   end

	val last_path = ref ([]: int list)

	fun compress_path t =
	    let fun slice i old [] = [i]
		  | slice i [] new = i::new
		  | slice i (p::old) (n::new) = 
		    if p = n then slice (i+1) old new else i::n::new
	    in 	let val path' = slice 0 (!last_path) t
		in (last_path := t; 
		    implode (map (fn x => chr (x+128)) path'))
		end
	    end

	    
	fun print os b  =
	    (let 
		fun blanks 0 = ()
		  | blanks n = (output(os," ");  space := !space - 1; 
				blanks(n-1))

		fun newline () = (output(os,"\n");  space := (!linelength))

		fun printing ([], _, _) = ()
		  | printing (b::bs, blockspace, after) =
		    (case b of
			 Block(bbs,indent,len) =>
			     printing(bbs, !space-indent, 
				      breakdist(bs,after))
		       | String s => (output(os,s);   space := !space - size s)
		       | Annotate s => 
			     if s <> [] andalso (hd s) = 252 
				 then output(os, "\252") 
			     else
				 output(os,"\250"^(compress_path s)^"\251")
		       | Linebreak => newline()
		       | Break len => 
			     if ((len + breakdist(bs,after) <= !space) orelse
				 (not (!active)))
				 then blanks len
			     else (newline(); 
				   blanks((!linelength)-blockspace));
				 printing (bs, blockspace, after))
	    in  
               (last_path:=[];
		printing([b], (!linelength), 0))
	    end);

	fun length (Block(_,_,len)) = len
	  | length (String s) = size s
	  | length (Annotate _) = 0
	  | length (Break len) = len
	  | length Linebreak = 0;

	val string = String  and  break = Break  and linebreak = Linebreak
	                     and annotate = Annotate    

	fun block (indent,bs) =
	    let fun sum([], k) = k
		  | sum(b::bs, k) = sum(bs, length b + k)
	    in  Block(bs,indent, sum(bs,0))  end;
    end;


