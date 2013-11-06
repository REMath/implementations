(* error.sml    Error handling for LEGO
   Author: Thomas Schreiber <tms@dcs.ed.ac.uk>
   $Log: error.sml,v $
   Revision 1.7  1997/11/24 11:00:57  tms
   merged immed-may-fail with main branch


   Revision 1.6  1997/08/25 10:59:15  tms
   Immed fails if no progress has been achieved

   Revision 1.5  1997/07/11 13:27:06  tms
   Qrepl will fail if the LHS does not occur in the goal

   Revision 1.4  1997/05/08 13:46:36  tms
   Extended expansion mechanism relative to a path

   Revision 1.3  1997/02/17 17:39:10  tms
   added support for failed Assumption command

*)

functor FunLegoError(ErrorFormatting:ERRORFORMATTING) : ERROR =
    struct
	local
	    open ErrorFormatting
	in
	    type cnstr = cnstr
	    datatype ErrorClass
		= ASSUMPTION | TYPEAPPLN | APPLNTYPE | APPLNNFUN |
		PATH | REPLLHS | IMMED

	    exception error of (ErrorClass,cnstr) ErrorSignal

	    fun append a b = a@b

	    fun prefix s
		= print o (block 2)
		      o append [formatString ("Error"
					      ^(if interactive() then
					      ""
						else " in file")^": "^s) ,newline]


	    fun leftmargin n bl
		= let
		      val s = (implode o ListUtil.genList) (n,fn _ => " ")
		  in
		      block n ((formatWord s)::bl::[newline])
		  end

	    fun ErrorHandler (ASSUMPTION,(SOME g):int option,[])
		= prefix ("Goal "^(makestring g)^
		" cannot be closed by an instance of any assumption") []

              | ErrorHandler (IMMED,_,[])
		= prefix ("No goal can be closed by an instance of \
			  \any assumption") []

	      | ErrorHandler (TYPEAPPLN,g,[c])
		= prefix " 'Type' must be either ambiguous or relative \
			    \to a universe i.e., a natural number or an \
			  \identifier, \
			    \but cannot refer to the term"
		[leftmargin 2 (cnstr_format false c),
		 formatString "Enclose 'Type' in parenthesis to achieve \
		     \full typical ambiguity."]
	      | ErrorHandler (APPLNTYPE,g,[v,t,v',t'])
		     = prefix "Type mismatch in attempting to apply"
		     [leftmargin 3 (cnstr_format true v),
		      formatString "with domain type", newline,
		      leftmargin 3 (cnstr_format true t),
		      block 3 [formatWord "to ",cnstr_format true v'], newline,
		      block 3 [formatWord " : ", cnstr_format true t']]

	      | ErrorHandler (APPLNNFUN, g, [c,T])
		= prefix "Application of a non-function"
		[leftmargin 3 (cnstr_format true c), 
		 block 3 [formatWord " : ", cnstr_format true T]]

	      | ErrorHandler (PATH, g, [c])
		= prefix "Illegal path specified"
		[formatString "The term", newline,
		 leftmargin 3 (cnstr_format false  c),
		 formatString "has been addressed with an illegal path"]

              | ErrorHandler (REPLLHS, (SOME g), [c])
		 = prefix "Qrepl Tactic"
		 [formatString "LHS", newline,
		  leftmargin 3 (cnstr_format false c),
		  formatString ("doesn't occur in goal "^(makestring g))]

              | ErrorHandler (IMMED, _, _)
		 = prefix "Immed Tactic failed" []

	      | ErrorHandler _ = print (formatString "Unexpected error!")
	end
    end

structure ErrorFormatting : ERRORFORMATTING
    = FunErrorFormatting (structure LegoFormat = LegoFormat);



