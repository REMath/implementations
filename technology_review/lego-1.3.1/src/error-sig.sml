(* error-sig.sml    Error handling for LEGO
   Author: Thomas Schreiber <tms@dcs.ed.ac.uk>
   $Log: error-sig.sml,v $
   Revision 1.7  1997/11/24 10:58:57  tms
   merged immed-may-fail with main branch

   Revision 1.6  1997/08/25 10:59:07  tms
   Immed fails if no progress has been achieved

   Revision 1.5  1997/07/11 13:26:58  tms
   Qrepl will fail if the LHS does not occur in the goal

   Revision 1.4  1997/05/08 13:46:27  tms
   Extended expansion mechanism relative to a path

   Revision 1.3  1997/02/17 17:39:01  tms
   added support for failed Assumption command
 

 Encountering an error, LEGO will raise an exception `error' provided
 by a structure Error:ERROR. The signatures ERROR and ERRORFORMATTING
 are defined in this file. A structure Errorformatting:ERRORFORMATTING
 will be used to implement the structure Error:ERROR in the file
 `error.sml'. An error is identified by its `ErrorSignal'
 encapsulating the `ErrorClass', the terms involved and, optionally,
 the number of the goal in question. The exception will be caught in
 the interface where an `ErrorHandler' will print an appropriate error
 message.

 ErrorClass  terms                  Reason for triggering Error
 ----------  -----                  ---------------------------

 ASSUMPTION  []                     no assumption closes the goal 

 TYPEAPPLN   [a,b]                  `Type (a b)' where `a b' is well-formed
                                    e.g. Type(([x:Type]x) Prop)
 APPLNTYPE   [v,dom v,w,type of w]  `v w' where the `dom v' is not equivalent to the
                                    `type of w', e.g. ([x:Prop]x) Prop

 APPLNNFUN   [c,T]                  c of type T has been applied, but is not
                                    a function

 IMMED       []                     no assumption closed any goal

 PATH        [c]                    the term c has been addressed with an 
                                    illegal path e.g., Expand 2 Prop

 REPLLHS     [c]                    the term c does not occur in the goal

 IMMED       []                     The tactic Immed was unsuccessful

 Currently, all other error messages are handled directly, but should
 be converted to use the new error handling structure `Error'.
 *)

signature ERRORFORMATTING =
    sig
	type format
	val print : format -> unit
	val formatWord : string -> format
	    
	val formatString : string -> format
	(* assumes that spaces seperate words *)

	val newline : format
	    
	val block : int -> format list -> format

	val cnstr_format : bool -> cnstr -> format
	(*  cnstr_format true  yields an extended form
	    cnstr_format false yields the standard form *)
    end;

type ('a,'b) ErrorSignal = 'a*(int option)*('b list)

signature ERROR =
    sig
	datatype ErrorClass = ASSUMPTION | TYPEAPPLN | APPLNTYPE | APPLNNFUN
	  | PATH | REPLLHS |IMMED
	exception error of (ErrorClass,cnstr) ErrorSignal
	val ErrorHandler : (ErrorClass,cnstr) ErrorSignal -> unit
    end;
