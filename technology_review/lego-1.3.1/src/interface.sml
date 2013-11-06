(* $Id: interface.sml,v 1.9 1998/09/16 14:32:58 tms Exp $ *)
functor FunLegoInterface ()

    : sig
	  val lego : unit -> unit
      end =
  struct

    fun parse (lookahead, reader:int->string, filename) =
      let
        val error = Pos.errmsg "Lego parser"
	val _ = Pos.init_lno()
        val dummyEOF = let val zzz = !Pos.lno
		       in  LegoLrVals.Tokens.EOF(zzz,zzz)
		       end
	fun invoke lexer = 
	   LegoParser.parse(lookahead,lexer,error,filename)
        fun loop lexer =
	  let val (result,lexer) = invoke lexer
	      val (nextToken,lexer) = LegoParser.Stream.get lexer
              val _ = map (fn knot => knot ())
		          (PromptKnots.seek_all_knots (fn _ => true))
	  in if LegoParser.sameToken(nextToken,dummyEOF) then ()
	     else loop lexer
	  end
     in loop (LegoParser.makeLexer reader)
     end

(* file parser *)
    fun legof (ntk as ((filnam,filtim),loadkind,DepChecking)) closeAct =
      let
	val in_str = open_in filnam
	  handle Io s => failwith("Unexpected error opening "^filnam^":\n"^s)
	val _ = if DepChecking 
	            then loudmessage ("(* checking "^filnam^" *)")
		    else loudmessage ("(* opening file "^filnam^" *)")
	val _ = go_to_file()                  (* show non-interactive *)
	val t = start_timer()
	fun closing() = ((if not DepChecking then
			     loudmessage("(* closing file "^
				     filnam^"; "^(makestring_timer t)^" *)")
			 else ());
			 exit_file();         (* show possibly interactive *)
			 close_in in_str)
	fun err_closing s = (message("Error in file: "^s);
			     closing();
			     raise Io"Unwinding to top-level")
      in
	(
	 parse (15,(fn _ => input_line in_str),ntk)
	 handle Error.error s => (Error.ErrorHandler s; closing();
				  raise Io "Unwinding to top-level")
		| Failure s => err_closing s
		| Bug s => err_closing s
		| Io s => err_closing s
                | Modules.DepCheckDone(d) => (closing(); 
                                              raise Modules.DepCheckDone(d))
		| exn => err_closing
                     ("\nLEGO detects unexpected exception named \""^
		      System.exn_name exn^"\""))
        before (closing(); closeAct())
      end
    val _ = Modules.legoFileParser := legof;   (* Used to implement Include *)


(* string parser *)
(* NOTE: exceptions from string parser are thrown to next outer
 * file parser or toplevel *)
    fun legos str =
      let val string_reader = let val next = ref str
			      in  fn _ => !next before next := ""
			      end
      in parse (0,string_reader,(("",System.Timer.TIME{sec=0,usec=0}),
				 Modules.LK_STRING, false))
      end
    val _ = Modules.legoStringParser := legos;   (* Used to implement Logic *) 


    local
      fun catchTopCont() =
	(System.Unsafe.toplevelcont :=
	 callcc (fn k => (callcc (fn k' => (throw k k'));
			  raise Interrupt)))
    in  
      fun lego() =
	(catchTopCont();
	 Interactive();
	 parse (0,(fn _ => (LegoFormat.print std_out 
			   (LegoFormat.string 
				(if isAnnotating() then "Lego> \249"
				                   else "Lego> "));
			    flush_out std_out;
			    input_line std_in)),
	   (("",System.Timer.TIME{sec=0,usec=0}),Modules.LK_INTERACTIVE,false))
	 handle Error.error s => (Error.ErrorHandler s; lego())
	      | Failure s => (message("Error: "^s); lego())
	      | Bug s => (message s; lego())
	      | Io s => (message s; lego())
	      | LegoParser.ParseError => lego()
(********
	      | LegoLex.LexError => lego()
*********)
	      | exn => (message("\nLEGO detects unexpected exception named \""^
				System.exn_name exn^"\"");
			lego()))
	 handle Interrupt => (message"\nInterrupt.. "; lego())
    end;

end;
structure LegoInterface = FunLegoInterface (Error);
open LegoInterface;
