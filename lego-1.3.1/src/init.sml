(* init.sml *)
(* Author: Randy Pollack <pollack@cs.chalmers.se> *)

(* CHANGES

   Thomas Schreiber <tms@lfcs.ed.ac.uk>
   February 1995
   Bernhard Reus <reus@informatik.uni-muenchen.de> and
   Peter Aczel <petera@cs.man.ac.uk> prefer small impredicative sigma
   types. To incorporate this extension, I have extended the switch
   ``Init'' *)

functor FunInit (structure Namespace:NAMESPACE
                 and Infix: INFIX
		 and Tactics:TACTICS
		 and Toplevel:TOPLEVEL
		 and Top:TOP
		 and ConorThen:CONORTHEN) (* : INIT *) =
  struct
    (* initialization function is defined last *)

    local
      fun Init x  =
	( set_inference x;
	 Init_universes();
	 init_reductions();
         Infix.init_infix();
	 Namespace.init_namespace();
	 Toplevel.init_toplevel();
	 Top.init_newtop();
	 ConorThen.InitConorThen();
	 Tactics.Config_Qrepl("","","");   (* init Qrepl to leibniz equality *)
	 message ((case theory()
		     of lf     => "LF"
		      | xtndCC => "Extended CC"
		      | pureCC => "Pure CC")
		  ^": Initial State!"));
      fun err() = failwith"MacroMode no longer supported"
    in
      fun Init_raw "LF"     = Init LF
	| Init_raw "PCC"    = Init PCC
	| Init_raw "XCC"    = (Init XCC; Predicativesums())
	| Init_raw "XCC'"   = err()
	| Init_raw "XCC_s"  = (Init XCC; ImpredicativeSums())
	| Init_raw "XCC'_s" = err()
	| Init_raw _        = failwith "LF, PCC, XCC or XCC_s expected"
    end
  end
