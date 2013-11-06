(* 
   $Log: linkOpen.sml,v $
   Revision 1.10  1998/11/10 15:28:44  ctm
   ConorInductiveNeeds now uses Quartermaster

   Revision 1.9  1998/10/30 14:14:04  ctm
   quartermaster added

   Revision 1.8  1997/11/24 11:01:29  tms
   merged immed-may-fail with main branch

   Revision 1.7.2.3  1997/10/13 16:47:10  djs
   More problems with the above.

   Revision 1.7.2.2  1997/10/13 16:21:28  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.7.2.1  1997/10/10 17:02:31  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.7  1997/05/08 13:54:10  tms
   Generalised Expansion Mechanism to Cope with Path information
  
   Revision 1.6  1997/03/06 09:53:14  tms
   restructured module Pbp
  
   Revision 1.5  1997/02/17 17:40:26  tms 
   integrated error handler in tactics functor
*)

structure Error = FunLegoError (ErrorFormatting)
structure Machine = FunMachine (structure Error=Error)

structure UndoKnots = FunConorKnots(UndoKnotTypes)
structure Type = FunType (Error)

structure Namespace = FunNamespace (structure Machine=Machine
				    structure UndoKnots=UndoKnots
                                    structure Infix=Infix
					structure Type=Type)

structure Concrete = FunConcrete(structure Namespace=Namespace
				 structure Machine=Machine)

structure PbpInput = FunPbpInput(structure Concrete=Concrete
				 structure Namespace=Namespace)

structure Pbp = FunPbp (structure PbpInput=PbpInput)

open Concrete;

(*** lexer and parser  ***)
(* The "abstract type" of lexer positions *)
signature POS =
  sig
    type pos
    val lno : pos ref
    val init_lno : unit->unit
    val inc_lno : unit->unit
    val errmsg : string->(string*pos*pos)->unit
  end;
functor Pos() : POS =
  struct
    type pos = int
    val lno = ref 0
    fun init_lno() = lno:=1
    fun inc_lno() = lno:=(!lno)+1
    fun errmsg who (msg,line:pos,_) =
      message(who^"; line "^(makestring line)^": "^msg)
  end;

use"base.sml";
use"lego.grm.sig";
use"lego.grm.sml";
use"lego.lex.sml";

structure Pos:POS = Pos()


structure Synt =
  FunSynt (structure Concrete=Concrete
	   structure Namespace=Namespace)

structure Toplevel =
  FunToplevel (structure Namespace=Namespace
	       structure Machine=Machine
	       structure Concrete=Concrete
	       structure Synt=Synt)

structure Inductive =
  FunInductive (structure Concrete=Concrete
		structure Namespace=Namespace)

structure Quartermaster = FunQuartermaster (structure Concrete=Concrete
                                            structure Namespace=Namespace)

structure ConorInductiveNeeds:CONORINDUCTIVENEEDS =
    FunConorInductiveNeeds(structure Concrete=Concrete
			   structure Namespace=Namespace
                           structure Quartermaster=Quartermaster)

structure ConorInductive:CONORINDUCTIVE =
    FunConorInductive(structure ConorInductiveNeeds=ConorInductiveNeeds)

structure Top =
  FunTop (structure Toplevel=Toplevel
	  structure Concrete=Concrete
	  structure Namespace=Namespace
	  structure Synt=Synt
	  structure Inductive=Inductive
	  structure Type=Type
	  structure Record=FunRecord (structure Concrete=Concrete
				      structure Inductive=Inductive)
	  structure Relation=FunRelation(structure Namespace=Namespace
					 structure Concrete=Concrete
					 structure Inductive=Inductive)
	  structure Double=FunDouble(structure Concrete=Concrete
				     structure Inductive=Inductive)
	  structure Theorems=FunTheorems(structure Concrete=Concrete
					 structure Inductive=Inductive)
	  structure ConorInductive=ConorInductive)

structure Discharge =
  FunDischarge (structure Namespace=Namespace
		structure Concrete=Concrete)

structure Modules =
  FunModules(structure Top=Top
	     structure Toplevel=Toplevel
	     structure Namespace=Namespace
	     structure Synt=Synt)

structure Tactics =
  FunTactics (structure Toplevel=Toplevel
	      structure Namespace=Namespace
	      structure Concrete=Concrete
	      structure Synt=Synt
	       structure Error=Error)

structure ConorTopNeeds = FunConorTopNeeds (structure Concrete=Concrete
					    structure Tactics=Tactics
					    structure Toplevel=Toplevel
					    structure Synt=Synt
					    structure Namespace=Namespace
					    structure ConorInductiveNeeds=
						ConorInductiveNeeds)

structure ConorTop = FunConorTop (structure ConorTopNeeds=ConorTopNeeds)

structure PromptKnots = FunConorKnots(PromptKnotTypes)

structure ConorThen = FunConorThen(structure Namespace=Namespace
				   structure PromptKnots=PromptKnots
				   structure UndoKnots=UndoKnots)


structure Init =
  FunInit (structure Namespace=Namespace
	   structure Tactics=Tactics
	   structure Toplevel=Toplevel
           structure Infix=Infix
	   structure Top=Top
	   structure ConorThen=ConorThen)

structure Tacticals = FunTacticals (structure Namespace = Namespace
				    structure ConorThen = ConorThen)

structure LegoLrVals:Lego_LRVALS =
  LegoLrValsFun(structure Token = LrParser.Token
		structure Pos = Pos
		structure Error = Error
		structure Modules = Modules
		structure Top = Top
		structure Synt = Synt
		structure Tactics = Tactics
		structure Tacticals = Tacticals
		structure Toplevel = Toplevel
		structure Discharge = Discharge
		structure Init = Init
                structure Infix = Infix
		structure ConorTop = ConorTop
		structure ConorThen = ConorThen
                structure Quartermaster = Quartermaster)

structure LegoLex:LEXER =
  LegoLexFun(structure Tokens = LegoLrVals.Tokens
	     structure Pos = Pos
             structure Infix = Infix)

structure LegoParser:PARSER =
  Join(structure LrParser = LrParser
       structure ParserData = LegoLrVals.ParserData
       structure Lex = LegoLex
       structure Error = Error)
  
