(* lexerint.ml *)
(* lexer interface *)
(* based on elkhound/lexerint.h *)


open Useract      (* tSemanticValue *)


(* the GLR parser will interact with the lexer via this interface *)
class virtual tLexerInterface =
object (self)
  (* ---- data ---- *)
  (* the following fields are used to describe the *current* token;
   * they are changed by getToken() each time it is called *)

  (* token classification, used by parser to make parsing decisions;
   * the value 0 means end of file *)
  val mutable tokType:int = 0;

  (* semantic value of the token *)
  val mutable sval:tSemanticValue = (Obj.repr 0);

  (* lexerint.h has a 'loc' field here... *)

  (* ---- funcs ---- *)
  (* data members aren't public... *)
  method getTokType() : int =           tokType
  method atEOF() : bool =               tokType=0
  method getSval() : tSemanticValue =   sval

  (* convenience during testing *)
  method setIntSval (i:int) : unit =    sval <- (Obj.repr i)
  method getIntSval() : int =          (Obj.obj sval : int)

  (* interface that must be implemented *)
  
  (* retrieve the next token, storing its information in tokType & sval *)
  method virtual getToken : unit -> unit

  (* yield a description of the current token *)
  method virtual tokenDesc : unit -> string

  (* yield a description of an arbitrary token kind *)
  method virtual tokenKindDesc : int -> string
end


(* EOF *)
