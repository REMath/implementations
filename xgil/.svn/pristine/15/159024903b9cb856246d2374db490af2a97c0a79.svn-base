(* main.ml *)
(* driver for an Elkhound parser written in OCaml *)

open Lexerint      (* tLexerInterface *)
open Lrparse       (* parse *)
open Glr           (* tGLR, makeGLR, glrParse *)
open Useract       (* tSemanticValue *)
open Parsetables   (* tParseTables *)
open Useract       (* tUserActions *)
open Arith         (* arithParseTables, arithUserActions *)
open Een           (* eenParseTables, eenUserActions *)
open Ptreeact      (* tParseTreeLexer, makeParseTreeActions *)
open Ptreenode     (* tPTreeNode, printTree *)
open Lexer         (* tToken, readToken *)
(* also uses Oc_arith, but with explicit qualification *)


(* ------------------ lexer ------------------- *)
let useHardcoded:bool = false        (* set to true for testing with ocamldebug *)

class tLexer =
object (self)
  inherit tLexerInterface

  (* stdin *)
  val lexbuf:Lexing.lexbuf =
    if (useHardcoded) then (
      (Lexing.from_string "2+3")     (* hardcoded input *)
    )
    else (
      (Lexing.from_channel stdin)
    );

  (* this method exists so that I can give the lexbuf directly to an
   * ocamlyacc parser, for performance/testing purposes *)
  method getLexbuf() : Lexing.lexbuf =
  begin
    lexbuf
  end

  method getToken() : unit =
  begin
    (* read from stdin *)
    let t:tToken = (readToken lexbuf) in
    
    (* break the tToken apart into a kind and an sval; perhaps
     * this belongs in lexer.mll too? *)
    match t with
    | INT(i) -> (
        tokType <- 1;
        (self#setIntSval i);
      )
    | _ -> (
        tokType <- (tokenKind t);
        (self#setIntSval 0);           (* clear previous *)
      )
  end

  method tokenDesc() : string =
  begin
    let kindDesc:string = (self#tokenKindDesc tokType) in
    if (tokType = 1) then (
      kindDesc ^ "(" ^ (string_of_int (self#getIntSval())) ^ ")"
    )
    else
      kindDesc
  end

  method tokenKindDesc (kind:int) : string =
  begin
    (Lexer.tokenKindDesc kind)
  end
end


let printTokens (lex:tLexerInterface) : unit =
begin
  (lex#getToken ());
  while (not ((lex#getTokType()) = 0)) do
    (Printf.printf "tokType=%d sval=%d desc=\"%s\"\n"
                   (lex#getTokType())
                   (lex#getIntSval())
                   (lex#tokenDesc())
                 );
    (flush stdout);
    (lex#getToken ());
  done
end


(* Substitute readToken; I need to translate between the tokens
 * that my lexer yields and the tokens that the ocamlyacc parser
 * expects.  I *could* have just used the ocamlyacc tokens
 * throughout, but then this example would be more dependent on
 * ocamlyacc than I want. *)
let ocReadToken (lexbuf: Lexing.lexbuf) : Oc_arith.token =
begin
  let t: tToken = (Lexer.readToken lexbuf) in
  match t with
  | EOF ->       Oc_arith.EOF
  | INT(n) ->    Oc_arith.TOK_NUMBER(n)
  | PLUS ->      Oc_arith.TOK_PLUS
  | MINUS ->     Oc_arith.TOK_MINUS
  | TIMES ->     Oc_arith.TOK_TIMES
  | DIV ->       Oc_arith.TOK_DIVIDE
  | LPAREN ->    Oc_arith.TOK_LPAREN
  | RPAREN ->    Oc_arith.TOK_RPAREN
end


(* --------------------- main -------------------- *)
let main() : unit =
begin
  (* random tests *)
  (if false then (
    (Printf.printf "Sys.max_array_length: %d\n" Sys.max_array_length);
    (Printf.printf "Sys.max_string_length: %d\n" Sys.max_string_length);
  ));

  (* defaults *)
  let useGLR: bool ref = ref true in
  let useArith: bool ref = ref true in
  let justTokens: bool ref = ref false in
  let usePTree: bool ref = ref false in
  let useOcamlyacc: bool ref = ref false in

  (* process arguments *)
  for i=1 to ((Array.length Sys.argv) - 1) do
    match Sys.argv.(i) with
    | "lr" ->         useGLR := false
    | "glr" ->        useGLR := true
    | "arith" ->      useArith := true
    | "een" ->        useArith := false
    | "tokens" ->     justTokens := true
    | "ptree" ->      usePTree := true
    | "ocamlyacc" ->  useOcamlyacc := true
    | op -> (
        (Printf.printf "unknown option: %s\n" op);
        (flush stdout);
        (failwith "bad command line syntax");
      )
  done;

  (* create the lexer *)
  let lex_orig:tLexer = (new tLexer) in
  let lex:tLexerInterface = (lex_orig :> tLexerInterface) in
  if (!justTokens) then (
    (* just print all the tokens and bail *)
    (printTokens lex);
    (raise Exit);       (* close enough *)
  );

  if (!useOcamlyacc) then (
    let lexbuf: Lexing.lexbuf = (lex_orig#getLexbuf ()) in
    let result: int = (Oc_arith.main ocReadToken lexbuf) in
    (Printf.printf "ocamlyacc result: %d\n" result);
    (raise Exit);
  );

  (* prime the lexer: get first token *)
  (lex#getToken());

  (* get parse tables and user actions, depending on which
   * grammar the user wants to use *)
  let (tables:tParseTables), (actions:tUserActions) =
    if (!useArith) then (
      (arithParseTables, arithUserActions)
    )
    else (
      (eenParseTables, eenUserActions)
    )
  in

  (* substitute tree-building actions? *)
  let (lex':tLexerInterface), (actions':tUserActions) =
    if (!usePTree) then (
      ((new tParseTreeLexer lex actions),      (* tree lexer *)
       (makeParseTreeActions actions tables))  (* tree actions *)
    )
    else (
      (lex, actions)                           (* unchanged *)
    )
  in
  
  (* parse the input *)
  let sval:tSemanticValue =
    if (not !useGLR) then (
      (* use LR *)
      (parse lex' tables actions')
    )
    else (
      (* use GLR *)
      let glr:tGLR = (makeGLR tables actions') in
      let treeTop: tSemanticValue ref = ref cNULL_SVAL in

      if (not (glrParse glr lex' treeTop)) then (
        (failwith "GLR parse error")
      );

      (* print accounting statistics from glr.ml *)
      (Printf.printf "stack nodes: num=%d max=%d\n"
                     !numStackNodesAllocd
                     !maxStackNodesAllocd);
      (Printf.printf "detShift:     %d\n" glr.detShift);
      (Printf.printf "detReduce:    %d\n" glr.detReduce);
      (Printf.printf "nondetShift:  %d\n" glr.nondetShift);
      (Printf.printf "nondetReduce: %d\n" glr.nondetReduce);
      (flush stdout);
      
      !treeTop
    )
  in

  (* interpret the result *)
  if (not !usePTree) then (
    (* assume it's an int *)
    let s:int = ((Obj.obj sval) : int) in
    (Printf.printf "%s parse result: %d\n"
                   (if (!useGLR) then "GLR" else "LR")
                   s);
  )
  else (
    (* it's a tree *)
    let t:tPTreeNode = ((Obj.obj sval) : tPTreeNode) in
    (printTree t stdout true(*expand*));
  );
  (flush stdout);

end
;;

let outerMain() : unit =
begin
  try
    (main())
  with
  | Exit -> ()
end
;;

Printexc.catch outerMain()
;;
