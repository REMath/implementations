(* ptreeact.ml *)
(* given actions for a grammar, wrap them with actions that
 * just build a parse tree (forsest) *)
(* based on elkhound/ptreeact *)


open Lexerint       (* tLexerInterface *)
open Parsetables    (* tParseTables *)
open Useract        (* tUserActions *)
open Ptreenode      (* tPTreeNode *)


(* ------------------------ tParseTreeLexer ------------------------- *)
(* wrap the lexer with one yielding parse tree leaf nodes *)
class tParseTreeLexer
  (underlying: tLexerInterface)        (* underlying lexer *)
  (actions: tUserActions) =            (* for getting symbol names *)
object (self)
  inherit tLexerInterface

  (* underlying lexer is already primed *)
  initializer (self#copyFields())

  method getToken() : unit =
  begin
    (underlying#getToken());           (* get next token *)
    (self#copyFields());               (* make new leaf *)
  end

  method private copyFields() : unit =
  begin
    tokType <- (underlying#getTokType());

    (* my sval is a tree leaf *)
    sval <- (Obj.repr (makePTreeNode (actions.terminalName tokType)));
  end

  method tokenDesc() : string =
  begin
    (underlying#tokenDesc())
  end

  method tokenKindDesc (kind:int) : string =
  begin
    (underlying#tokenKindDesc kind)
  end
end


(* ----------------------- parseTreeActions ------------------------ *)
let makeParseTreeActions (underlying: tUserActions) (tables: tParseTables) 
  : tUserActions =
begin
  let actions:tUserActions = {
    (* action to perform upon performing a reduction *)
    reductionAction = (
      fun (prodId:int) (svals: tSemanticValue array) -> (
        (* production info *)
        let rhsLen:int = (getProdInfo_rhsLen tables prodId) in
        let lhsIndex:int = (getProdInfo_lhsIndex tables prodId) in
        
        (* make a tree node, initially with no children *)
        let ret:tPTreeNode = (makePTreeNode (underlying.nonterminalName lhsIndex)) in

        (* add the children *)
        (setNumChildren ret rhsLen);
        for i=0 to rhsLen-1 do
          let child:tPTreeNode = (Obj.obj svals.(i) : tPTreeNode) in
          (setChild ret i child);
        done;
        
        (Obj.repr ret)
      ));
      
    (* duplicate a semantic value: trivial *)
    duplicateTerminalValue = (fun _ sval -> sval);
    duplicateNontermValue = (fun _ sval -> sval);

    (* deallocate an sval that didn't get used: trivial *)
    deallocateTerminalValue = (fun _ _ -> ());
    deallocateNontermValue = (fun _ _ -> ());

    (* merge svals for alternative derivations of the same nonterminal *)
    mergeAlternativeParses = (
      fun (ntIndex:int) (left:tSemanticValue) (right:tSemanticValue) -> (
        let l:tPTreeNode = ((Obj.obj left) : tPTreeNode) in
        let r:tPTreeNode = ((Obj.obj right) : tPTreeNode) in
        
        (addAlternative l r);
        (Obj.repr l)
      ));

    (* choose whether to keep or drop a reduced value: trivial *)
    keepNontermValue = (fun _ _ -> true);

    terminalDescription = (fun id _ -> (underlying.terminalName id));
    nonterminalDescription = (fun id _ -> (underlying.nonterminalName id));
    terminalName = (fun id -> (underlying.terminalName id));
    nonterminalName = (fun id -> (underlying.nonterminalName id));
  } in
  
  actions
end


(* EOF *)
