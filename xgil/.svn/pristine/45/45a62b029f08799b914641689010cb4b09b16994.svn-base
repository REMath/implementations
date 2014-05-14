(* useract.ml *)
(* interface for user-defined reduction (etc.) actions *)
(* based on elkhound/useract.h *)

(* for now, some actual user actions *)


(* secret to type casting in OCaml: the Obj module *)
type tSemanticValue = Obj.t
let cNULL_SVAL = (Obj.repr 0)


(* collection of actions for use during parsing *)
(* again, see elkhound/useract.h for more info *)
type tUserActions = {
  (* action to perform upon performing a reduction *)
  reductionAction:
    (*context?*)
    int ->                     (* production being used to reduce *)
    tSemanticValue array ->    (* array of svals for RHS symbols *)
    (*loc?*)
    tSemanticValue;            (* sval for the reduction *)

  (* duplicate a semantic value *)
  duplicateTerminalValue:
    (*context?*)
    int ->                     (* terminal id *)
    tSemanticValue ->          (* sval being yielded *)
    tSemanticValue;            (* sval to yield next time *)
  duplicateNontermValue:
    (*context?*)
    int ->                     (* nonterminal id *)
    tSemanticValue ->          (* sval being yielded *)
    tSemanticValue;            (* sval to yield next time *)

  (* deallocate an sval that didn't get used *)
  deallocateTerminalValue:
    (*context?*)
    int ->                     (* terminal id *)
    tSemanticValue ->          (* sval being dropped *)
    unit;
  deallocateNontermValue:
    (*context?*)
    int ->                     (* nonterminal id *)
    tSemanticValue ->          (* sval being dropped *)
    unit;

  (* merge svals for alternative derivations of the same nonterminal *)
  mergeAlternativeParses:
    int ->                     (* nonterminal with two derivations *)
    tSemanticValue ->          (* sval from derivation 1 *)  
    tSemanticValue ->          (* sval from derivation 2 *)
    tSemanticValue;            (* merged sval *)
    
  (* choose whether to keep or drop a reduced value *)
  keepNontermValue:
    int ->                     (* reduced nonterm id *)
    tSemanticValue ->          (* sval that 'reductionAction' yielded *)
    bool;                      (* if false, drop the sval on the floor *)
    
  (* reclassification goes here *)
  
  (* debugging support; see useract.h for more info *)
  terminalDescription: int -> tSemanticValue -> string;
  nonterminalDescription: int -> tSemanticValue -> string;
  terminalName: int -> string;
  nonterminalName: int -> string;
} 


(* ---------------- sample reduction actions -------------- *)
let handcoded_arithUserActions = {
  reductionAction = (fun prodId svals -> (
    (* this is how ocamlyacc does it, so I assume it's the fastest way *)
    let actions : (tSemanticValue array -> tSemanticValue) array = [|
      (fun svals ->
        let top = (Obj.obj svals.(0) : int) in
        (Obj.repr (
          top
        ))
      );
      (fun svals ->
        let e1 = (Obj.obj svals.(0) : int) in
        let e2 = (Obj.obj svals.(2) : int) in
        (Obj.repr (
          e1 + e2
        ))
      );
      (fun svals ->
        let e1 = (Obj.obj svals.(0) : int) in
        let e2 = (Obj.obj svals.(2) : int) in
        (Obj.repr (
          e1 - e2
        ))
      );
      (fun svals ->
        let e1 = (Obj.obj svals.(0) : int) in
        let e2 = (Obj.obj svals.(2) : int) in
        (Obj.repr (
          e1 * e2
        ))
      );
      (fun svals ->
        let e1 = (Obj.obj svals.(0) : int) in
        let e2 = (Obj.obj svals.(2) : int) in
        (Obj.repr (
          e1 / e2
        ))
      );
      (fun svals ->
        let n = (Obj.obj svals.(0) : int) in
        (Obj.repr (
          n
        ))
      );
      (fun svals ->
        let p = (Obj.obj svals.(0) : int) in
        (Obj.repr (
          p
        ))
      );
      (fun svals ->
        let e = (Obj.obj svals.(1) : int) in
        (Obj.repr (
          e
        ))
      )
    |] in
    (actions.(prodId) svals)
  ));
  
  duplicateTerminalValue = (fun termId sval -> sval);
  duplicateNontermValue = (fun termId sval -> sval);
  
  deallocateTerminalValue = (fun termId sval -> ());
  deallocateNontermValue = (fun termId sval -> ());
  
  mergeAlternativeParses = (fun nontermId sval1 sval2 -> sval1);
  
  keepNontermValue = (fun nontermId sval -> true);

  terminalDescription = (fun termId sval -> "TODO");
  nonterminalDescription = (fun termId sval -> "TODO");

  terminalName = (fun termId -> "TODO");
  nonterminalName = (fun termId -> "TODO")
}


(* EOF *)
