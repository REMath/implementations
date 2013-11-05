(* parsetables.ml *)
(* representation of parsing tables *)
(* based on elkhound/parsetables.h *)


(* The C++ implementation is designed so the sizes of the various
 * table entries can be adjusted.  I'm reflecting that design here,
 * but I am just using 'int' as the size choice everywhere, since
 * (I think) OCaml arrays don't get smaller if you use (e.g.) char.
 *
 * The way to make array of char efficiently is using strings, but
 * that's a TODO at best, for now.
 *)


(* for action entries; some places may still be called int *)
type tActionEntry = int

(* identifier for a state in the finite automaton *)
type tStateId = int
let cSTATE_INVALID = -1

(* entry in the goto table *)
type tGotoEntry = int

(* index for a terminal *)
type tTermIndex = int

(* index for a nonterminal *)
type tNtIndex = int

(* index for a production *)
type tProdIndex = int

(* ErrorBitsEntry goes here *)


(* encode a symbol in the 'stateSymbol' map *)
(*   N+1:  terminal N *)
(*   0:    no symbol *)
(*   -N-1: nonterminal N *)
type tSymbolId = int
let symIsTerm (id: tSymbolId) : bool =        id > 0
let symAsTerm (id: tSymbolId) : int =         id-1      (* why not TermIndex? don't know *)
let symIsNonterm (id: tSymbolId) : bool =     id < 0
let symAsNonterm (id: tSymbolId) : tNtIndex = -id-1


(* collection of data needed for the online parsing algorithm *)
type tParseTables = {
  (* grammar counts *)
  numTerms: int;
  numNonterms: int;
  numProds: int;

  (* # of states in LR automaton *)
  numStates: int;

  (* action table, indexed by (state*actionCols + lookahead) *)
  actionCols: int;
  actionTable: tActionEntry array;

  (* goto table, indexed by (state*gotoCols + nontermId) *)
  gotoCols: int;
  gotoTable: tGotoEntry array;

  (* production info, indexed by production id *)
  prodInfo_rhsLen: int array;         (* this is 'unsigned char' array in C++ *)
  prodInfo_lhsIndex: tNtIndex array;

  (* map state to symbol shifted to arrive at that state *)
  stateSymbol: tSymbolId array;

  (* ambiguous actions: one big list, for allocation purposes; then
   * the actions encode indices into this table; the first indexed
   * entry gives the # of actions, and is followed by that many
   * actions, each interpreted the same way ordinary 'actionTable'
   * entries are *)
  ambigTableSize: int;                (* redudant in OCaml... *)
  ambigTable: tActionEntry array;

  (* total order on nonterminals; see elkhound/parsetables.h *)
  nontermOrder: tNtIndex array;

  (* TODO: implement some of the table compression options? *)

  (* start state id (always 0) *)
  startState: tStateId;
  
  (* index of last production to reduce *)
  finalProductionIndex: int;
}


(* ------------- sample parse tables (from arith.gr.gen.cc) ------------ *)
let handcoded_arithParseTables:tParseTables = {
  numTerms = 8;
  numNonterms = 4;
  numProds = 8;

  numStates = 16;

  actionCols = 8;
  actionTable = [|    (* 128 elements *)
    (* 0*) 0; 3; 0; 0; 0; 0; 8; 0;
    (* 1*) 0; 0; 0; 0; 0; 0; 0; 0;
    (* 2*) -6; 0; -6; -6; -6; -6; 0; -6;
    (* 3*) 0; 3; 0; 0; 0; 0; 8; 0;
    (* 4*) 0; 3; 0; 0; 0; 0; 8; 0;
    (* 5*) 0; 3; 0; 0; 0; 0; 8; 0;
    (* 6*) 0; 3; 0; 0; 0; 0; 8; 0;
    (* 7*) 0; 3; 0; 0; 0; 0; 8; 0;
    (* 8*) -8; 0; -8; -8; -8; -8; 0; -8;
    (* 9*) 2; 0; 4; 5; 6; 7; 0; 0;
    (*10*) 0; 0; 4; 5; 6; 7; 0; 9;
    (*11*) -2; 0; -2; -2; 6; 7; 0; -2;
    (*12*) -3; 0; -3; -3; 6; 7; 0; -3;
    (*13*) -4; 0; -4; -4; -4; -4; 0; -4;
    (*14*) -5; 0; -5; -5; -5; -5; 0; -5;
    (*15*) -7; 0; -7; -7; -7; -7; 0; -7
  |];

  gotoCols = 4;
  gotoTable = [|     (* 64 elements *)
    (* 0*) 65535; 65535; 9; 15;
    (* 1*) 65535; 65535; 65535; 65535;
    (* 2*) 65535; 65535; 65535; 65535;
    (* 3*) 65535; 65535; 11; 15;
    (* 4*) 65535; 65535; 12; 15;
    (* 5*) 65535; 65535; 13; 15;
    (* 6*) 65535; 65535; 14; 15;
    (* 7*) 65535; 65535; 10; 15;
    (* 8*) 65535; 65535; 65535; 65535;
    (* 9*) 65535; 65535; 65535; 65535;
    (*10*) 65535; 65535; 65535; 65535;
    (*11*) 65535; 65535; 65535; 65535;
    (*12*) 65535; 65535; 65535; 65535;
    (*13*) 65535; 65535; 65535; 65535;
    (*14*) 65535; 65535; 65535; 65535;
    (*15*) 65535; 65535; 65535; 65535
  |];

  prodInfo_rhsLen = [|       (* 8 elements *)
    (*0*) 2; 3; 3; 3; 3; 1; 1; 3
  |];
  prodInfo_lhsIndex = [|     (* 8 elements *)
    (*0*) 1; 2; 2; 2; 2; 2; 2; 3
  |];

  stateSymbol = [|           (* 16 elements *)
    (*0*) 0; 1; 2; 3; 4; 5; 6; 7; 8; -3; -3; -3; -3; -3; -3; -4
  |];

  ambigTableSize = 0;
  ambigTable = [| |];        (* 0 elements *)

  nontermOrder = [|          (* 4 elements *)
    (*0*) 3; 2; 1; 0
  |];

  startState = 0;
  finalProductionIndex = 0
} 


(* -------------- ParseTables client access interface -------------- *)
let getActionEntry (tables: tParseTables) (state: int) (tok: int) : tActionEntry =
begin
  tables.actionTable.(state * tables.actionCols + tok)
end

let getActionEntry_noError (tables: tParseTables) (state: int) (tok: int) : tActionEntry =
begin
  (getActionEntry tables state tok)
end


let isShiftAction (tables: tParseTables) (code: tActionEntry) : bool =
begin
  code > 0 && code <= tables.numStates
end

(* needs tables for compression *)
let decodeShift (code: tActionEntry) (shiftedTerminal: int) : tStateId =
begin
  code-1
end

let isReduceAction (code: tActionEntry) : bool =
begin
  code < 0
end

(* needs tables for compression *)
let decodeReduce (code: tActionEntry) (inState: tStateId) : int =
begin
  -(code+1)
end

let isErrorAction (*tables*) (code: tActionEntry) : bool =
begin
  code = 0
end

                       
(* this returns an index into the ambigTable *)
(* needs tables for compression *)
let decodeAmbigAction (tables: tParseTables) (code: tActionEntry) 
                      (inState: tStateId) : int =
begin
  code - 1 - tables.numStates
end


let getGotoEntry (tables: tParseTables) (stateId: tStateId)
                 (nontermId: int) : tGotoEntry =
begin
  tables.gotoTable.(stateId * tables.gotoCols + nontermId)
end

(* needs tables for compression *)
let decodeGoto (code: tGotoEntry) (shiftNonterminal: int) : tStateId =
begin
  code
end


let getProdInfo_rhsLen (tables: tParseTables) (rule: int) : int =
begin
  tables.prodInfo_rhsLen.(rule)
end

let getProdInfo_lhsIndex (tables: tParseTables) (rule: int) : int =
begin
  tables.prodInfo_lhsIndex.(rule)
end


let getNontermOrdinal (tables: tParseTables) (idx: int) : int =
begin
  tables.nontermOrder.(idx)
end


(* EOF *)
