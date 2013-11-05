(* glr.ml *)
(* GLR parser *)
(* based on elkhound/glr.h and elkhound/glr.cc *)

open Arraystack      (* tArrayStack *)
open Objpool         (* tObjPool *)
open Useract         (* tSemanticValue *)
open Lexerint        (* tLexerInterface *)
open Parsetables     (* action/goto/etc. *)
open Smutil          (* getSome, etc. *)


(* Relative to C++ implementation, what is not done:
 *   - Token reclassification
 *   - Table compression
 *   - Heavy testing of the mini-LR core
 *)


(* when true, print parse actions *)
let traceParse:bool = false

(* when true, keep some statistics useful for performance evaluation *)
let accounting:bool = true

(* when true, we call the user's keep() functions *)
let use_keep:bool = true

(* when true, use the mini LR core *)
let use_mini_lr:bool = true


(* NOTE: in some cases, more detailed comments can be found in
 * elkhound/glr.h, as these data structures mirror the ones
 * defined there *)


(* identifier for a symbol *)
type tSymbolId = int


(* link from one stack node to another *)
type tSiblingLink = {
  (* stack node we're pointing at; == cNULL_STACK_NODE if none *)
  mutable sib: tStackNode;

  (* semantic value on this link *)
  mutable sval: tSemanticValue;

  (* TODO: source location *)

  (* possible TODO: yield count *)
}

(* node in the GLR graph-structured stack; all fields are
 * mutable because these are stored in a pool for explicit re-use *)
and tStackNode = {
  (* LR parser state when this node is at the top *)
  mutable state: tStateId;

  (* pointers to adjacent (to the left) stack nodes *)
  (* possible TODO: put links into a pool so I can deallocate them *)
  mutable leftSiblings: tSiblingLink list;

  (* logically first sibling in the sibling list; separated out
   * from 'leftSiblings' for performance reasons *)
  mutable firstSib: tSiblingLink;

  (* number of sibling links pointing at this node, plus the
   * number of worklists this node appears in *)
  mutable referenceCount: int;

  (* number of links we can follow to the left before hitting a node
   * that has more than one sibling *)
  mutable determinDepth: int;

  (* for access to parser context in a few unusual situations *)
  mutable glr: tGLR;

  (* position of token that was active when this node was created
   * (or pulled from pool); used in yield-then-merge calculations *)
  mutable column: int;
}

(* this is a path that has been queued for reduction;
 * all fields mutable to support pooling *)
and tPath = {
  (* rightmost state's id *)
  mutable startStateId: tStateId;

  (* production we're going to reduce with *)
  mutable prodIndex: int;

  (* column from leftmost stack node *)
  mutable startColumn: int;

  (* the leftmost stack node itself *)
  mutable leftEdgeNode: tStackNode;

  (* array of sibling links, i.e. the path; 0th element is
   * leftmost link *)
  sibLinks: tSiblingLink array ref;

  (* corresponding array of symbol ids to interpret svals *)
  symbols: tSymbolId array ref;

  (* next path in dequeueing order *)
  mutable next: tPath option;
}

(* priority queue of reduction paths *)
and tReductionPathQueue = {
  (* head of the list, first to dequeue *)
  mutable top: tPath option;

  (* pool of path objects *)
  pathPool: tPath tObjectPool;

  (* need our own copy of the tables pointer *)
  rpqTables: tParseTables;      (* name can't collide with tGLR.tables.. ! *)
}


(* GLR parser object *)
(* some mutable fields are for hack in 'makeGLR' *)
and tGLR = {
  (* user-specified actions *)
  userAct: tUserActions;

  (* parse tables from the grammar *)
  tables: tParseTables;

  (* for debugging, so I can ask for token descriptions in places *)
  mutable lexerPtr: tLexerInterface option;

  (* set of topmost parser nodes *)
  mutable topmostParsers: tStackNode tArrayStack;

  (* treat this as a local variable of rwlProcessWorklist, included
   * here just to avoid unnecessary repeated allocation *)
  toPass: tSemanticValue array;

  (* swapped with 'topmostParsers' periodically, for performance reasons *)
  mutable prevTopmost: tStackNode tArrayStack;

  (* node allocation pool; shared with innerGlrParse *)
  mutable stackNodePool: tStackNode tObjectPool;

  (* reduction queue and pool *)
  mutable pathQueue: tReductionPathQueue;

  (* when true, print some diagnosis of failed parses *)
  mutable noisyFailedParse: bool;

  (* current token number *)
  mutable globalNodeColumn: int;
  
  (* parser action statistics *)
  mutable detShift: int;
  mutable detReduce: int;
  mutable nondetShift: int;
  mutable nondetReduce: int;
}



(* what follows is based on elkhound/glr.cc *)


(* -------------------- misc constants --------------------- *)
(* maximum RHS length for mini-lr core *)
let cMAX_RHSLEN = 30

let cTYPICAL_MAX_REDUCTION_PATHS = 5

let cINITIAL_RHSLEN_SIZE = 10


(* ------------------ accounting statistics ----------------- *)
let numStackNodesAllocd: int ref = ref 0

let maxStackNodesAllocd: int ref = ref 0


(* ----------------- front ends to user code --------------- *)
let symbolDescription (sym: tSymbolId) (user: tUserActions) 
                      (sval: tSemanticValue) : string =
begin
  if (symIsTerm sym) then (
    (user.terminalDescription (symAsTerm sym) sval)
  )
  else (
    (user.nonterminalDescription (symAsNonterm sym) sval)
  )
end

let duplicateSemanticValue (glr: tGLR) (sym: tSymbolId) (sval: tSemanticValue)
  : tSemanticValue =
begin
  (assert (sym <> 0));
                                
  (* the C++ implementation checks for NULL sval, but I don't think
   * that can be here in the ML version, and I'm not convinced the
   * check would even be safe *)

  if (symIsTerm sym) then (
    (glr.userAct.duplicateTerminalValue (symAsTerm sym) sval)
  )
  else (
    (glr.userAct.duplicateNontermValue (symAsNonterm sym) sval)
  )
end

let deallocateSemanticValue (sym: tSymbolId) (user: tUserActions) 
                            (sval: tSemanticValue) : unit =
begin
  (assert (sym <> 0));

  if (symIsTerm sym) then (
    (user.deallocateTerminalValue (symAsTerm sym) sval)
  )
  else (
    (user.deallocateNontermValue (symAsNonterm sym) sval)
  )
end


(* --------------------- SiblingLink ----------------------- *)
(* NULL sibling link *)
let cNULL_SIBLING_LINK:tSiblingLink = {
  sib = (Obj.magic []);
  sval = cNULL_SVAL;
}

let makeSiblingLink (s: tStackNode) (sv: tSemanticValue) : tSiblingLink =
begin
  { sib=s; sval=sv; }
end


(* --------------------- StackNode -------------------------- *)
(* NULL stack node *)
let cNULL_STACK_NODE:tStackNode = {
  state          = cSTATE_INVALID;
  leftSiblings   = [];
  firstSib       = (Obj.magic []);
  referenceCount = 0;
  determinDepth  = 0;
  glr            = (Obj.magic []);
  column         = 0
}

let emptyStackNode(g : tGLR) : tStackNode =
begin
  {
    state = cSTATE_INVALID;
    leftSiblings = [];
    firstSib = (makeSiblingLink cNULL_STACK_NODE cNULL_SVAL);
    referenceCount = 0;
    determinDepth = 0;
    glr = g;
    column = 0
  }
end


let getNodeSymbol (ths: tStackNode) : tSymbolId =
begin
  ths.glr.tables.stateSymbol.(ths.state)
end

let rec deallocSemanticValues (ths: tStackNode) : unit =
begin
  if (ths.firstSib.sib != cNULL_STACK_NODE) then (
    (deallocateSemanticValue (getNodeSymbol ths) ths.glr.userAct ths.firstSib.sval)
  );

  (List.iter
    (fun s -> (
      (deallocateSemanticValue (getNodeSymbol ths) ths.glr.userAct s.sval);

      (* this is implicit in the C++ version, due to Owner<> *)
      (decRefCt s.sib)
    ))
    ths.leftSiblings);
  ths.leftSiblings <- [];
end

and initStackNode (ths: tStackNode) (st: tStateId) : unit =
begin
  ths.state <- st;
  (assert (isEmpty ths.leftSiblings));
  (assert (ths.firstSib.sib == cNULL_STACK_NODE));
  ths.referenceCount <- 0;
  ths.determinDepth <- 1;

  if (accounting) then (
    (incr numStackNodesAllocd);
    if (!numStackNodesAllocd > !maxStackNodesAllocd) then (
      maxStackNodesAllocd := !numStackNodesAllocd;
    );
    (*
      (Printf.printf "(!!!) init stack node: num=%d max=%d\n"
                     !numStackNodesAllocd
                     !maxStackNodesAllocd);
      (flush stdout);
    *)
  );
end

and deinitStackNode (ths: tStackNode) : unit =
begin
  (deallocSemanticValues ths);

  (* this is implicit in the C++ implementation because firstSib.sib
   * is an RCPtr in C++ *)
  (if (ths.firstSib.sib != cNULL_STACK_NODE) then (
    (decRefCt ths.firstSib.sib)
  ));

  ths.firstSib.sib <- cNULL_STACK_NODE;

  if (accounting) then (
    (decr numStackNodesAllocd);
    (*
      (Printf.printf "(...) deinit stack node: num=%d max=%d\n"
                     !numStackNodesAllocd
                     !maxStackNodesAllocd);
      (flush stdout);
    *)
  );
end

and incRefCt (ths: tStackNode) : unit =
begin
  ths.referenceCount <- ths.referenceCount + 1;
end

and decRefCt (ths: tStackNode) : unit =
begin
  (assert (ths.referenceCount > 0));

  ths.referenceCount <- ths.referenceCount - 1;

  (*(Printf.printf "decrementing node %d to %d\n" ths.state ths.referenceCount);*)
  (*(flush stdout);*)

  if (ths.referenceCount = 0) then (
    (deinitStackNode ths);
    (ths.glr.stackNodePool#dealloc ths)
  )
end

let hasZeroSiblings (ths: tStackNode) : bool =
begin
  (ths.firstSib.sib == cNULL_STACK_NODE)
end

let hasOneSibling (ths: tStackNode) : bool =
begin
  (ths.firstSib.sib != cNULL_STACK_NODE) && (isEmpty ths.leftSiblings)
end

let hasMultipleSiblings (ths: tStackNode) : bool =
begin
  (isNotEmpty ths.leftSiblings)
end

let addFirstSiblingLink_noRefCt (ths: tStackNode) (leftSib: tStackNode)
                                (sval: tSemanticValue) : unit =
begin
  (assert (hasZeroSiblings ths));

  ths.determinDepth <- leftSib.determinDepth + 1;

  (assert (ths.firstSib.sib == cNULL_STACK_NODE));
  ths.firstSib.sib <- leftSib;     (* update w/o refct *)

  ths.firstSib.sval <- sval;
end

let addAdditionalSiblingLink (ths: tStackNode) (leftSib: tStackNode)
                             (sval: tSemanticValue) : tSiblingLink =
begin
  (* now there is a second outgoing pointer *)
  ths.determinDepth <- 0;

  (* this was implicit in the C++ verison *)
  (incRefCt leftSib);

  let link:tSiblingLink = (makeSiblingLink leftSib sval) in
  ths.leftSiblings <- link :: ths.leftSiblings;
  link
end

let addSiblingLink (ths: tStackNode) (leftSib: tStackNode)
                   (sval: tSemanticValue) : tSiblingLink =
begin
  if (ths.firstSib.sib == cNULL_STACK_NODE) then (
    (addFirstSiblingLink_noRefCt ths leftSib sval);

    (* manually inc refct *)
    (incRefCt leftSib);

    (* pointer to firstSib.. *)
    ths.firstSib
  )
  else (
    (addAdditionalSiblingLink ths leftSib sval)
  )
end

let getUniqueLink (ths: tStackNode) : tSiblingLink =
begin
  (assert (hasOneSibling ths));
  ths.firstSib
end

let getLinkTo (ths: tStackNode) (another: tStackNode)
  : tSiblingLink (*not tStackNode!*) option =
begin
  (* first? *)
  if (ths.firstSib.sib == another) then (
    (Some ths.firstSib)
  )

  else (
    (* rest? *)
    try
      let link:tSiblingLink = (List.find
        (fun candidate -> (candidate.sib == another))
        ths.leftSiblings) in
      (Some link)
    with Not_found ->
      None
  )
end

(* printAllocStats goes here *)

let computeDeterminDepth (ths: tStackNode) : int =
begin
  if (hasZeroSiblings ths) then (
    1
  )
  else if (hasOneSibling ths) then (
    (* sibling's plus one *)
    ths.firstSib.sib.determinDepth + 1
  )
  else (
    (assert (hasMultipleSiblings ths));
    0
  )
end

let checkLocalInvariants (ths: tStackNode) : bool =
begin
  (computeDeterminDepth ths) = ths.determinDepth;
end


(* ----------------------- stack node list ops ---------------------- *)
let decParserList (lst: tStackNode tArrayStack) : unit =
begin
  (lst#iter (fun n -> (decRefCt n)))
end

let incParserList (lst: tStackNode tArrayStack) : unit =
begin
  (lst#iter (fun n -> (incRefCt n)))
end

let parserListContains (lst: tStackNode tArrayStack) (n: tStackNode) : bool =
begin
  (lst#contains (fun n2 -> n2 == n))
end


(* ----------------------------- GLR --------------------------------- *)
let rec makeGLR (tablesIn: tParseTables) (actions:tUserActions) : tGLR =
begin
  let glr:tGLR = {
    userAct = actions;
    tables = tablesIn;
    lexerPtr = None;
    topmostParsers = ((Obj.magic []) : tStackNode tArrayStack);  (* HACK!! *)
    toPass = (Array.make cMAX_RHSLEN cNULL_SVAL);
    prevTopmost = ((Obj.magic []) : tStackNode tArrayStack);     (* HACK!! *)
    stackNodePool = ((Obj.magic []) : tStackNode tObjectPool);   (* HACK!! *)
    pathQueue = ((Obj.magic []) : tReductionPathQueue);          (* HACK!! *)
    noisyFailedParse = true;
    globalNodeColumn = 0;
    detShift = 0;
    detReduce = 0;
    nondetShift = 0;
    nondetReduce = 0
  } in

  (* finish nasty hack: I've got a bootstrapping problem where I can't
   * make the pool before the GLR, nor the other way around; so I fell back
   * on the trusted_cast to get it off the ground, and now I have to
   * fix it
   *
   * The main problem here is that because I'm doing explicit deallocation,
   * ML gets to see the objects while they're in limbo.  I *could* mark
   * some fields 'option' but that would not properly reflect the design.
   * So I prefer this local (if gross) hack to something that pollutes the
   * design itself.
   *
   * In fact, I *did* use the 'option' approach for tSiblingLink.sib,
   * and it is indeed a pain.
   * UPDATE: Switched to using Obj.magic there too, for performance.
   *)

  glr.topmostParsers <- (new tArrayStack cNULL_STACK_NODE);
  glr.prevTopmost <- (new tArrayStack cNULL_STACK_NODE);
  glr.stackNodePool <- (new tObjectPool (fun () -> (emptyStackNode glr)));
  glr.pathQueue <- (makeReductionPathQueue tablesIn);
                   
  if (use_mini_lr) then (
    (* check that none of the productions exceed cMAX_RHSLEN *)
    for i=0 to (glr.tables.numProds-1) do
      let len:int = (getProdInfo_rhsLen glr.tables i) in
      if (len > cMAX_RHSLEN) then (
        (* I miss token concatenation...*)
        (Printf.printf "Production %d contains %d right-hand side symbols,\nbut the GLR core has been compiled with a limit of %d.\nPlease adjust cMAX_RHSLEN and recompile the GLR core.\n"
                       i len cMAX_RHSLEN);
        (flush stdout);
        (failwith "cannot continue");
      );
    done;
  );

  glr
end

(* printConfig goes here *)

and grabTopSval (glr: tGLR) (node: tStackNode) : tSemanticValue =
begin
  let sib:tSiblingLink = (getUniqueLink node) in
  let ret:tSemanticValue = sib.sval in
  sib.sval <- (duplicateSemanticValue glr (getNodeSymbol node) sib.sval);

  (* TRSACTION("dup'd " << ret << " for top sval, yielded " << sib->sval); *)

  ret
end


(* macro in C++ version *)
and mMAKE_STACK_NODE (*dest is retval*) (state: tStateId) (glr: tGLR)
                     (pool: tStackNode tObjectPool) : tStackNode =
begin
  let dest:tStackNode = (pool#alloc()) in
  (initStackNode dest state);
  dest.column <- glr.globalNodeColumn;
  dest
end

and makeStackNode (glr: tGLR) (state: tStateId) : tStackNode =
begin
  (mMAKE_STACK_NODE state glr glr.stackNodePool)
end


and addTopmostParser (glr: tGLR) (parsr: tStackNode) : unit =
begin
  (assert (checkLocalInvariants parsr));

  (glr.topmostParsers#push parsr);
  (incRefCt parsr);

  (* no USE_PARSER_INDEX *)
end


(* buildParserIndex goes here *)

and glrParse (glr: tGLR) (lexer: tLexerInterface)
             (treeTop: tSemanticValue ref) : bool =
begin
  (* should reset this to None on all exit paths *)
  glr.lexerPtr <- (Some lexer);

  let ret:bool = (innerGlrParse glr lexer treeTop) in

  (* this takes care of above obligation unless exception, oh well *)
  glr.lexerPtr <- None;

  ret
end

and innerGlrParse (glr: tGLR) (lexer: tLexerInterface)
                  (treeTop: tSemanticValue ref) : bool =
begin
  (* make some things into local variables *)
  let userAct:tUserActions = glr.userAct in
  let tables:tParseTables = glr.tables in
  let topmostParsers: tStackNode tArrayStack = glr.topmostParsers in

  (*nextToken*)

  (*reclassifier*)

  (* the C++ implementation is careful to allocate the main pointer on
   * the stack to save an indirection; but I can't do that in the ML
   * version, so may as well just let the GLR object own the pool *)
  let stackNodePool: tStackNode tObjectPool = glr.stackNodePool in

  glr.globalNodeColumn <- 0;
  begin
    let first:tStackNode = (makeStackNode glr 0(*startState*)) in
    (addTopmostParser glr first);
  end;

  (* array for passing semantic values in the mini lr core *)
  let toPass: tSemanticValue array = (Array.make cMAX_RHSLEN cNULL_SVAL) in

  let localDetShift: int ref = ref 0 in
  let localDetReduce: int ref = ref 0 in

  (* main parsing loop *)
  try
    let rec main_loop (jump_to_mini_lr:bool) : bool =
    begin(
      if (not jump_to_mini_lr) then (
        if (traceParse) then (
          (Printf.printf "---- processing token %s, %d active parsers ----\n"
                         (lexer#tokenDesc())
                         (glr.topmostParsers#length())
          );
          (Printf.printf "Stack:%s\n" (stackSummary glr));
          (flush stdout);
        );

        (* reclassifyToken *)
      );
      
      (* ------------ glr parser ------------ *)
      (* pulled out so I can use this block of statements in several places *)
      let glrParseToken () : unit =
      begin
        if (not (nondeterministicParseToken glr)) then (
          (raise Exit)              (* "return false" *)
        );

        (* goto label: getNextToken *)
        (* last token? *)
        if (lexer#atEOF()) then (
          (raise End_of_file)       (* "break" *)
        );

        (* get the next token *)
        (lexer#getToken());
      end in

      (* --------- mini-lr parser ------- *)
      (* see elkhound/glr.cc for more details *)
      (* goto label: tryDeterministic *)
      if (use_mini_lr &&
          (topmostParsers#length()) = 1) then (
        let parsr: tStackNode ref = ref (topmostParsers#top()) in
        (assert (!parsr.referenceCount = 1));

        let tok:int = (lexer#getTokType()) in
        let action:tActionEntry = (getActionEntry_noError tables !parsr.state tok) in

        if (isReduceAction action) then (
          if (accounting) then (
            (incr localDetReduce);
          );
          let prodIndex:int = (decodeReduce action !parsr.state) in
          let rhsLen:int = (getProdInfo_rhsLen tables prodIndex) in
          if (rhsLen <= !parsr.determinDepth) then (
            (* can reduce unambiguously *)
            let lhsIndex:int = (getProdInfo_lhsIndex tables prodIndex) in

            let startStateId:int = !parsr.state in

            (assert (rhsLen <= cMAX_RHSLEN));

            (* loop for arbitrary rhsLen *)
            for i = rhsLen-1 downto 0 do
              (* grab the (only) sibling of 'parsr' *)
              let sib:tSiblingLink = !parsr.firstSib in

              (* store its semantic value in the 'toPass' array *)
              toPass.(i) <- sib.sval;

              (* pop 'parsr' and move to next one *)
              (stackNodePool#dealloc !parsr);
              let prev:tStackNode = !parsr in
              parsr := sib.sib;

              (assert (!parsr.referenceCount = 1));
              (assert (prev.referenceCount = 1));

              (* adjust a couple things about 'prev' reflecting
               * that it has been deallocated *)
              (decr numStackNodesAllocd);
              prev.firstSib.sib <- cNULL_STACK_NODE;

              (assert (!parsr.referenceCount = 1));
            done;

            (* call the user's action function (TREEBUILD) *)
            let sval:tSemanticValue =
              (userAct.reductionAction prodIndex toPass) in

            (* now, do an abbreviated 'glrShiftNonterminal' *)
            let newState:int = (decodeGoto
              (getGotoEntry tables !parsr.state lhsIndex)
            lhsIndex) in

            if (traceParse) then (
              (Printf.printf "state %d, (unambig) reduce by %d (len=%d), back to %d then out to %d\n"
                             startStateId
                             prodIndex
                             rhsLen
                             !parsr.state
                             newState);
              (flush stdout);
            );

            (* the sole reference is the 'parsr' variable *)
            (assert (!parsr.referenceCount = 1));

            (* push new state *)
            let newNode:tStackNode =
              (mMAKE_STACK_NODE newState glr stackNodePool) in

            (addFirstSiblingLink_noRefCt newNode !parsr sval);

            (assert (!parsr.referenceCount = 1));

            (* replace old topmost parser with 'newNode' *)
            (topmostParsers#setElt 0 newNode);
            (incRefCt newNode);
            (assert (newNode.referenceCount = 1));

            (* does the user want to keep it? *)
            if (use_keep &&
                (not (userAct.keepNontermValue lhsIndex sval))) then (
              (printParseErrorMessage glr newNode.state);
              if (accounting) then (
                glr.detShift <- glr.detShift + !localDetShift;
                glr.detReduce <- glr.detReduce + !localDetReduce;
              );

              (raise Exit)               (* "return false" *)
            );

            (* we have not shifted a token, so again try to use
             * the deterministic core *)
            (main_loop true(*jump*))     (* "goto tryDeterministic;" *)
          )
          else (
            (* deterministic depth insufficient: use GLR *)
            (glrParseToken());
            (main_loop false)            (* tail call *)
          )
        )

        else if (isShiftAction tables action) then (
          if (accounting) then (
            (incr localDetShift);
          );

          (* can shift unambiguously *)
          let newState:int = (decodeShift action tok) in

          if (traceParse) then (
            (Printf.printf "state %d, (unambig) shift token %d, to state %d\n"
                           !parsr.state
                           tok
                           newState);
            (flush stdout);
          );

          glr.globalNodeColumn <- glr.globalNodeColumn + 1;

          let rightSibling:tStackNode =
            (mMAKE_STACK_NODE newState glr stackNodePool) in

          (addFirstSiblingLink_noRefCt rightSibling !parsr (lexer#getSval()));

          (* replace 'parsr' with 'rightSibling' *)
          (topmostParsers#setElt 0 rightSibling);

          (assert (!parsr.referenceCount = 1));
          (assert (rightSibling.referenceCount = 0));

          rightSibling.referenceCount <- 1;

          (* get next token *)
          (* "goto getNextToken;" *)
          begin
            (* last token? *)
            if (lexer#atEOF()) then (
              (raise End_of_file)       (* "break" *)
            );

            (* get the next token *)
            (lexer#getToken());
          end;
          (main_loop false)      (* tail call *)
        )

        else (
          (* error or ambig; not deterministic *)
          (glrParseToken());
          (main_loop false)      (* tail call *)
        )
      )

      else (
        (* mini lr core disabled, use full GLR *)
        (glrParseToken());
        (main_loop false)        (* tail call *)
      )
    )end in
    (main_loop false)
  with
  | Exit -> false
  | End_of_file -> (
      if (accounting) then (
        glr.detShift <- glr.detShift + !localDetShift;
        glr.detReduce <- glr.detReduce + !localDetReduce;
      );

      (* end of parse *)
      (cleanupAfterParse glr (*timer*) treeTop)
    )
end

(* stackTraceString *)


and curToken (glr: tGLR) : int =
begin
  ((getSome glr.lexerPtr)#getTokType())
end

and nondeterministicParseToken (glr: tGLR) : bool =
begin
  let lastToDie: tStateId ref = ref cSTATE_INVALID in

  (* seed the reduction worklist by analyzing the top nodes *)
  (glr.topmostParsers#iter
    (fun parsr ->
     begin
       let tt:int = (curToken glr) in
       let action:tActionEntry = (getActionEntry glr.tables parsr.state tt) in
       let actions:int = (rwlEnqueueReductions glr parsr action None(*sibLink*)) in
       
       if (actions = 0) then (
         if (traceParse) then (
           (Printf.printf "parser in state %d died\n" parsr.state);
           (flush stdout)
         );
         lastToDie := parsr.state;
       );
     end));

  (* drop into worklist processing loop *)
  (rwlProcessWorklist glr);

  (* do all shifts last *)
  (rwlShiftTerminals glr);

  (* error? *)
  if (glr.topmostParsers#isEmpty()) then (
    (printParseErrorMessage glr !lastToDie);
    false
  )
  else (
    true
  )
end


and printParseErrorMessage (glr: tGLR) (lastToDie: tStateId) : unit =
begin
  if (not glr.noisyFailedParse) then () 
  else begin
    let lexer:tLexerInterface = (getSome glr.lexerPtr) in

    if (not (lastToDie = cSTATE_INVALID)) then (
      (Printf.printf "In state %d, I expected one of these tokens:\n" lastToDie);
      for i = 0 to (glr.tables.numTerms - 1) do
        let act:int = (getActionEntry glr.tables lastToDie i) in
        if (not (isErrorAction (*tables*) act)) then (
          (Printf.printf "  [%d] %s\n" i (lexer#tokenKindDesc i));
        );
      done;
    )
    else (
      (Printf.printf "(expected-token info not available due to nondeterministic mode\n");
    );

    (Printf.printf (*loc*) "Parse error (state %d) at %s\n"
                   lastToDie
                   (lexer#tokenDesc()));

    (flush stdout);
  end 
end


and doReductionAction (glr: tGLR) (productionId: int)
                      (svals: tSemanticValue array) : tSemanticValue =
begin
  (glr.userAct.reductionAction productionId svals)
end


and cleanupAfterParse (*timer*) (glr: tGLR) (treeTop: tSemanticValue ref) : bool =
begin
  if (traceParse) then (
    (Printf.printf "Parse succeeded!\n");
    (flush stdout);
  );

  if (not ((glr.topmostParsers#length()) = 1)) then (
    (Printf.printf "parsing finished with %d active parsers!\n"
                   (glr.topmostParsers#length()));
    (flush stdout);
    false     (* return *)
  )
  else begin
    let last:tStackNode = (glr.topmostParsers#top()) in

    (* prepare to run final action *)
    let arr: tSemanticValue array = (Array.make 2 cNULL_SVAL) in
    let nextToLast: tStackNode = (getUniqueLink last).sib in
    arr.(0) <- (grabTopSval glr nextToLast);      (* sval we want *)
    arr.(1) <- (grabTopSval glr last);            (* EOF's sval *)

    (* reduce *)
    treeTop := (doReductionAction glr glr.tables.finalProductionIndex arr);

    (* before pool goes away.. *)
    (decParserList glr.topmostParsers);

    true
  end 
end


and pullFromTopmostParsers (glr: tGLR) (parsr: tStackNode) : unit =
begin
  let last:int = (glr.topmostParsers#length()) - 1 in

  try
    for i=0 to last do
      if ((glr.topmostParsers#elt i) = parsr) then (
        (* remove by swapping *)
        if (i < last) then (
          (glr.topmostParsers#setElt i (glr.topmostParsers#elt last));
        );
        ignore (glr.topmostParsers#pop());   (* removes a reference *)
        (decRefCt parsr);                    (* so decrement *)
        raise Exit;      (* "break" *)
      )
    done
  with
  | Exit -> ()
end


and canMakeProgress (glr: tGLR) (parsr: tStackNode) : bool =
begin
  let entry:int =
    (getActionEntry glr.tables parsr.state (curToken glr)) in
    
  (isShiftAction glr.tables entry) ||
  (isReduceAction (*tables*) entry) ||
  (not (isErrorAction (*tables*) entry))
end


and findTopmostParser (glr: tGLR) (state: tStateId) : tStackNode option =
begin
  (* always using the *not* USE_PARSER_INDEX case *)
  (glr.topmostParsers#findOption
    (fun n -> n.state = state))
end


(* dumpGSS goes here *)
(* dumpGSSEdge goes here *)


and stackSummary (glr: tGLR) : string =
begin
  (* nodes already printed *)
  let printed: tStackNode list ref = ref [] in

  (* loop/fold *)
  let len:int = (glr.topmostParsers#length ()) in
  let rec loop (acc: string) (i: int) : string =
  begin
    if (i > len-1) then (
      acc                      (* done *)
    )
    else (
      let n:tStackNode = (glr.topmostParsers#elt i) in

      (loop
        (acc ^ " (" ^ (string_of_int i) ^ ": " ^
         (innerStackSummary printed n) ^
         ")")
        (i+1)
      )
    )
  end in

  (loop "" 0)
end
  
and nodeSummary (node: tStackNode) : string =
begin
  (string_of_int node.state) ^ 
  "[" ^ (string_of_int node.referenceCount) ^ "]"
end

and innerStackSummary (printed: tStackNode list ref) (node: tStackNode) : string =
begin
  if (List.exists
       (fun (n:tStackNode) -> n = node)
       !printed) then (
    (* already printed *)
    "(rep:" ^ (nodeSummary node) ^ ")"
  ) 
  
  else (  
    (* remember that we've now printed 'node' *)
    printed := node :: !printed;

    if (node.firstSib.sib == cNULL_STACK_NODE) then (
      (* no siblings *)
      (nodeSummary node)
    )

    else if (isEmpty node.leftSiblings) then (
      (* one sibling *)
      (nodeSummary node) ^ "-" ^ 
      (innerStackSummary printed node.firstSib.sib)
    )

    else (
      (* multiple siblings *)
      let tmp1:string =       (* force order of eval *)
        (nodeSummary node) ^ "-(" ^
        (innerStackSummary printed node.firstSib.sib) in
      tmp1 ^ (List.fold_left 
        (fun (acc:string) (link:tSiblingLink) -> (
          acc ^ "|" ^ (innerStackSummary printed link.sib)
        ))
        ""
        node.leftSiblings
      ) ^
      ")"
    )
  )
end


(* ------------------------ RWL algorithm ------------------------- *)
and makePath() : tPath =
begin
  {
    startStateId = cSTATE_INVALID;
    prodIndex = -1;
    startColumn = -1;
    leftEdgeNode = cNULL_STACK_NODE;
    sibLinks = ref (Array.make cINITIAL_RHSLEN_SIZE cNULL_SIBLING_LINK);
    symbols = ref (Array.make cINITIAL_RHSLEN_SIZE 0);
    next = None;
  }
end


and initPath (ths: tPath) (ssi: tStateId) (pi: int) (rhsLen: int) : unit =
begin
  ths.startStateId <- ssi;
  ths.prodIndex <- pi;

  (* just use the 0th elements as the dummy 'null' value *)
  (ensureIndexDoubler ths.sibLinks rhsLen ((!(ths.sibLinks)).(0)));
  (ensureIndexDoubler ths.symbols rhsLen ((!(ths.symbols)).(0)));
end


and makeReductionPathQueue (tablesIn: tParseTables) : tReductionPathQueue =
begin
  let allocator() : tPath = (makePath ()) in
  {
    top = None;
    pathPool = (new tObjectPool allocator);
    rpqTables = tablesIn;
  }
end


and newPath (ths: tReductionPathQueue) (ssi: tStateId) (pi: int) 
            (rhsLen: int) : tPath =
begin
  let p:tPath = (ths.pathPool#alloc()) in
  (initPath p ssi pi rhsLen);
  p
end


and insertPathCopy (ths:tReductionPathQueue) (src: tPath) 
                   (leftEdge: tStackNode) : unit =
begin
  let rhsLen:int = (getProdInfo_rhsLen ths.rpqTables src.prodIndex) in

  (* make a new node *)
  let p:tPath = (ths.pathPool#alloc()) in
  (initPath p src.startStateId src.prodIndex rhsLen);
  
  (* fill in left edge info *)
  p.leftEdgeNode <- leftEdge;
  p.startColumn <- leftEdge.column;
  
  (* copy path info *)
  (Array.blit
    !(src.sibLinks)       (* source array *)
    0                     (* source start position *)
    !(p.sibLinks)         (* dest array *)
    0                     (* dest start position *)
    rhsLen                (* number of elements to copy *)
  );
  (Array.blit
    !(src.symbols)        (* source array *)
    0                     (* source start position *)
    !(p.symbols)          (* dest array *)
    0                     (* dest start position *)
    rhsLen                (* number of elements to copy *)
  );
  
  (* find proper place to insert new path *)
  if ((isNone ths.top) || (goesBefore ths p (getSome ths.top))) then (
    (* prepend *)
    p.next <- ths.top;
    ths.top <- (Some p);
  )
  else (
    (* search *)
    let prev: tPath ref = ref (getSome ths.top) in
    while ((isSome !prev.next) && (not (goesBefore ths p (getSome !prev.next)))) do
      prev := (getSome !prev.next);
    done;

    (* insert *)
    p.next <- !prev.next;
    !prev.next <- (Some p);
  );
end

and goesBefore (ths: tReductionPathQueue) (p1: tPath) (p2: tPath) : bool =
begin
  if (p1.startColumn > p2.startColumn) then (
    (* 'p1' spans fewer tokens, so it goes first *)
    true
  )
  else if (p2.startColumn > p1.startColumn) then (
    (* same logic *)
    false
  )
  else (
    (* equal start columns, compare nonterm ids *)
    let p1NtIndex:int = (getProdInfo_lhsIndex ths.rpqTables p1.prodIndex) in
    let p2NtIndex:int = (getProdInfo_lhsIndex ths.rpqTables p2.prodIndex) in
    
    (* check nonterm order *)
    let ord1:int = (getNontermOrdinal ths.rpqTables p1NtIndex) in
    let ord2:int = (getNontermOrdinal ths.rpqTables p2NtIndex) in
    
    ord1 < ord2
  )
end


and dequeue (ths: tReductionPathQueue) : tPath =
begin
  let ret:tPath = (getSome ths.top) in
  ths.top <- ret.next;
  ret
end


and deletePath (ths: tReductionPathQueue) (p: tPath) : unit =
begin
  (ths.pathPool#dealloc p);
end


and queueIsNotEmpty (ths: tReductionPathQueue) : bool =
begin
  (isSome ths.top)
end

and rwlProcessWorklist (glr: tGLR) : unit =
begin
  while (queueIsNotEmpty glr.pathQueue) do
    (* process enabled reductions in priority order *)
    let path:tPath = (dequeue glr.pathQueue) in
    
    (* production info *)
    let rhsLen:int = (getProdInfo_rhsLen glr.tables path.prodIndex) in
    let lhsIndex:int = (getProdInfo_lhsIndex glr.tables path.prodIndex) in
    
    if (traceParse) then (
      (Printf.printf "state %d, reducing by production %d (rhsLen=%d), back to state %d\n"
                     path.startStateId
                     path.prodIndex
                     rhsLen
                     path.leftEdgeNode.state);
      (flush stdout);
    );
    
    if (accounting) then (
      glr.nondetReduce <- glr.nondetReduce + 1;
    );
    
    (* leftEdge *)
    
    (* before calling user's code, duplicate svals *)
    for i = (rhsLen-1) downto 0 do
      let sib:tSiblingLink = (!(path.sibLinks)).(i) in

      (* put the sval in the array that will be passed to the user *)
      glr.toPass.(i) <- sib.sval;

      (* source loc stuff *)

      (* ask user to duplicate, store that back in 'sib' *)
      sib.sval <- (duplicateSemanticValue glr (!(path.symbols)).(i) sib.sval);
    done;
    
    (* invoke user's reduction action (TREEBUILD) *)
    let sval:tSemanticValue =
      (doReductionAction glr path.prodIndex glr.toPass) in

    (* did user want to keep? *)
    if (use_keep &&
        (not (glr.userAct.keepNontermValue lhsIndex sval))) then (
      (* cancelled; drop on floor *)
    )
    else (
      (* shift the nonterminal, sval *)
      let newLink: tSiblingLink option =
        (rwlShiftNonterminal glr path.leftEdgeNode lhsIndex sval) in

      if (isSome newLink) then (
        (* for each 'finished' parser, enqueue actions enabled by the new link *)
        (glr.topmostParsers#iter
          (fun parsr ->
            let action:tActionEntry =
              (getActionEntry glr.tables parsr.state (curToken glr)) in
            ignore (rwlEnqueueReductions glr parsr action newLink)
          ));
      );
    );
                                   
    (* we dequeued it above, and are now done with it, so recycle
     * it for future use *)
    (deletePath glr.pathQueue path)
  done;
end


and rwlShiftNonterminal (glr: tGLR) (leftSibling: tStackNode) (lhsIndex: int)
                        (sval: tSemanticValue) : tSiblingLink option =
begin
  (* consult goto table to find where to go upon "shifting" the nonterminal *)
  let rightSiblingState:tStateId =
    (decodeGoto (getGotoEntry glr.tables leftSibling.state lhsIndex) lhsIndex) in
    
  if (traceParse) then (
    (Printf.printf "state %d, shift nonterm %d, to state %d\n"
                   leftSibling.state
                   lhsIndex
                   rightSiblingState);
    (flush stdout);
  );
  
  (* is there already an active parser with this state? *)
  match (findTopmostParser glr rightSiblingState) with
  | Some(rightSibling) -> (     (* rightSibling:tStackNode *)
      match (getLinkTo rightSibling leftSibling) with
      | Some(sibLink) -> (      (* sibLink:tSiblingLink *)
          (* we already have a sibling link, don't need a new one *)

          (* +--------------------------------------------------+
           * | it is here that we are bringing the tops of two  |
           * | alternative parses together (TREEBUILD)          |
           * +--------------------------------------------------+
           *)

          (* dead tree optimization *)
          if (not (canMakeProgress glr rightSibling)) then (
            if (traceParse) then (
              (Printf.printf "avoided a merge by noticing the state was dead\n");
              (flush stdout);
            );
            (deallocateSemanticValue (getNodeSymbol rightSibling) glr.userAct sval);
          )
          else (
            (* call user's merge code *)
            sibLink.sval <-
              (glr.userAct.mergeAlternativeParses lhsIndex sibLink.sval sval);
          );

          (* ok, done *)
          None

          (* didn't add a link, no potential for new paths *)
        )

      | None -> (
          (* no suitable sibling link already, so add it *)
          let sibLink:tSiblingLink = (addSiblingLink rightSibling leftSibling sval) in

          (* recompute depths; TODO: do the topological sort thing *)
          if (rightSibling.referenceCount > 1) then (
            let changes: int ref = ref 1 in
            let iters: int ref = ref 0 in
            while (!changes > 0) do
              changes := 0;
              (glr.topmostParsers#iter
                (fun parsr -> (
                  let newDepth:int = (computeDeterminDepth parsr) in
                  if (newDepth <> parsr.determinDepth) then (
                    (incr changes);
                    parsr.determinDepth <- newDepth;
                  );
                )));
              (incr iters);
              (assert (!iters < 1000));     (* protect against infinite loop *)
              (* computeDepthIters++; *)
            done;
          );

          (* inform caller of new link *)
          (Some sibLink)
        )
    )

  | None -> (
      (* not already active parser in this state, so make one *)
      let rightSibling:tStackNode = (makeStackNode glr rightSiblingState) in
      
      (* add link *)
      ignore (addSiblingLink rightSibling leftSibling sval);
      
      (* extend frontier *)
      (addTopmostParser glr rightSibling);
      
      (* enqueue this new parser's reductions *)
      let action:tActionEntry =
        (getActionEntry glr.tables rightSibling.state (curToken glr)) in
      ignore (rwlEnqueueReductions glr rightSibling action None(*siblink*));
          
      (* caller doesn't need to do anything more *)
      None
    )
end

  
(* returns # of actions *)
and rwlEnqueueReductions (glr: tGLR) (parsr: tStackNode) (action: tActionEntry)
                         (mustUseLink: tSiblingLink option) : int =
begin
  (assert (checkLocalInvariants parsr));

  if (isShiftAction glr.tables action) then (
    (* do nothing, only looking for reductions *)
    1
  )
  else if (isReduceAction (*tables*) action) then (
    let prodIndex = (decodeReduce (*tables*) action parsr.state) in

    (* production info *)
    let rhsLen:int = (getProdInfo_rhsLen glr.tables prodIndex) in
    (assert (rhsLen >= 0));       (* paranoia *)

    (* make a prototype path; used to control recursion *)
    let proto:tPath =
      (newPath glr.pathQueue parsr.state prodIndex rhsLen) in

    (* kick off the recursion *)
    (rwlRecursiveEnqueue glr proto rhsLen parsr mustUseLink);

    (* deallocate prototype *)
    (deletePath glr.pathQueue proto);

    1
  )
  else if (isErrorAction (*tables*) action) then (
    (* parser just dies *)
    0
  )
  else (
    (* ambiguous; check for reductions in list of actions *)
    let firstEntry:int = (decodeAmbigAction glr.tables action parsr.state) in
    let numEntries:int = glr.tables.ambigTable.(firstEntry) in
    for i = 1 to numEntries do
      (* ignore return value because I know it will be 1 *)
      ignore (rwlEnqueueReductions glr parsr glr.tables.ambigTable.(firstEntry+i) mustUseLink);
    done;

    numEntries
  )
end


(* same argument meanings as for 'rwlRecursiveEnqueue' *)
and rwlCollectPathLink
  (glr: tGLR)
  (proto: tPath)
  (popsRemaining: int)
  (currentNode: tStackNode)
  (mustUseLink: tSiblingLink option)
  (linkToAdd: tSiblingLink)         (* extra *)
  : unit =
begin
  (!(proto.sibLinks)).(popsRemaining) <- linkToAdd;
  (!(proto.symbols)).(popsRemaining) <- (getNodeSymbol currentNode);

  if (someEquals mustUseLink linkToAdd) then (
    (* consume must-use link *)
    (rwlRecursiveEnqueue glr proto popsRemaining linkToAdd.sib
                         None(*mustUse*));
  )
  else (
    (rwlRecursiveEnqueue glr proto popsRemaining linkToAdd.sib
                         mustUseLink);
  );
end

(* recursive depth-first enumeration of paths *)
and rwlRecursiveEnqueue
  (glr: tGLR)
  (proto: tPath)                      (* prototype path, with path so far *)
  (popsRemaining: int)                (* # of links yet to traverse to find a full path *)
  (currentNode: tStackNode)           (* node we're at in the path *)
  (mustUseLink: tSiblingLink option)  (* link the path must use (if not None) *)
  : unit =
begin
  if (popsRemaining = 0) then (
    (* found path *)
    
    (* must have used the link *)
    if (isSome mustUseLink) then (
      (* do nothing *)
    )
    else (
      (* copy the prototype path, it's the one we want *)
      (insertPathCopy glr.pathQueue proto currentNode)
    );
  )

  else (
    (* explore currentNode's siblings *)
    (rwlCollectPathLink glr proto (popsRemaining-1) currentNode mustUseLink
                        currentNode.firstSib);

    (List.iter
      (fun sibling -> (
        (rwlCollectPathLink glr proto (popsRemaining-1) currentNode mustUseLink
                            sibling)
      ))
      currentNode.leftSiblings
    );
  );
end


and rwlShiftTerminals (glr: tGLR) : unit =
begin
  glr.globalNodeColumn <- glr.globalNodeColumn + 1;
  
  (* move all parsers from 'topmostParsers' to 'prevTopmost' *)
  (assert (glr.prevTopmost#isEmpty()));
  (glr.prevTopmost#swapWith glr.topmostParsers);
  (assert (glr.topmostParsers#isEmpty()));

  (* grab current token since we'll need it and the access 
   * isn't all that fast here in ML *)
  let token:int = (curToken glr) in

  (* for token multi-yield.. *)
  let prev: tSiblingLink option ref = ref None in

  while (glr.prevTopmost#isNotEmpty()) do
    (* take the node from 'prevTopmost'; the refcount transfers
     * from 'prevTopmost' to (local variable) 'leftSibling' *)
    let leftSibling:tStackNode = (glr.prevTopmost#pop()) in
    (assert (leftSibling.referenceCount >= 1));   (* for the local *)

    (* can this parser shift? *)
    let action:tActionEntry =
      (getActionEntry glr.tables leftSibling.state token) in

    (* if we find a shift, this will be set to something valid *)
    let newState: tStateId ref = ref cSTATE_INVALID in

    (* consult action table, looking for shifts *)
    if (isShiftAction glr.tables action) then (
      (* unambiguous shift *)
      newState := (decodeShift (*tables*) action token);
    )
    else if ((isReduceAction (*tables*) action) ||
             (isErrorAction (*tables*) action)) then (
      (* unambiguous reduction or error *)
    )
    else (
      (* nondeterministic *)
      let firstEntry:int = (decodeAmbigAction glr.tables action leftSibling.state) in
      let numEntries:int = glr.tables.ambigTable.(firstEntry) in

      for i=1 to numEntries do
        let action:tActionEntry = glr.tables.ambigTable.(firstEntry+i) in
        if (isShiftAction glr.tables action) then (
          (* a shift was among the conflicted actions *)
          newState := (decodeShift (*tables*) action token);

          (* would like to break out, but I can't, so just eat the wasted time.. *)
        );
      done;
    );

    if (!newState <> cSTATE_INVALID) then (
      (* found a shift *)

      glr.nondetShift <- glr.nondetShift + 1;

      if (traceParse) then (
        (Printf.printf "state %d, shift token %s, to state %d\n"
                       leftSibling.state
                       ((getSome glr.lexerPtr)#tokenDesc())
                       !newState);
        (flush stdout);
      );

      (* already a parser in this state? *)
      let rightSibling:tStackNode =
        match (findTopmostParser glr !newState) with
        | Some(rs) -> rs     (* use existing *)
        | None -> (
            (* must make a new stack node *)
            let rs:tStackNode = (makeStackNode glr !newState) in

            (* add it to active parsers *)
            (addTopmostParser glr rs);

            rs               (* use new *)
          )
      in

      (* semantic value for this token *)
      let sval:tSemanticValue =
        match !prev with
        | None -> ((getSome glr.lexerPtr)#getSval())    (* usual case *)

        | Some(prev) -> (
            (* the 'sval' we just grabbed has already been claimed by
             * 'prev.sval'; get a fresh one by duplicating the latter *)
            (glr.userAct.duplicateTerminalValue token prev.sval)
          )
      in

      (* add sibling link now *)
      prev := (Some (addSiblingLink rightSibling leftSibling sval));

      (* see comments in glr.cc for explanation *)
      (assert (rightSibling.referenceCount = 1));
    );
    
    (* pending decrement of leftSibling, which is about to go out of scope *)
    (decRefCt leftSibling);
  done;
end


(* EOF *)
