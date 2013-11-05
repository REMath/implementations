(* ptreenode.ml *)
(* parse tree node for use with ptreeact module *)
(* based on elkhound/ptreenode *)


open Smutil          (* getSome, etc. *)
open Arraystack      (* tArrayStack *)


(* for storing parse tree counts *)
type tTreeCount = float


(* a node in a parse tree *)
(* (I tried making this a class, but OCaml kicked my ass instead) *)
type tPTreeNode = {            
  (* symbol at this node *)
  symbol: string;          
  
  (* list of ambiguous alternatives to this node *)
  mutable merged: tPTreeNode option;

  (* array of children *)
  mutable children: tPTreeNode option array;

  (* number of parse trees this node is root of *)
  mutable count: tTreeCount;
}


let makePTreeNode (sym:string) : tPTreeNode =
begin
  {
    symbol = sym;
    merged = None;
    children = (Array.make 0 None);
    count = 0.0;
  }
end


let indent (out:out_channel) (n:int) : unit =
begin
  for i=0 to n-1 do
    (output_char out ' ');
  done;
end


(* this was polymorphic at one point, then OCaml said "thou shalt not" *)
let childFold (children: tPTreeNode option array) (init: int)
              (f: tPTreeNode -> int -> int) : int =
begin
  (Array.fold_right (fun co v -> (f (getSome co) v)) children init);
end

let childIter (children: tPTreeNode option array)
              (f: tPTreeNode -> unit) : unit =
begin
  (Array.iter (fun co -> (f (getSome co))) children);
end

let rec mergedFold (merged: tPTreeNode option) (init: int)
               (f: tPTreeNode -> int -> int) : int =
begin
  match merged with
  | None -> init
  | Some(n) -> (mergedFold n.merged (f n init) f)
end

let mergedIter (self:tPTreeNode) (f: tPTreeNode -> unit) : unit =
begin
  ignore (mergedFold (Some self) 0 (fun n (x:int) -> ((f n); x)))
end


(* just the length of the 'merged' list *)
let countMergedList (self:tPTreeNode) : int =
begin
  (mergedFold (Some self) 0 (fun _ v -> (v+1)))
end


(* count trees rooted here *)
let rec countTrees (self:tPTreeNode) : tTreeCount =
begin
  (* memoize *)
  if (self.count > 0.0) then (
    self.count
  )

  else (
    (* sum over alternatives, product over children *)
    (* (look at me, functional programming boy) *)
    (* never mind, I am obviously not functional programming boy *)

    (* sum over children here *)
    let ct: float ref = ref 1.0 in
    (childIter self.children (fun c -> (
      ct := !ct *. (countTrees c);
    )));

    (* alternatives? *)
    if (isSome self.merged) then (
      (* add them too, recursively *)
      ct := !ct +. (countTrees (getSome self.merged));
    );

    !ct
  )
end


(* set number of children, i.e. size of 'children' array *)
let setNumChildren (self:tPTreeNode) (i:int) : unit =
begin
  self.children <- (Array.make i None)
end

(* set a particular child *)
let setChild (self:tPTreeNode) (i:int) (c:tPTreeNode) : unit =
begin
  self.children.(i) <- (Some c);
end

(* add an ambiguous alternative *)
let addAlternative (self:tPTreeNode) (alt:tPTreeNode) : unit =
begin
  (* insert as 2nd element *)
  alt.merged <- self.merged;
  self.merged <- (Some alt);
end


(* ----------- printTree (a little biotch) ------------ *)
let printTree (self:tPTreeNode) (out:out_channel) (expand:bool) : unit =
begin
  (* indentation per level *)
  let cINDENT_INC:int = 2 in

  (* for detecting cyclicity *)      
  let dummyNode: tPTreeNode = ((Obj.magic []) : tPTreeNode) in
  let path: tPTreeNode tArrayStack = (new tArrayStack dummyNode) in
  
  (* turn this on to detect cyclicity; there is a performance penalty *)
  let checkForCycles: bool = true in

  (* methods cannot be recursive!  what's up with that?! *)
  let rec innerPrint (self:tPTreeNode) (indentationOrig:int) : unit =
  begin
    let indentation: int ref = ref indentationOrig in
    let alts: int ref = ref 1 in
    let lhs: string ref = ref "" in
    let symbol: string = self.symbol in
    let merged: tPTreeNode option = self.merged in
      
    let cyclicSkip: bool = (
      if (checkForCycles) then (
        (* does 'self' appear in 'path'? *)
        let idx:int = (path#findIndex (fun p -> p == self)) in
        if (idx >= 0) then (
          (* yes; print a cyclicity reference *)
          (indent out !indentation);
          (Printf.fprintf out "[CYCLIC: refers to %d hops up]\n"
                              ((path#length()) - idx + 1));
          true   (* return *)
        )
        else (
          (* no; add myself to the path *)
          (path#push self);
          false
        )
      )
      else (
        false
      )
    ) in

    if (not cyclicSkip) then (
      if (isSome merged) then (
        (* this is an ambiguity node *)
        alts := (countMergedList self);

        (* get nonterm from first; should all be same *)
        try
          (* extract first word *)
          let firstSpace:int = (String.index symbol ' ') in
          lhs := (String.sub symbol 0 firstSpace);
        with
        | Not_found -> (
            lhs := symbol    (* no spaces, use whole thing *)
          );

        indentation := !indentation + cINDENT_INC;
      );

      (* iterate over interpretations *)
      let ct: int ref = ref 1 in
      (mergedIter self (fun (node:tPTreeNode) -> (
        if (!alts > 1) then (
          (indent out (!indentation - cINDENT_INC));
          (Printf.fprintf out "------------- ambiguous %s: %d of %d ------------\n"
                              !lhs !ct !alts);
          (flush out);
        );

        (indent out !indentation);

        let children: tPTreeNode option array = node.children in
        let numChildren:int = (Array.length children) in

        (Printf.fprintf out "%s" node.symbol);

        if (expand) then (
          (* symbol is just LHS, write out RHS names after "->" *)
          if (numChildren > 0) then (
            (Printf.fprintf out " ->");
            (childIter node.children (fun c ->
              (Printf.fprintf out " %s" c.symbol)
            ));
          );
        );

        (Printf.fprintf out "\n");
        (flush out);

        (* iterate over children and print them *)
        (childIter node.children (fun c ->
          (innerPrint c (!indentation + cINDENT_INC))
        ));

        (incr ct);
      )));

      if (isSome merged) then (
        (* close up ambiguity display *)
        indentation := !indentation - cINDENT_INC;
        (indent out !indentation);
        (Printf.fprintf out "----------- end of ambiguous %s -----------\n"
                            !lhs);
        (flush out);
      );
      
      if (checkForCycles) then (
        (* remove myself from the path *)
        (ignore (path#pop ()));
      );
    );
  end in

  (innerPrint self 0(*indentation*))
end


(* EOF *)
