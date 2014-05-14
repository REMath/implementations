open Varencoding ;;
open Basics ;;
open Cfg ;;

type treenode = NNode of int * string * int
              | TNode of string * int

module TreeNode = 
struct
  type t = treenode
 
  let compare = compare
end ;;

module TreeNodeSet = Set.Make(TreeNode) ;;

let makeNode = 
  function NNode(i,v,j) -> "N" ^ v ^ string_of_int i ^ string_of_int j
         | TNode(t,i) -> "T" ^ t ^ string_of_int i

let dottyParseTreeHeader =
  "digraph G {\n"

let dottyParseTreeFooter =
  "}\n"

let dottyWord alphabet k =
  let s = ref "" in
  for i = 0 to (k-1) do
    List.iter
      (fun t -> if 1 = getValue(T(t,i))
                then let label = "(" ^ t ^ "," ^ string_of_int i ^ ")" in
                     let n = TNode(t,i) in
                     s := !s ^ makeNode n ^ " [shape=\"box\",label=\"" ^ label ^ "\"];\n")
      alphabet
  done;
  !s


let dottyParseTree cfg k =
  let s = ref "" in
  let nodes = ref TreeNodeSet.empty in

  for i = 0 to (k-1) do
    for j = i to (k-1) do
      let ns = List.filter
                 (fun n -> 1 = getValue(N(cfg,n,i,j)))
                 cfg.nonterminals
      in
      List.iter
        (fun n -> let shape = if StringSet.mem n cfg.ambnonterminals 
                              then "\"tripleoctagon\"" 
                              else "\"octagon\""
                  in
                  let label = "[" ^ string_of_int i ^ "," ^ n ^ "," ^ string_of_int j ^ "]" in
                  let n = NNode(i,n,j) in
                  s := !s ^ makeNode n ^ " [shape=" ^ shape ^ ",label=\"" ^ label ^ "\"];\n";
                  nodes := TreeNodeSet.add n !nodes)
        ns  
    done;
    List.iter
      (fun t -> if 1 = getValue(T(t,i))
                then nodes := TreeNodeSet.add (TNode(t,i)) !nodes)
      cfg.alphabet
  done;

  TreeNodeSet.iter
     (function TNode(_,_) -> ()
             | NNode(i,n,j) -> 
                  let rules = List.assoc n cfg.cfg in
                  List.iter 
                    (function [] -> ()
		            | [Terminal t] ->
                                 if i=j && TreeNodeSet.mem (TNode(t,i)) !nodes
                                 then s := !s ^ makeNode (NNode(i,n,j)) ^ " -> " ^ makeNode (TNode(t,i)) ^ 
                                           "[label=\"" ^ n ^ "->" ^ t ^ "\"];\n";
		  	    | [Nonterminal b] ->
                                 if TreeNodeSet.mem (NNode(i,b,j)) !nodes
                                 then s := !s ^ makeNode (NNode(i,n,j)) ^ " -> " ^ makeNode (NNode(i,b,j)) ^ 
                                           "[label=\"" ^ n ^ "->" ^ b ^ "\"];\n";
		  	    | [Nonterminal b; Nonterminal c] ->
                                 if TreeNodeSet.mem (NNode(i,b,j)) !nodes
                                 then (if StringIntSet.mem (c,2) cfg.ambnullable
                                       then s := !s ^ makeNode (NNode(i,n,j)) ^ " -> " ^ makeNode (NNode(i,b,j)) ^ 
                                                 "[shape=\"crow\",label=\"" ^ n ^ "->" ^ b ^ c ^ "\"];\n"
                                       else if StringIntSet.mem (c,1) cfg.ambnullable
                                            then s := !s ^ makeNode (NNode(i,n,j)) ^ " -> " ^ makeNode (NNode(i,b,j)) ^ 
                                                 "[shape=\"lcrow\",label=\"" ^ n ^ "->" ^ b ^ c ^ "\"];\n");
                                 if TreeNodeSet.mem (NNode(i,b,j)) !nodes
                                 then (if StringIntSet.mem (b,2) cfg.ambnullable
                                       then s := !s ^ makeNode (NNode(i,n,j)) ^ " -> " ^ makeNode (NNode(i,c,j)) ^ 
                                                 "[shape=\"crow\",label=\"" ^ n ^ "->" ^ b ^ c ^ "\"];\n"
                                       else if StringIntSet.mem (b,1) cfg.ambnullable
                                            then s := !s ^ makeNode (NNode(i,n,j)) ^ " -> " ^ makeNode (NNode(i,c,j)) ^ 
                                                 "[shape=\"rcrow\",label=\"" ^ n ^ "->" ^ b ^ c ^ "\"];\n");
                                 for h = i to j-1 do
                                   if TreeNodeSet.mem (NNode(i,b,h)) !nodes && TreeNodeSet.mem (NNode(h+1,c,j)) !nodes
                                   then (s := !s ^ makeNode (NNode(i,n,j)) ^ " -> " ^ makeNode (NNode(i,b,h)) ^ 
                                              "[label=\"" ^ n ^ "->" ^ b ^ c ^ "\"];\n";
                                         s := !s ^ makeNode (NNode(i,n,j)) ^ " -> " ^ makeNode (NNode(h+1,c,j)) ^ 
                                              "[label=\"" ^ n ^ "->" ^ b ^ c ^ "\"];\n")
                                 done)
                    rules)
     !nodes;

  !s
