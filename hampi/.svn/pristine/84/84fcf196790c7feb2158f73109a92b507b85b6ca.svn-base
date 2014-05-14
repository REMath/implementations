open Basics ;;

type symbol = Nonterminal of string
            | Terminal of string

type pureCFG = (string * (symbol list list)) list

type alphabet = string list

type fullCFG = { cfg: pureCFG;
                 origcfg: pureCFG;
                 alphabet: string list;
                 nonterminals: string list;
                 start: string;
(*                 termprods: (string * (string list)) list; *)
                 nullable: StringSet.t;
                 ambnullable: StringIntSet.t;
                 ambnonterminals: StringSet.t;
                 ambproductions: StringStringSet.t (*;
                 closure: StringSet.t StringMap.t;
                 ambclosure: StringIntSet.t StringMap.t *)
               }

let showPureCFG = 
  List.fold_left
    (fun s -> fun (nonterminal,rules) -> 
       s ^ nonterminal ^ " -> " ^ 
       (String.concat " | " (List.map (fun rule -> String.concat " " (List.map (function Terminal s -> "\"" ^ s ^ "\""
                                                                                       | Nonterminal s -> s) 
                                                                               rule)) 
                                      rules)) ^ " ;\n")
    ""

let alphabet cfg = 
  StringSet.fold 
    (fun s -> fun l -> s::l) 
    (List.fold_left (fun s -> fun (_,rules) -> 
                       StringSet.union s (List.fold_left (fun s -> fun r -> StringSet.union s r) 
                                                        StringSet.empty
                                                        (List.map (function Terminal s -> StringSet.singleton s
		                                                          | Nonterminal _ -> StringSet.empty)
                                                                  (List.concat rules))))
                    StringSet.empty
                    cfg)
    []

let nonterminals = List.map fst   

let to2nf cfg =
  let ncounter = ref 0 in
  let acounter = ref 0 in
  let newNvar _ = let s = "AuxN" ^ string_of_int !ncounter in
                  incr ncounter; s
  in
  let newAvar _ = let s = "AuxA" ^ string_of_int !acounter in
                  incr acounter; s
  in

  let newAvars = List.map (fun a -> (a,newAvar ())) (alphabet cfg) in
  let getAvar a = List.assoc a newAvars in
  let replaced = ref StringSet.empty in

  let cfg = (List.map 
               (fun (n,rules) -> 
                  let rules = List.map 
                                (fun rule -> if List.length rule > 1 
                                             then List.map 
                                                    (function Terminal s -> 
                                                                replaced := StringSet.add s !replaced;
                                                                Nonterminal (getAvar s)
                                                            | t -> t)
                                                     rule
                                             else rule)
                                 rules
                  in 
                  (n,rules))
                cfg) 
  in
  let cfg = cfg @ (StringSet.fold (fun t -> fun l -> ((getAvar t), [[Terminal t]])::l) !replaced []) 
  in

  let rec divider racc newracc = 
    function []               -> (racc,newracc)
           | ([]::rs)         -> divider ([]::racc) newracc rs
           | ([x]::rs)        -> divider ([x]::racc) newracc rs
           | ([x;y]::rs)      -> divider ([x;y]::racc) newracc rs
	   | ((x::y::xs)::rs) -> let n = newNvar () in
                                 divider racc ((n,[[x;y]])::newracc) (((Nonterminal n)::xs)::rs)
  in

  let rec transformer racc newracc = 
    function []          -> racc @ newracc
           | (n,rs)::rls -> let (rs,nrs) = divider [] newracc (List.rev rs) in
                            transformer ((n,rs)::racc) nrs rls
  in

  transformer [] [] (List.rev cfg)
  

let nullableSymbols cfg =
  let s = ref (List.fold_left (fun s -> fun n -> StringSet.add n s)
                              StringSet.empty
                              (List.map fst 
                                        (List.filter (fun (n,rs) -> List.exists (function [] -> true | _ -> false) rs) 
                                                     cfg)))
  in

  let s' = ref StringSet.empty in

  while not (StringSet.equal !s !s') do
    s' := !s;

    s := List.fold_left 
           (fun s -> fun n -> StringSet.add n s)
           !s
           (List.map 
              fst
              (List.filter (fun (n,rs) -> List.exists (fun r -> match r with
                                                                      [Nonterminal b]   -> StringSet.mem b !s
                                                                    | [Nonterminal b;Nonterminal c] -> StringSet.mem b !s && StringSet.mem c !s
                                                                    | _     -> false)
                                          rs)
                           cfg))
  done;

  !s


let showUnitProdClosure m =
  StringMap.fold 
    (fun n -> fun bs -> fun s -> 
       n ^ " ==>* {" ^ String.concat "," (StringSet.fold (fun x -> fun l -> x::l) bs []) ^ "}\n" ^ s) 
    m
    ""

let showAmbUnitProdClosure m =
  StringMap.fold 
    (fun n -> fun bs -> fun s -> 
       n ^ " ==>* {" ^ String.concat "," (StringIntSet.fold (fun (x,d) -> fun l -> ("(" ^ x ^ "," ^ string_of_int d ^ ")")::l) bs []) ^ "}\n" ^ s) 
    m
    ""

let unitProductionClosure cfg =
  let nullable = nullableSymbols cfg in

  let m = ref (List.fold_left 
                 (fun m -> fun (n,ns) -> StringMap.add n ns m)
                 StringMap.empty
                 (List.map 
                    (fun (n,rs) -> 
                       (n, List.fold_left 
                             (fun s -> fun b -> StringSet.add b s)
                             StringSet.empty
                             (n::(List.concat 
                                (List.map 
                                   (function [Nonterminal b]                -> [b]
	   	                           | [Nonterminal b; Nonterminal c] -> let nc = if StringSet.mem b nullable then [c] else [] in
                                                                               if StringSet.mem c nullable then b::nc else nc
	                                   | _                              -> [])
                                   rs)))))
                    cfg))
  in

  let m' = ref StringMap.empty in

  while not (StringMap.equal StringSet.equal !m !m') do
    m' := !m;

    m := StringMap.map
           (fun bs -> StringSet.fold
                        (fun b -> fun s -> StringSet.union s (StringMap.find b !m))
                        bs
                        bs)
           !m
  done;

  !m



let terminalProductions cfg =
  List.map 
    (fun (n,rules) ->
       (n, List.map 
             (function [Terminal a] -> a | _ -> failwith "Should only be applied to unit productions!")
             (List.filter (function [Terminal a] -> true | _ -> false) rules)))
    cfg



let stringIntSetAdd b s = 
  match b with 
       (b,i) -> match StringIntSet.elements (StringIntSet.filter (fun (c,_) -> b=c) s) with
                      []       -> StringIntSet.add (b,i) s
                    | (c,j)::_ -> StringIntSet.add (b,2) (StringIntSet.remove (c,j) s)

let stringIntSetUnion s s' =
  List.fold_left (fun s -> fun x -> stringIntSetAdd x s) s (StringIntSet.elements s')



let nullableSymbolsAmb cfg =
  let s = ref (List.fold_left (fun s -> fun n -> stringIntSetAdd (n,1) s)
                              StringIntSet.empty
                              (List.map fst 
                                        (List.filter (fun (n,rs) -> List.exists (function [] -> true | _ -> false) rs) 
                                                     cfg)))
  in
  let m = ref !s in
  let s' = ref StringIntSet.empty in

  while not (StringIntSet.equal !s !s') do
    s' := !s;

    m := List.fold_left 
           (fun s -> fun x -> stringIntSetAdd x s)
           StringIntSet.empty
           (List.concat
             (List.map   
               (fun (n,rs) ->
                 List.concat 
                   (List.map 
                      (function [] -> []
                              | [Nonterminal b]   -> if StringIntSet.mem (b,1) !m
                                                     then [(n,1)]
                                                     else if StringIntSet.mem (b,2) !m
                                                          then [(n,2)]
                                                          else []
                              | [Nonterminal b;Nonterminal c] -> 
                                                     if StringIntSet.mem (b,1) !m
                                                     then (if StringIntSet.mem (c,1) !m 
                                                           then [(n,1)]
                                                           else if StringIntSet.mem (c,2) !m
                                                                then [(n,2)]
                                                                else [])
                                                     else if StringIntSet.mem (b,2) !m
                                                          then (if StringIntSet.mem (c,1) !m || 
                                                                   StringIntSet.mem (c,2) !m 
                                                                then [(n,2)]
                                                                else [])
                                                          else [] 
                              | _     -> [])
                      rs))
               cfg));
    s := stringIntSetUnion !s !m
  done;

  !s


let stringMapUnion m m' =
  StringMap.fold 
    (fun k -> fun s -> fun m -> let s' = try
                                           StringMap.find k m 
                                         with Not_found -> StringIntSet.empty
                                in
                                StringMap.add k (stringIntSetUnion s' s) m)
    m'
    m

let makeAmbClosure cfg = 
  let nullable = nullableSymbolsAmb cfg in

  let m = ref (List.fold_left 
                 (fun m -> fun (n,ns) -> StringMap.add n ns m)
                 StringMap.empty
                 (List.map 
                    (fun (n,rs) -> 
                       (n, List.fold_left 
                             (fun s -> fun b -> stringIntSetAdd b s)
                             StringIntSet.empty
                             (List.concat 
                                (List.map 
                                   (function [Nonterminal b]                -> [(b,1)]
	   	                           | [Nonterminal b; Nonterminal c] -> 
                                                let nc = if StringIntSet.mem (b,1) nullable 
                                                         then [(c,1)] 
                                                         else if StringIntSet.mem (b,2) nullable 
                                                              then [(c,2)] 
                                                              else [] 
                                                in
                                                if StringIntSet.mem (c,1) nullable 
                                                then (b,1)::nc 
                                                else if StringIntSet.mem (c,2) nullable
                                                     then (b,2)::nc
                                                     else nc
	                                   | _                              -> [])
                                   rs))))
                    cfg))
  in
  let id = List.fold_left
             (fun m -> fun n -> StringMap.add n (StringIntSet.singleton (n,1)) m)
             StringMap.empty
             (List.map fst cfg)
  in 
  let s = ref (stringMapUnion id !m) in
  let s' = ref StringMap.empty in
  let m' = ref !m in

  while not (StringMap.equal StringIntSet.equal !s !s') do
(*    message 3 (fun _ -> "Current m:\n" ^ showAmbUnitProdClosure !m);
    message 3 (fun _ -> "Current s:\n" ^ showAmbUnitProdClosure !s); *)

    s' := !s;
    
    m' := StringMap.map
           (fun bs -> StringIntSet.fold
                        (fun (b,d) -> fun s -> stringIntSetUnion 
                                                 s 
                                                 (try
                                                    StringIntSet.fold
                                                      (fun (c,d') -> fun s' -> StringIntSet.add (c,min 2 (d*d')) s')
                                                      (StringMap.find b !m')
                                                      StringIntSet.empty
                                                 with Not_found -> failwith ("Can't find nonterminal " ^ b ^ "\n")))
                        bs
                        StringIntSet.empty)
           !m;
    s := stringMapUnion !s !m'
  done;

  !s



let equivalence_classes cfg =
  let nulls = nullableSymbols cfg in
  message 3 (fun _ -> "    Nullable symbols: {" ^ 
                      String.concat "," (StringSet.fold (fun b -> fun l -> b::l) nulls []) ^ "}\n");
  let l = List.length cfg in
  let dfsnum = Hashtbl.create l in
  let dfsnam = Array.make l "" in
(*  let index = Array.make l (-1) in *)

  let n = ref 0 in
  let visited = ref (StringSet.empty) in

  let rec dfs v = 
    message 3 (fun _ -> "      Now visiting node " ^ v ^ "\n");
    if not (StringSet.mem v !visited) 
    then (visited := StringSet.add v !visited;
          let nexts = ref [] in
          List.iter
            (function [Nonterminal b] -> nexts := b :: !nexts
		    | [Nonterminal b; Nonterminal c] ->
                         if StringSet.mem b nulls then nexts := c :: !nexts;  
                         if StringSet.mem c nulls then nexts := b :: !nexts
		    | _ -> ())  
            (List.assoc v cfg);
          List.iter (fun w -> dfs w) !nexts;
          Hashtbl.add dfsnum v !n;
          dfsnam.(!n) <- v;
          message 3 (fun _ -> "    Node " ^ v ^ " has DFS finishing time " ^ string_of_int !n ^ "\n");
          incr n)
  in

  message 3 (fun _ -> "    Forwards DFS through CFG\n");
  List.iter
    (fun (v,_) -> if not (StringSet.mem v !visited) then dfs v)
    cfg;

  decr n;

  message 3 (fun _ -> "    Computing transposed graph\n");
  let tcfg = ref [] in
  List.iter
    (fun (n,rules) -> List.iter
                        (function [Nonterminal b] -> tcfg := (b,StringSet.singleton n) :: !tcfg
			        | [Nonterminal b; Nonterminal c] -> 
                                     if StringSet.mem b nulls then tcfg := (c,StringSet.singleton n) :: !tcfg;
                                     if StringSet.mem c nulls then tcfg := (b,StringSet.singleton n) :: !tcfg
				| _ -> ())
                        rules)
    cfg;
  message 3 (fun _ -> "    Sorting\n");
  tcfg := List.sort (fun (b,_) -> fun (c,_) -> compare b c) !tcfg;
  let rec retract = 
    function []                   -> []
           | [(b,bs)]             -> [(b, StringSet.elements bs)]
	   | ((b,bs)::(c,cs)::xs) -> if b <> c 
                                     then (b,StringSet.elements bs) :: (retract ((c,cs)::xs))
                                     else retract ((b,StringSet.union bs cs)::xs)
  in
  message 3 (fun _ -> "    Retracting\n");
  let tcfg = List.map 
               (fun (n,bs) -> (n, List.sort 
                                    (fun b -> fun c -> compare (Hashtbl.find dfsnum c) (Hashtbl.find dfsnum b))
                                    bs))
               (retract !tcfg)
  in

  visited := StringSet.empty;
  let scc = ref [] in
  let sccs = ref [] in

  let rec dfs v = 
    message 3 (fun _ -> "      Now visiting node " ^ v ^ "\n");
    if not (StringSet.mem v !visited) 
    then (visited := StringSet.add v !visited;
          message 3 (fun _ -> "        Adding node " ^ v ^ "\n");
          scc := v :: !scc;
          let nexts = try 
                        List.assoc v tcfg
                      with _ -> []
          in
          List.iter (fun w -> dfs w) nexts)
  in

  message 3 (fun _ -> "    Backwards DFS through CFG\n");
  while !n >= 0 do
    let v = dfsnam.(!n) in

    message 3 (fun _ -> "      Starting new SCC with node with DFS finishing time " ^ string_of_int !n ^ "\n");
    scc := [];
    dfs v;
    sccs := !scc :: !sccs;

    while !n >= 0 && StringSet.mem (dfsnam.(!n)) !visited do
      decr n
    done
  done;
  !sccs



let tidy cfg =
  let reachable = ref StringSet.empty in
  
  let rec reach v = 
    if not (StringSet.mem v !reachable) 
    then (reachable := StringSet.add v !reachable;
          let rules = List.assoc v cfg in
          List.iter 
            (fun rule -> List.iter
                           (function Nonterminal b -> reach b
			           | _             -> ())
                           rule)
            rules)
  in
  reach (fst (List.hd cfg));

  let cfg = List.filter
              (fun (n,_) -> StringSet.mem n !reachable)
              cfg
  in

  let productive = ref (List.fold_left 
                          (fun s -> fun n -> StringSet.add n s) 
                          StringSet.empty 
                          ((List.map 
                              fst 
                              (terminalProductions cfg)) 
                           @ 
                           (List.map 
                              fst
                              (List.filter
                                 (fun (n,rules) -> List.exists (function [] -> true | _ -> false) rules)
                                 cfg))))
  in
  let p' = ref StringSet.empty in

  while !productive <> !p' do
    p' := !productive;

    productive := List.fold_left
                    (fun s -> fun b -> StringSet.add b s)
                    !productive
                    (List.map 
                      fst
                      (List.filter
                        (fun (n,rules) ->
                          (List.exists 
                            (fun rule -> List.for_all 
                                           (function Terminal _ -> true
			                           | Nonterminal b -> StringSet.mem b !productive)
                                           rule)
                            rules))
                        cfg))
  done;
(*  let start = fst (List.hd cfg) in *)
  let cfg = List.filter
              (fun (n,_) -> StringSet.mem n !productive)
              cfg
  in
  cfg


exception No_initial_nonterminal

let makeFullCFG cfg' =
  message 3 (fun _ -> "  Pre-computing ...\n");
  let cfg = tidy cfg' in
  message 3 (fun _ -> "  CFG after removing of unreachable and unproductive nonterminals:\n" ^
                      showPureCFG cfg ^ "\n");
  let cfg = to2nf cfg' in
  message 3 (fun _ -> "  CFG after transformation into 2NF:\n" ^ showPureCFG cfg ^ "\n");
  let nullsamb = nullableSymbolsAmb cfg in
  let nulls = StringIntSet.fold (fun (b,_) -> fun s -> StringSet.add b s) nullsamb StringSet.empty in
  let sccs = equivalence_classes cfg in
  message 3 (fun _ -> "  Equivalence classes under <=*=> are:\n    " ^
                      String.concat 
                        "\n    " 
                        (List.map (fun scc -> "{" ^ String.concat "," scc ^ "}") sccs)
                      ^ "\n"); 
  let ambns = List.fold_left 
                (fun s -> fun b -> StringSet.add b s)
                StringSet.empty
                (List.concat 
                  (List.filter
                    (function [b] -> List.exists
                                       (fun rule -> match rule with
                                                          [Nonterminal c] -> b=c
			  	                        | [Nonterminal c; Nonterminal d] -> b=c && StringSet.mem d nulls ||
                                                                                            b=d && StringSet.mem c nulls
							| _ -> false)
                                       (List.assoc b cfg)
		            | _::_::_ -> true
			    | _ -> false)
                    sccs))
  in

  let rec replace_rules n cfg rules = 
    match cfg with
          []           -> []
        | ((b,rs)::xs) -> if n=b 
                          then (b,rules)::xs
                          else (b,rs)::(replace_rules n xs rules)
  in

  let rec replace_nonterminals cs b =
    function [] -> []
           | (n,rules)::xs -> (n, List.map 
                                    (fun rule -> List.map 
                                                   (function (Nonterminal c) -> if List.mem c cs 
                                                                                then Nonterminal b
                                                                                else Nonterminal c
					                   | x -> x)
                                                   rule)
                                  rules) :: (replace_nonterminals cs b xs)
  in

  let rec remove_nonterminals cs = 
    function [] -> []
           | (n,rules)::xs -> if List.mem n cs 
                              then remove_nonterminals cs xs
                              else (n,rules)::(remove_nonterminals cs xs)
  in

  let cfg = ref cfg in
  List.iter
    (fun scc -> match scc with
                      []  -> ()
                    | [b] -> ()
		    | bs  -> let ns = List.map fst !cfg in
                             let bs = List.sort 
                                        (fun b -> fun c -> compare (listindex b ns) (listindex c ns))
                                        bs
                             in
                             match bs with (b::bs) -> (
                             cfg := replace_rules 
                                          b 
                                          !cfg 
                                          (List.concat 
                                            (List.map 
                                              (fun c -> List.assoc c !cfg) 
                                              (b::bs)));
                                 cfg := remove_nonterminals bs !cfg;
                                 cfg := replace_nonterminals bs b !cfg)
			     | _ -> ())
    sccs;

  message 3 (fun _ -> "    Removing duplicate productions\n");
  cfg := List.map 
           (fun (n,rules) -> (n, remove_dups rules))
           !cfg;
  message 3 (fun _ -> showPureCFG !cfg);

  message 3 (fun _ -> "    Removing unproductive productions\n");
  cfg := List.map
           (fun (n,rules) -> (n, List.filter 
                                   (function [Nonterminal b] -> b <> n
				           | _ -> true)
                                   rules))
           !cfg;
  message 3 (fun _ -> showPureCFG !cfg);

  message 3 (fun _ -> "    Removing epsilon productions\n");
  cfg := List.map 
           (fun (n,rules) -> (n, List.filter 
                                   (function [] -> false | _ -> true)
                                   rules))
           !cfg;
  message 3 (fun _ -> showPureCFG !cfg);

  let cfg = !cfg in
  let ns = nonterminals cfg in
  { cfg = cfg;
    origcfg = cfg';
    alphabet = alphabet cfg;
    nonterminals = ns;
(*    termprods = terminalProductions cfg; *)
    start = (try
              List.hd ns
            with Failure _ -> raise No_initial_nonterminal);
    nullable = nulls;
    ambnullable = nullsamb;
    ambnonterminals = ambns;
    ambproductions = StringStringSet.empty
 (*;
    closure = unitProductionClosure cfg;
    ambclosure = (message 3 (fun _ -> "    Computing derivation relation between nonterminals with ambiguity information\n");
                  makeAmbClosure cfg) *) }


let size cfg = 
  let epsilons = ref 0 in
  let terminals = ref 0 in
  let units = ref 0 in
  let comps = ref 0 in
  let z = ref 0 in

  List.iter 
    (fun (n,rules) -> 
       List.iter (fun rule -> z := !z + (min 1 (List.length rule));
                              match rule with
                                    []              -> incr epsilons
	                          | [Terminal _]    -> incr terminals
	     		          | [Nonterminal _] -> incr units
			          | _::_            -> incr comps)
                 rules)
    cfg;
  let r = !epsilons + !terminals + !units + !comps in
  (!epsilons, !terminals, !units, !comps, r, !z, !z + (List.length cfg))


let number_of_productions cfg n =
  List.length (List.assoc n cfg.cfg)
