open Varencoding ;;
open Basics ;;
open Zchaff ;;
open Cfg ;;

type parsetree = Leaf of string
               | BinNode of string * parsetree * parsetree
               | Node of string * parsetree
	       | Derivation of string * parsetree
	       | AmbDerivation of string * parsetree

(*
 * TODO: put in "obtaining value for"-messages everywhere
 *)

let obtainValue v = 
  message 3 (fun _ -> "  Obtaining value for variable " ^ showVar v ^ ": ");
  let x = getValue v in
  message 3 (fun _ -> string_of_int x ^ "\n");
  x


let extractParseTree cfg k = 
  let rec extract v = 
    message 3 (fun _ -> "  Now processing variable " ^ showVar v ^ "\n");
    match v with
             N(_,n,i,j,1) -> 
                           let m = try
                                     List.find  
                                       (fun m -> 1 = obtainValue(N(cfg,m,i,j,0)))
                                       (StringSet.elements (try 
                                                              StringMap.find n cfg.closure
                                                            with Not_found -> failwith "Undefined nonterminal!"))
                                   with Not_found -> failwith "Parse tree is dangling!"
                           in
                           if n=m
                           then extract(N(cfg,m,i,j,0))
                           else Derivation(n, extract(N(cfg,m,i,j,0)))
	   | N(_,n,i,j,0) -> 
                           if i < j 
                           then let h = ref (-1) in
                                let (b,c) = match 
                                              (try
                                                List.find
                                                  (function [Nonterminal b; Nonterminal c] ->
                                                     h := -1;
                                                     h := (try
                                                            List.find
                                                              (fun h -> 1 = obtainValue(H(cfg,b,c,i,j,h)))
                                                              (range i (j-1))
                                                          with Not_found -> -1);
                                                     !h >= 0
						    | _ -> false)
                                                  (List.filter 
                                                     (function [Nonterminal _; Nonterminal _] -> true | _ -> false)
                                                     (List.assoc n cfg.cfg))
                                              with Not_found -> failwith "Dangling parse tree!")
                                            with [Nonterminal b; Nonterminal c] -> (b,c)
			                       | _ -> failwith "This error cannot occur."
                                in
                                BinNode(n, extract(N(cfg,b,i,!h,1)), extract(N(cfg,c,!h+1,j,1)))
                           else let t = try
                                          List.find 
                                            (fun t -> 1 = obtainValue(T(t,i)))
                                            (List.map
                                              (function [Terminal t] -> t | _ -> "")
                                              (List.filter
                                                (function [Terminal t] -> true | _ -> false)
                                                (List.assoc n cfg.cfg)))
                                        with Not_found -> failwith "Parse tree misses a leaf!"
                                in Node(n,Leaf(t))
	   | _ -> failwith "Cannot extract parse trees from other variables."
  in
  extract(N(cfg,cfg.start,0,k,1))



let extractTwoParseTrees cfg k =
  let rec extractOne v = 
    message 3 (fun _ -> "  Now processing variable " ^ showVar v ^ "\n");
    match v with
             A(_,n,i,j,1,1) -> 
                             let m = try
                                       List.find  
                                         (fun m -> 1 = obtainValue(A(cfg,m,i,j,0,1)))
                                         (StringSet.elements (try 
                                                                StringMap.find n cfg.closure
                                                              with Not_found -> failwith "Undefined nonterminal!"))
                                     with Not_found -> failwith ("Parse tree is dangling at " ^ 
                                                                 showVar(A(cfg,n,i,j,1,1)) ^ "\n")
                             in
                             if n=m
                             then extractOne(A(cfg,m,i,j,0,1))
                             else Derivation(n, extractOne(A(cfg,m,i,j,0,1)))
	   | A(_,n,i,j,0,1) -> 
                             if i < j 
                             then let h = ref (-1) in
                                  let (b,c) = match 
                                                (try
                                                  List.find
                                                    (function [Nonterminal b; Nonterminal c] ->
                                                       h := -1;
                                                       h := (try
                                                              List.find
                                                                (fun h -> 1 = obtainValue(H(cfg,b,c,i,j,h)))
                                                                (range i (j-1))
                                                            with Not_found -> -1);
                                                       !h >= 0
				  		      | _ -> false)
                                                    (List.filter 
                                                       (function [Nonterminal _; Nonterminal _] -> true | _ -> false)
                                                       (List.assoc n cfg.cfg))
                                                with Not_found -> failwith "Dangling parse tree!")
                                              with [Nonterminal b; Nonterminal c] -> (b,c)
			                         | _ -> failwith "This error cannot occur."
                                  in
                                  BinNode(n, extractOne(A(cfg,b,i,!h,1,1)), extractOne(A(cfg,c,!h+1,j,1,1)))
                             else let t = try
                                            List.find 
                                              (function t -> 1 = obtainValue(T(t,i)))
                                              (List.map
                                                (function [Terminal t] -> t | _ -> "")
                                                (List.filter
                                                  (function [Terminal t] -> true | _ -> false)
                                                  (List.assoc n cfg.cfg)))
                                          with Not_found -> failwith "Parse tree misses a leaf!"
                                  in Node(n,Leaf(t))
	   | _ -> failwith "Cannot extract parse trees from other variables."
  in
  let rec extractTwo v = 
    message 3 (fun _ -> "  Now processing variable " ^ showVar v ^ "\n");
    match v with
             A(_,n,i,j,1,2) -> 
                             (try
                               let (m,d) = List.find  
                                             (fun (m,d) -> 1 = obtainValue(A(cfg,m,i,j,0,3-d)))
                                             (StringIntSet.elements 
                                                (try 
                                                   StringMap.find n cfg.ambclosure
                                                 with Not_found -> failwith "Undefined nonterminal!"))
                               in
                               if n=m
                               then extractTwo(A(cfg,m,i,j,0,3-d))
                               else (if d=1 
                                    then let (t,t') = extractTwo(A(cfg,m,i,j,0,2)) in
                                         match t' with
                                               None -> (Derivation(n,t), None)
				             | Some t' -> (Derivation(n,t), Some(Derivation(n,t')))
                                    else let t = extractOne(A(cfg,m,i,j,0,1)) in
                                         (AmbDerivation(n,t), None))
                             with Not_found -> 
                               try
                                 let (b,c) = List.find
                                              (fun (b,c) -> 1 = obtainValue(H'(cfg,n,b,c,i,j)))
                                              (ordered_pairs 
                                                (StringIntSet.fold 
                                                  (fun (b,_) -> fun l -> b::l) 
                                                  (try
                                                    StringMap.find n cfg.ambclosure
                                                   with Not_found -> failwith "Undefined nonterminal!")
                                                  []))
                                 in
                                 let t = extractOne(A(cfg,b,i,j,0,1)) in
                                 let t' = extractOne(A(cfg,c,i,j,0,1)) in
                                 (Derivation(n,t),Some(Derivation(n,t')))
                               with Not_found -> failwith ("Parse tree is dangling at " ^ 
                                                            showVar(A(cfg,n,i,j,1,2)) ^ "\n"))
	   | A(_,n,i,j,0,2) -> if i < j 
                             then (let v = ref (B(-1)) in
                                  let found = ref false in

                                  List.iter
                                    (function [Nonterminal b; Nonterminal c] -> if not !found then
                                       (List.iter 
                                          (function [Nonterminal b'; Nonterminal c'] -> if not !found then
                                             (List.iter 
                                                (fun h -> if not !found then
                                                   (List.iter
                                                      (fun h' -> 
                                                         if not !found && not (b=b' && c=c' && h=h')
                                                         then (v := D(cfg,b,c,b',c',i,j,h,h');
                                                               found := 1 = obtainValue(!v)))
                                                      (range i (j-1))))
                                                (range i (j-1)))
					    | _ -> ())
                                          (List.assoc n cfg.cfg))
				      | _ -> ())
                                    (List.assoc n cfg.cfg);

                                  if not !found
                                  then (List.iter
                                          (function [Nonterminal b; Nonterminal c] -> if not !found then
                                             (List.iter
                                                (fun h -> if not !found 
                                                          then (v := H12(cfg,b,c,i,j,h);
                                                                found := 1 = obtainValue(!v));
                                                          if not !found
                                                          then (v := H21(cfg,b,c,i,j,h);
                                                                found := 1 = obtainValue(!v)))
                                                (range i (j-1)))
					    | _ -> ())
                                          (List.assoc n cfg.cfg));

                                  match !v with
                                        D(_,b,c,b',c',i,j,h,h') -> let t1 = extractOne(A(cfg,b,i,h,1,1)) in
                                                                   let t2 = extractOne(A(cfg,c,h+1,j,1,1)) in
                                                                   let t1' = extractOne(A(cfg,b',i,h',1,1)) in
                                                                   let t2' = extractOne(A(cfg,c',h'+1,j,1,1)) in
                                                                   (BinNode(n,t1,t2), Some(BinNode(n,t1',t2')))
				      | H12(_,b,c,i,j,h) -> let t = extractOne(A(cfg,b,i,h,1,1)) in
                                                            let (t2,t2') = extractTwo(A(cfg,c,h+1,j,1,2)) in
                                                            (BinNode(n,t,t2), match t2' with
                                                                                  None -> None
							                        | Some t2' -> Some(BinNode(n,t,t2')))
				      | H21(_,b,c,i,j,h) -> let (t1,t1') = extractTwo(A(cfg,b,i,h,1,2)) in
                                                            let t = extractOne(A(cfg,c,h+1,j,1,1)) in
                                                            (BinNode(n,t1,t), match t1' with
                                                                                    None -> None
							                          | Some t1' -> Some(BinNode(n,t1',t)))
				      | _ -> failwith "Unknown variable to continue extracting with.")
		             else failwith "Ambiguity should not occur on the base level!"

	   | _ -> failwith "Cannot extract parse trees from other variables."
  in
  extractTwo(A(cfg,cfg.start,0,k,1,2))
