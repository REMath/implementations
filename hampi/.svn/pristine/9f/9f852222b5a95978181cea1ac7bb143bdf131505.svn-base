open Basics ;;
open Cfg ;;
open Zchaff ;;
open Varencoding ;;


exception Uninitialised ;;
exception Unexpected_rule ;;


(* topdown: if answer is "sat", then there is a derivable word 
   --> implications from top to bottom, i.e. SAT solver guesses a word and has to show that it is derivable
        S(0,1)
        S(0,1) -> (A(0,0) /\ B(1,1)) \/ (...) 
        A(0,0) -> a(0)
        B(1,1) -> b(1)   *)

(* bottomup: if answer is "unsat" then there is no derivable word 
   --> implications from bottom to top, e.g. 
        -S(0,1)
        S(0,1) <- (A(0,0) /\ B(1,1)) \/ (...) 
        A(0,0) <- a(0)
        B(1,1) <- b(1) *)


let unique_symbols alphabet lower_k upper_k =
  let constraints = ref [] in

  for k=lower_k to upper_k do
    let cs = List.map (fun a -> posEncode(T(a,k))) alphabet in
    message 3 (fun _ -> "  Creating uniqueness constraint  >> " ^ 
                        String.concat " \\/ " (List.map (fun t -> showVar (T(t,k))) alphabet) ^ 
                        " <<\n    [ " ^ String.concat ", " (List.map string_of_int cs ) ^ " ]\n");
    constraints := (Array.of_list cs) :: !constraints;
    
    iter_with_tail
      (fun a -> fun ts -> message 3 (fun _ -> "  Creating uniqueness constraint  >> " ^
                                              showVar(T(a,k)) ^ " -> -" ^ showVar(T'(a,k)) ^ " <<\n    [ " ^
                                              string_of_int(negEncode(T(a,k))) ^ ", " ^ 
                                              string_of_int(negEncode(T'(a,k))) ^ "]\n"); 
                          constraints := [| negEncode(T(a,k)); negEncode(T'(a,k)) |] :: !constraints;
                          if List.length ts > 0 
                          then (let b = List.hd ts in
                                message 3 (fun _ -> "  Creating uniqueness constraint  >> " ^
                                                    showVar(T(a,k)) ^ " -> " ^ showVar(T'(b,k)) ^ " <<\n    [ " ^
                                                    string_of_int(negEncode(T(a,k))) ^ ", " ^ 
                                                    string_of_int(posEncode(T'(b,k))) ^ "]\n"); 
                                constraints := [| negEncode(T(a,k)); posEncode(T'(b,k)) |] :: !constraints;
                                message 3 (fun _ -> "  Creating uniqueness constraint  >> " ^
                                                    showVar(T'(a,k)) ^ " -> " ^ showVar(T'(b,k)) ^ " <<\n    [ " ^
                                                    string_of_int(negEncode(T'(a,k))) ^ ", " ^ 
                                                    string_of_int(posEncode(T'(b,k))) ^ "]\n"); 
                                constraints := [| negEncode(T'(a,k)); posEncode(T'(b,k)) |] :: !constraints))
      alphabet
  done;

  !constraints

(*
let base_topdown cfg lower_k upper_k =
  let constraints = ref [] in

  for i=lower_k to upper_k do
    List.iter
      (fun (a,ts) ->
         let nna = negEncode(N(cfg,a,i,i)) in
         message 3 (fun _ -> "  Creating t/d base constraint         >> " ^ showVar(N(cfg,a,i,i)) ^ " -> "
                             ^ String.concat " \\/ " (List.map (fun t -> showVar(T(t,i))) ts) ^ " <<\n    [ " ^
                             string_of_int nna ^ ", " ^ 
                             String.concat ", " (List.map (fun t -> string_of_int(posEncode(T(t,i)))) ts)
                             ^ " ]\n");
         constraints := (Array.of_list (nna :: (List.map (fun t -> posEncode(T(t,i))) ts))) :: !constraints)
      cfg.termprods
  done;

  !constraints


let base_bottomup cfg lower_k upper_k =
  let constraints = ref [] in

  for i=lower_k to upper_k do
    List.iter
      (fun (a,ts) ->
         List.iter 
           (fun t -> let ntt = negEncode(T(t,i)) in
                     let na = posEncode(N(cfg,a,i,i)) in
                     message 3 (fun _ -> "  Creating b/u base constraint         >> " ^ showVar(T(t,i)) ^ " -> " ^ 
                                         showVar(N(cfg,a,i,i)) ^ " <<\n    [ " ^ string_of_int ntt ^ ", " ^ 
                                         string_of_int na ^ " ]\n");
                     constraints := [| ntt ; na |] :: !constraints)
           ts)
      cfg.termprods
  done;

  !constraints
*)


let composition_topdown cfg lower_k upper_k =
  let constraints = ref [] in
  let nulls = cfg.nullable in
  let constr = ref [] in

  for i=0 to upper_k do
    for j=max i lower_k to upper_k do
      List.iter 
        (fun (a,rules) -> 
                  constr := [];
                  List.iter 
                      (function [Nonterminal b] -> constr := (N(cfg,b,i,j)) :: !constr; 
                              | [Terminal t]    -> if i=j then constr := (T(t,i)) :: !constr;
                              | []              -> ()
                              | [Nonterminal b; Nonterminal c] ->
                                   for h=i to j-1 do
                                     constr := (H(cfg,b,c,i,j,h)) :: !constr;
                                   done;
                                   if StringSet.mem b nulls then constr := (N(cfg,c,i,j)) :: !constr;
                                   if StringSet.mem c nulls then constr := (N(cfg,b,i,j)) :: !constr
			      | _ -> failwith "Grammar not in 2NF")
                       rules; 
                  message 3 (fun _ -> "  Creating t/d composition constraint     >> " ^ showVar(N(cfg,a,i,j)) ^ 
                                      " -> " ^ String.concat " \\/ " (List.map showVar !constr) ^ " <<\n    [" ^ 
                                      string_of_int (negEncode(N(cfg,a,i,j))) ^ ", " ^ 
                                      String.concat ", " (List.map (fun x -> string_of_int(posEncode(x))) !constr) ^ " ]\n");
                  constraints := (Array.of_list ((negEncode(N(cfg,a,i,j))) :: (List.map posEncode !constr))) :: 
                                 !constraints;
                  List.iter
                    (function H(_,b,c,i,j,h) ->                          
                       let nhbc = negEncode(H(cfg,b,c,i,j,h)) in
                       let nb = posEncode(N(cfg,b,i,h)) in
                       let nc = posEncode(N(cfg,c,h+1,j)) in
                       message 3 (fun _ -> "  Creating t/d composition constraint     >> " ^
                                           showVar(H(cfg,b,c,i,j,h)) ^ " -> " ^ showVar(N(cfg,b,i,h)) ^ 
                                           " <<\n    [ " ^ string_of_int nhbc ^ ", " ^ string_of_int nb ^ " ]\n");  
                       message 3 (fun _ -> "  Creating t/d composition constraint     >> " ^
                                           showVar(H(cfg,b,c,i,j,h)) ^ " -> " ^ showVar(N(cfg,c,h+1,j)) ^ 
                                           " <<\n    [ " ^ string_of_int nhbc ^ ", " ^ string_of_int nc ^ " ]\n");  
                       constraints := [| nhbc ; nb |] :: [| nhbc ; nc |] :: !constraints
                     | _ -> ())
                    !constr)
         cfg.cfg
    done
  done;
  !constraints


let composition_bottomup cfg lower_k upper_k =
  let constraints = ref [] in
  let nulls = cfg.nullable in

  for i=0 to upper_k do
    for j=max i lower_k to upper_k do
      List.iter 
        (fun (a,rules) -> 
           List.iter 
             (function [Nonterminal b] -> 
                     message 3 (fun _ -> "  Creating b/u composition constraint >> " ^ showVar(N(cfg,a,i,j)) ^
                                         " <- " ^ showVar(N(cfg,b,i,j)) ^ " <<\n    [ " ^ 
                                         string_of_int (posEncode(N(cfg,a,i,j))) ^ ", " ^ 
                                         string_of_int (negEncode(N(cfg,b,i,j))) ^ "]\n");
                     constraints := [| posEncode(N(cfg,a,i,j)); negEncode(N(cfg,b,i,j)) |] :: !constraints
	       | [Terminal t] -> 
                     if i=j 
                     then (message 3 (fun _ -> "  Creating b/u composition constraint >> " ^ 
                                               showVar(N(cfg,a,i,j)) ^ " <- " ^ 
                                               showVar(T(t,i)) ^ " <<\n    [ " ^ 
                                               string_of_int (posEncode(N(cfg,a,i,j))) ^ ", " ^ 
                                               string_of_int (negEncode(T(t,i))) ^ "]\n");
                           constraints := [| posEncode(N(cfg,a,i,j)); negEncode(T(t,i)) |] :: !constraints);
               | []              -> ()
               | [Nonterminal b; Nonterminal c] ->
                     for h=i to j-1 do
                       message 3 (fun _ -> "  Creating b/u composition constraint >> " ^ showVar(N(cfg,a,i,j)) ^ 
                                           " <- " ^ showVar(N(cfg,b,i,h)) ^ " /\\ " ^ showVar(N(cfg,c,h+1,j)) ^
                                           " <<\n   [ " ^ string_of_int(posEncode(N(cfg,a,i,j))) ^ ", " ^ 
                                           string_of_int(negEncode(N(cfg,b,i,h))) ^ ", " ^
                                           string_of_int(negEncode(N(cfg,c,h+1,j))) ^ " ]\n");
                       constraints := [| posEncode(N(cfg,a,i,j)); 
                                         negEncode(N(cfg,b,i,h)); negEncode(N(cfg,c,h+1,j)) |] :: !constraints;
                     done;
                     if StringSet.mem b nulls 
                     then (message 3 (fun _ -> "  Creating b/u composition constraint >> " ^ showVar(N(cfg,a,i,j)) ^ 
                                           " <- " ^ showVar(N(cfg,c,i,j)) ^ " <<\n   [ " ^ 
                                           string_of_int(posEncode(N(cfg,a,i,j))) ^ ", " ^ 
                                           string_of_int(negEncode(N(cfg,c,i,j))) ^ " ]\n");
                           constraints := [| posEncode(N(cfg,a,i,j)); negEncode(N(cfg,c,i,j)) |] :: !constraints);
                     if StringSet.mem c nulls 
                     then (message 3 (fun _ -> "  Creating b/u composition constraint >> " ^ showVar(N(cfg,a,i,j)) ^ 
                                           " <- " ^ showVar(N(cfg,b,i,j)) ^ " <<\n   [ " ^ 
                                           string_of_int(posEncode(N(cfg,a,i,j))) ^ ", " ^ 
                                           string_of_int(negEncode(N(cfg,b,i,j))) ^ " ]\n");
                           constraints := [| posEncode(N(cfg,a,i,j)); negEncode(N(cfg,b,i,j)) |] :: !constraints)
	       | _ -> ())
             rules)
        cfg.cfg
    done
  done;

  !constraints

(*
  let constraints = ref [] in

  for i=0 to upper_k-1 do
    for j=max (i+1) lower_k to upper_k do
      List.iter 
        (fun a -> let rules = List.filter (function [_;_] -> true | _ -> false) (List.assoc a cfg.cfg) in
                  for h=i to j-1 do
                    List.iter
                      (function [Nonterminal b; Nonterminal c] ->
                                   let na = posEncode(N(cfg,a,i,j,0)) in
                                   let nnb = negEncode(N(cfg,b,i,h,1)) in
                                   let nnc = negEncode(N(cfg,c,h+1,j,1)) in
                                   message 3 (fun _ -> "  Creating b/u composition constraint     >> " ^ 
                                                       showVar(N(cfg,b,i,h,1)) ^ " /\\ " ^ showVar(N(cfg,c,h+1,j,1)) ^ 
                                                       " -> " ^ showVar(N(cfg,a,i,j,0)) ^ " <<\n    [ " ^ 
                                                       string_of_int nnb ^ ", " ^ string_of_int nnc
                                                       ^ ", " ^ string_of_int na ^ " ]\n");  
                                   constraints := [| nnb; nnc; na |] :: !constraints
                              | _ -> raise Unexpected_rule)
                      rules
                  done)
        cfg.nonterminals
    done
  done;

  !constraints
*)

(*
let closure_topdown cfg lower_k upper_k =
  let constraints = ref [] in

  for i=0 to upper_k do
    for j=max i lower_k to upper_k do
      StringMap.iter
        (fun a -> fun bs -> 
           let nna = negEncode(N(cfg,a,i,j,1)) in
           let nbs = StringSet.fold (fun b -> fun l -> (posEncode(N(cfg,b,i,j,0))) :: l) bs [] in
           message 3 (fun _ -> "  Creating t/d closure constraint      >> " ^ showVar(N(cfg,a,i,j,1)) ^ " -> " ^
                               String.concat " \\/ " 
                                             (StringSet.fold (fun b -> fun l -> (showVar(N(cfg,b,i,j,0))) :: l) bs [])
                               ^ " <<\n    [ " ^ string_of_int nna ^ ", " ^ 
                               String.concat ", " (List.map string_of_int nbs) ^ " ]\n");
           constraints := (Array.of_list (nna :: nbs)) :: !constraints)
        cfg.closure
    done
  done;

  !constraints 


let closure_bottomup cfg lower_k upper_k =
  let constraints = ref [] in

  for i=0 to upper_k do
    for j=max i lower_k to upper_k do
      StringMap.iter
        (fun a -> fun bs -> 
           StringSet.iter 
             (fun b -> let na = posEncode(N(cfg,a,i,j,1)) in
                       let nnb = negEncode(N(cfg,b,i,j,0)) in
                       message 3 (fun _ -> "  Creating b/u closure constraint      >> " ^ showVar(N(cfg,b,i,j,0)) ^ 
                                           " -> " ^ showVar(N(cfg,a,i,j,1)) ^ " <<\n    [ " ^
                                           string_of_int nnb ^ ", " ^ string_of_int na ^ " ]\n"); 
                       constraints := [| nnb ; na |] :: !constraints)
             bs)
        cfg.closure
    done
  done;

  !constraints 
*)

let derivable cfg lower_k upper_k =
  let s = cfg.start in

  let rs = range lower_k upper_k in
  let constr = List.map (fun j -> posEncode(N(cfg,s,0,j))) rs in

  message 3 (fun _ -> let ns = List.map (fun j -> showVar(N(cfg,s,0,j))) rs in
                      "  Creating t/d derivability constraint >> " ^ String.concat " \\/ " ns ^ " <<\n    [ " ^ 
                      String.concat ", " (List.map string_of_int constr) ^ " ]\n");
  [ Array.of_list constr ]


let underivable cfg lower_k upper_k =
  let constraints = ref [] in
  let s = cfg.start in

  for j=lower_k to upper_k do
    let nns = negEncode(N(cfg,s,0,j)) in
    message 3 (fun _ -> "  Creating b/u underivability constraint >> -" ^ showVar(N(cfg,s,0,j)) ^ " <<\n    [ " ^ 
                        string_of_int nns ^ " ]\n");
    constraints := [| nns |] :: !constraints
  done;

  !constraints


let derives_one_but_not_the_other lower_k upper_k =
  let rs = range lower_k upper_k in
  let constr = List.map (fun j -> posEncode(B(j))) rs in

  message 3 (fun _ -> let ns = List.map (fun j -> showVar(B(j))) rs in
                      "  Creating derivability constraint >> " ^ String.concat " \\/ " ns ^ " <<\n    [ " ^ 
                      String.concat ", " (List.map string_of_int constr) ^ " ]\n");
  [ Array.of_list constr ]


let derives_one_but_not_the_other_implications cfg1 cfg2 lower_k upper_k =
  let constrs = ref [] in
  for j = lower_k to upper_k do
    let nb = negEncode(B(j)) in
    let ns = posEncode(N(cfg1,cfg1.start,0,j)) in
    message 3 (fun _ -> "Creating t/d derivability constraint >> " ^ showVar(B(j)) ^ " -> " ^ 
                        showVar(N(cfg1,cfg1.start,0,j)) ^ " <<\n    [ " ^ string_of_int nb ^ ", " ^ 
                        string_of_int ns ^ " ]\n");
    constrs := [| nb; ns |] :: !constrs;
    let ns = negEncode(N(cfg2,cfg2.start,0,j)) in
    message 3 (fun _ -> "Creating t/d derivability constraint >> " ^ showVar(B(j)) ^ " -> -" ^ 
                        showVar(N(cfg2,cfg2.start,0,j)) ^ " <<\n    [ " ^ string_of_int nb ^ ", " ^ 
                        string_of_int ns ^ " ]\n");
    constrs := [| nb; ns |] :: !constrs
  done;
  !constrs



let all_derivable lower_k upper_k =
  let rs = range lower_k upper_k in
  let constr = List.map (fun j -> posEncode(B(j))) rs in

  message 3 (fun _ -> let ns = List.map (fun j -> showVar(B(j))) rs in
                      "  Creating derivability constraint >> " ^ String.concat " \\/ " ns ^ " <<\n    [ " ^ 
                      String.concat ", " (List.map string_of_int constr) ^ " ]\n");
  [ Array.of_list constr ]


let all_derivable_implications cfgs lower_k upper_k =
  let constrs = ref [] in
  List.iter (fun cfg -> 
    for j = lower_k to upper_k do
      let nb = negEncode(B(j)) in
      let ns = posEncode(N(cfg,cfg.start,0,j)) in
      message 3 (fun _ -> "Creating t/d derivability constraint >> " ^ showVar(B(j)) ^ " -> " ^ 
                          showVar(N(cfg,cfg.start,0,j)) ^ " <<\n    [ " ^ string_of_int nb ^ ", " ^ 
                          string_of_int ns ^ " ]\n");
      constrs := [| nb; ns |] :: !constrs;
    done) cfgs;
  !constrs





let derives_exactly_one lower_k upper_k = 
  [ Array.of_list (List.concat (List.map 
                                  (fun j -> [posEncode (B(j)); posEncode(B'(j)) ])
                                  (range lower_k upper_k))) ]

let derives_exactly_one_implications cfg1 cfg2 lower_k upper_k = 
  let constraints = ref [] in

  for j = lower_k to upper_k do
    let nb = negEncode(B(j)) in
    let ns = posEncode(N(cfg1,cfg1.start,0,j)) in
    message 3 (fun _ -> "  Creating equivalence constraint    >> " ^ showVar(B(j)) ^ " -> " ^ 
                        showVar(N(cfg1,cfg1.start,0,j)) ^ "\n    [ " ^ string_of_int nb ^ ", " ^ string_of_int ns 
                        ^ " ]\n");
    constraints := [| nb; ns |] :: !constraints;
    let ns = negEncode(N(cfg2,cfg2.start,0,j)) in
    message 3 (fun _ -> "  Creating equivalence constraint    >> " ^ showVar(B(j)) ^ " -> -" ^ 
                        showVar(N(cfg2,cfg2.start,0,j)) ^ "\n    [ " ^ string_of_int nb ^ ", " ^ string_of_int ns 
                        ^ " ]\n");
    constraints := [| nb; ns |] :: !constraints;

    let nb = negEncode(B'(j)) in
    let ns = negEncode(N(cfg1,cfg1.start,0,j)) in
    message 3 (fun _ -> "  Creating equivalence constraint    >> " ^ showVar(B'(j)) ^ " -> -" ^ 
                        showVar(N(cfg1,cfg1.start,0,j)) ^ "\n    [ " ^ string_of_int nb ^ ", " ^ string_of_int ns 
                        ^ " ]\n");
    constraints := [| nb; ns |] :: !constraints;
    let ns = posEncode(N(cfg2,cfg2.start,0,j)) in
    message 3 (fun _ -> "  Creating equivalence constraint    >> " ^ showVar(B'(j)) ^ " -> " ^ 
                        showVar(N(cfg2,cfg2.start,0,j)) ^ "\n    [ " ^ string_of_int nb ^ ", " ^ string_of_int ns 
                        ^ " ]\n");
    constraints := [| nb; ns |] :: !constraints
  done;

  !constraints





let two_productions cfg lower_k upper_k =
  let constraints = ref [] in
  let cnt = ref 0 in
  let nullable = cfg.ambnullable in

  message 3 (fun _ -> "  Creating ambiguity constraint >> " ^
                      String.concat " \\/ " (List.concat
                                               (List.map 
                                                  (fun j -> (List.map 
                                                               (fun n -> let r = number_of_productions cfg n in
                                                                         if StringSet.mem n cfg.ambnonterminals
                                                                         then showVar(N(cfg,n,0,j))
                                                                         else showVar(Two(n,j,r)))
                                                               cfg.nonterminals))
                                                  (range lower_k upper_k))) ^
                      " <<\n    [ " ^
                      String.concat ", " (List.concat 
                                            (List.map 
                                               (fun j -> List.map
                                                           (fun n -> let r = number_of_productions cfg n in
                                                                     if StringSet.mem n cfg.ambnonterminals
                                                                     then string_of_int(posEncode(N(cfg,n,0,j)))
                                                                     else string_of_int(posEncode(Two(n,j,r))))
                                                           cfg.nonterminals)
                                               (range lower_k upper_k))) ^ " ]\n");
  constraints := [ Array.of_list (List.concat 
                                    (List.map 
                                       (fun j -> List.map
                                                   (fun n -> let r = number_of_productions cfg n in
                                                             if StringSet.mem n cfg.ambnonterminals
                                                             then posEncode(N(cfg,n,0,j))
                                                             else posEncode(Two(n,j,r)))
                                                   cfg.nonterminals)
                                       (range lower_k upper_k))) ]; 

  
  List.iter
    (fun n -> let r = number_of_productions cfg n in
              List.iter
                (fun j -> message 3 (fun _ -> "  Creating (unnecessary) ambiguity constraint >> " ^ 
                                              showVar(Two(n,j,r)) ^ " -> " ^ showVar(N(cfg,n,0,j)) ^ " <<\n    [ "
                                              ^ string_of_int(negEncode(Two(n,j,r))) ^ ", " ^ 
                                              string_of_int(posEncode(N(cfg,n,0,j))) ^ " ]\n");
                          constraints := [| negEncode(Two(n,j,r)); posEncode(N(cfg,n,0,j)) |] :: !constraints)
                (range lower_k upper_k))
    (List.filter
       (fun n -> not (StringSet.mem n cfg.ambnonterminals))
       cfg.nonterminals);

  for j = lower_k to upper_k do
    List.iter
      (fun (n,rules) -> 
         cnt := List.length rules;

         List.iter
           (function [Nonterminal b] -> 
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(Two(n,j,!cnt)) ^
                                            " -> " ^ showVar(Two(n,j,!cnt-1)) ^ " \\/ ( " ^ showVar(N(cfg,b,0,j)) ^ 
                                            " /\\ " ^ showVar(One(n,j,!cnt-1)) ^ " ) <<\n    [ " ^ 
                                            string_of_int(negEncode(Two(n,j,!cnt))) ^ ", " ^
                                            string_of_int(posEncode(Two(n,j,!cnt-1))) ^ ", " ^
                                            string_of_int(posEncode(A(cfg,b,j,!cnt-1))) ^ "]\n    [ " ^
                                            string_of_int(negEncode(A(cfg,b,j,!cnt-1))) ^ ", " ^
                                            string_of_int(posEncode(N(cfg,b,0,j))) ^ "]\n    [ " ^
                                            string_of_int(negEncode(A(cfg,b,j,!cnt-1))) ^ ", " ^
                                            string_of_int(posEncode(One(n,j,!cnt-1))) ^ "]\n");
                        constraints := [| negEncode(Two(n,j,!cnt)); posEncode(Two(n,j,!cnt-1)); 
                                          posEncode(A(cfg,b,j,!cnt-1)) |] ::
                                       [| negEncode(A(cfg,b,j,!cnt-1)); posEncode(N(cfg,b,0,j)) |] ::
                                       [| negEncode(A(cfg,b,j,!cnt-1)); posEncode(One(n,j,!cnt-1)) |] ::
                                       !constraints;
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(One(n,j,!cnt)) ^
                                            " -> " ^ showVar(One(n,j,!cnt-1)) ^ " \\/ " ^ showVar(N(cfg,b,0,j)) ^ 
                                            " <<\n    [ " ^ 
                                            string_of_int(negEncode(One(n,j,!cnt))) ^ ", " ^
                                            string_of_int(posEncode(One(n,j,!cnt-1))) ^ ", " ^
                                            string_of_int(posEncode(N(cfg,b,0,j))) ^ "]\n");
                        constraints := [| negEncode(One(n,j,!cnt)); posEncode(One(n,j,!cnt-1)); 
                                          posEncode(N(cfg,b,0,j)) |] :: !constraints;
                        decr cnt
	           | [Terminal t] -> 
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(Two(n,j,!cnt)) ^
                                            " -> " ^ showVar(Two(n,j,!cnt-1)) ^ 
                                            (if j=0 then " \\/ ( " ^ showVar(T(t,j)) ^ " /\\ " ^ 
                                                        showVar(One(n,j,!cnt-1)) ^ " )"
                                            else "") ^ " <<\n    [ " ^ 
                                            string_of_int(negEncode(Two(n,j,!cnt))) ^ ", " ^
                                            string_of_int(posEncode(Two(n,j,!cnt-1))) ^ 
                                            (if j=0 
                                             then ", " ^ string_of_int(posEncode(A(cfg,t,j,!cnt-1))) ^ 
                                                  "]\n    [ " ^ string_of_int(negEncode(A(cfg,t,j,!cnt-1))) ^ ", " ^
                                                  string_of_int(posEncode(T(t,j))) ^ "]\n    [ " ^
                                                  string_of_int(negEncode(A(cfg,t,j,!cnt-1))) ^ ", " ^
                                                  string_of_int(posEncode(One(n,j,!cnt-1)))
                                             else "") ^ "]\n");
                        constraints := (Array.of_list (negEncode(Two(n,j,!cnt)) :: posEncode(Two(n,j,!cnt-1)) :: 
                                                      if j=0 then [ posEncode(A(cfg,t,j,!cnt-1)) ] else [])) ::
                                       (if j=0 
                                        then [| negEncode(A(cfg,t,j,!cnt-1)); posEncode(T(t,j)) |] ::
                                             [| negEncode(A(cfg,t,j,!cnt-1)); posEncode(One(n,j,!cnt-1)) |] ::
                                             !constraints
                                        else !constraints);
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(One(n,j,!cnt)) ^
                                            " -> " ^ showVar(One(n,j,!cnt-1)) ^ " \\/ " ^ showVar(T(t,j)) ^ 
                                            " <<\n    [ " ^ 
                                            string_of_int(negEncode(One(n,j,!cnt))) ^ ", " ^
                                            string_of_int(posEncode(One(n,j,!cnt-1))) ^ ", " ^
                                            string_of_int(posEncode(T(t,j))) ^ " ]\n");
                        constraints := [| negEncode(One(n,j,!cnt)); posEncode(One(n,j,!cnt-1)); 
                                          posEncode(T(t,j)) |] :: !constraints;
                        decr cnt
		   | [Nonterminal b; Nonterminal c] ->
                        (* Start *)
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(Two(n,j,!cnt)) ^
                                            " -> " ^ showVar(AT(n,j,!cnt,-1)) ^ " <<\n    [" ^ 
                                            string_of_int(negEncode(Two(n,j,!cnt))) ^ ", " ^
                                            string_of_int(posEncode(AT(n,j,!cnt,-1))) ^ " ]\n");
                        constraints := [| negEncode(Two(n,j,!cnt)); posEncode(AT(n,j,!cnt,-1)) |] :: !constraints;
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(One(n,j,!cnt)) ^
                                            " -> " ^ showVar(AO(n,j,!cnt,-1)) ^ " <<\n    [" ^ 
                                            string_of_int(negEncode(One(n,j,!cnt))) ^ ", " ^
                                            string_of_int(posEncode(AO(n,j,!cnt,-1))) ^ " ]\n");
                        constraints := [| negEncode(One(n,j,!cnt)); posEncode(AO(n,j,!cnt,-1)) |] :: !constraints;

                        (* special case of B nullable *)
                        (*   subcase TWO *)
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(AT(n,j,!cnt,-1)) ^
                                            " -> " ^ showVar(AT(n,j,!cnt,0)) ^ 
                                            if StringIntSet.mem (b,2) nullable
                                            then (" \\/ " ^ showVar(N(cfg,c,0,j)) ^ " <<\n    [ " ^ 
                                                  string_of_int(negEncode(AT(n,j,!cnt,-1))) ^ ", " ^
                                                  string_of_int(posEncode(AT(n,j,!cnt,0))) ^ ", " ^
                                                  string_of_int(posEncode(N(cfg,c,0,j))) ^ " ]\n")
                                            else if StringIntSet.mem (b,1) nullable
                                            then (" \\/ ( " ^ showVar(N(cfg,c,0,j)) ^ " /\\ " ^ showVar(AO(n,j,!cnt,0)) ^ 
                                                  " ) <<\n    [ " ^ string_of_int(negEncode(AT(n,j,!cnt,-1))) ^ ", " ^
                                                  string_of_int(posEncode(AT(n,j,!cnt,0))) ^ ", " ^
                                                  string_of_int(posEncode(N(cfg,c,0,j))) ^ " ]\n    [ " ^ 
                                                  string_of_int(negEncode(AT(n,j,!cnt,-1))) ^ ", " ^
                                                  string_of_int(posEncode(AT(n,j,!cnt,0))) ^ ", " ^
                                                  string_of_int(posEncode(AO(n,j,!cnt,0))) ^ " ]\n")
                                            else (" <<\n    [ " ^ string_of_int(negEncode(AT(n,j,!cnt,-1))) ^ ", " ^ 
                                                  string_of_int(posEncode(AT(n,j,!cnt,0))) ^ " ]\n"));
                        (if (StringIntSet.mem (b,2) nullable) || (StringIntSet.mem (b,1) nullable)
                        then (constraints := [| negEncode(AT(n,j,!cnt,-1)); posEncode(AT(n,j,!cnt,0)); posEncode(N(cfg,c,0,j)) |] ::
                                             !constraints;
                             if StringIntSet.mem (b,1) nullable
                             then constraints := [| negEncode(AT(n,j,!cnt,-1)); posEncode(AT(n,j,!cnt,0)); posEncode(AO(n,j,!cnt,0)) |]
                                                 :: !constraints)
                        else constraints := [| negEncode(AT(n,j,!cnt,-1)); posEncode(AT(n,j,!cnt,0)) |] :: !constraints);
                        (*    subcase ONE *)
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(AO(n,j,!cnt,-1)) ^
                                            " -> " ^ showVar(AO(n,j,!cnt,0)) ^ 
                                            if StringIntSet.mem (b,2) nullable || StringIntSet.mem (b,1) nullable
                                            then (" \\/ " ^ showVar(N(cfg,c,0,j)) ^ " <<\n    [ " ^ 
                                                  string_of_int(negEncode(AO(n,j,!cnt,-1))) ^ ", " ^
                                                  string_of_int(posEncode(AO(n,j,!cnt,0))) ^ ", " ^
                                                  string_of_int(posEncode(N(cfg,c,0,j))) ^ " ]\n")
                                            else (" <<\n    [ " ^ string_of_int(negEncode(AO(n,j,!cnt,-1))) ^ ", " ^
                                                  string_of_int(posEncode(AO(n,j,!cnt,0))) ^ " ]\n"));
                        (if (StringIntSet.mem (b,2) nullable) || (StringIntSet.mem (b,1) nullable)
                        then constraints := [| negEncode(AO(n,j,!cnt,-1)); posEncode(AO(n,j,!cnt,0)); posEncode(N(cfg,c,0,j)) |] ::
                                             !constraints
                        else constraints := [| negEncode(AO(n,j,!cnt,-1)); posEncode(AO(n,j,!cnt,0)) |] :: !constraints);

                        (* usual cases of production A -> BC splitting the subword up at position h *)
                        for h = 0 to j-1 do
                          message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(AT(n,j,!cnt,h)) ^
                                              " -> " ^ showVar(AT(n,j,!cnt,h+1)) ^ " \\/ ( " ^
                                              showVar(N(cfg,b,0,h)) ^ " /\\ " ^ showVar(N(cfg,c,h+1,j)) ^ " /\\ "
                                              ^ showVar(AO(n,j,!cnt,h+1)) ^ " ) <<\n    [ " ^
                                              string_of_int(negEncode(AT(n,j,!cnt,h))) ^ ", " ^
                                              string_of_int(posEncode(AT(n,j,!cnt,h+1))) ^ ", " ^
                                              string_of_int(posEncode(ATH(b,c,j,h,!cnt))) ^ " ]\n    [ " ^
                                              string_of_int(negEncode(ATH(b,c,j,h,!cnt))) ^ ", " ^
                                              string_of_int(posEncode(N(cfg,b,0,h))) ^ " ]\n    [ " ^
                                              string_of_int(negEncode(ATH(b,c,j,h,!cnt))) ^ ", " ^
                                              string_of_int(posEncode(N(cfg,c,h+1,j))) ^ " ]\n    [ " ^
                                              string_of_int(negEncode(ATH(b,c,j,h,!cnt))) ^ ", " ^
                                              string_of_int(posEncode(AO(n,j,!cnt,h+1))) ^ " ]\n");
                          constraints := [| negEncode(AT(n,j,!cnt,h)); posEncode(AT(n,j,!cnt,h+1)); 
                                                                       posEncode(ATH(b,c,j,h,!cnt)) |] :: 
                                         [| negEncode(ATH(b,c,j,h,!cnt)); posEncode(N(cfg,b,0,h)) |] ::
                                         [| negEncode(ATH(b,c,j,h,!cnt)); posEncode(N(cfg,c,h+1,j)) |] ::
                                         [| negEncode(ATH(b,c,j,h,!cnt)); posEncode(AO(n,j,!cnt,h+1)) |] ::
                                         !constraints;
                          message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(AO(n,j,!cnt,h)) ^
                                              " -> " ^ showVar(AO(n,j,!cnt,h+1)) ^ " \\/ ( " ^
                                              showVar(N(cfg,b,0,h)) ^ " /\\ " ^ showVar(N(cfg,c,h+1,j)) ^ 
                                              " ) <<\n    [ " ^ string_of_int(negEncode(AO(n,j,!cnt,h))) ^ ", " ^
                                              string_of_int(posEncode(AO(n,j,!cnt,h+1))) ^ ", " ^
                                              string_of_int(posEncode(AOH(b,c,j,h,!cnt))) ^ " ]\n    [ " ^
                                              string_of_int(negEncode(AOH(b,c,j,h,!cnt))) ^ ", " ^
                                              string_of_int(posEncode(N(cfg,b,0,h))) ^ " ]\n    [ " ^
                                              string_of_int(negEncode(AOH(b,c,j,h,!cnt))) ^ ", " ^
                                              string_of_int(posEncode(N(cfg,c,h+1,j))) ^ " ]\n");
                          constraints := [| negEncode(AO(n,j,!cnt,h)); posEncode(AO(n,j,!cnt,h+1)); 
                                                                       posEncode(AOH(b,c,j,h,!cnt)) |] :: 
                                         [| negEncode(AOH(b,c,j,h,!cnt)); posEncode(N(cfg,b,0,h)) |] ::
                                         [| negEncode(AOH(b,c,j,h,!cnt)); posEncode(N(cfg,c,h+1,j)) |] ::
                                         !constraints;
                        done;

                        (* special case of C nullable *)
                        (*   subcase TWO *)
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(AT(n,j,!cnt,j)) ^
                                            " -> " ^ showVar(AT(n,j,!cnt-1,j+1)) ^ 
                                            if StringIntSet.mem (c,2) nullable
                                            then (" \\/ " ^ showVar(N(cfg,b,0,j)) ^ " <<\n    [ " ^ 
                                                  string_of_int(negEncode(AT(n,j,!cnt,j))) ^ ", " ^
                                                  string_of_int(posEncode(AT(n,j,!cnt,j+1))) ^ ", " ^
                                                  string_of_int(posEncode(N(cfg,b,0,j))) ^ " ]\n")
                                            else if StringIntSet.mem (c,1) nullable
                                            then (" \\/ ( " ^ showVar(N(cfg,b,0,j)) ^ " /\\ " ^ showVar(AO(n,j,!cnt,j+1)) ^ 
                                                  " ) <<\n    [ " ^ string_of_int(negEncode(AT(n,j,!cnt,j))) ^ ", " ^
                                                  string_of_int(posEncode(AT(n,j,!cnt,j+1))) ^ ", " ^
                                                  string_of_int(posEncode(N(cfg,b,0,j))) ^ " ]\n    [ " ^ 
                                                  string_of_int(negEncode(AT(n,j,!cnt,j))) ^ ", " ^
                                                  string_of_int(posEncode(AT(n,j,!cnt,j+1))) ^ ", " ^
                                                  string_of_int(posEncode(AO(n,j,!cnt,j+1))) ^ " ]\n")
                                            else (" <<\n    [ " ^ string_of_int(negEncode(AT(n,j,!cnt,j))) ^ ", " ^ 
                                                  string_of_int(posEncode(AT(n,j,!cnt,j+1))) ^ " ]\n"));
                        (if (StringIntSet.mem (c,2) nullable) || (StringIntSet.mem (c,1) nullable)
                        then (constraints := [| negEncode(AT(n,j,!cnt,j)); posEncode(AT(n,j,!cnt,j+1)); posEncode(N(cfg,b,0,j)) |] ::
                                             !constraints;
                             if StringIntSet.mem (c,1) nullable
                             then constraints := [| negEncode(AT(n,j,!cnt,j)); posEncode(AT(n,j,!cnt,j+1)); posEncode(AO(n,j,!cnt,j+1)) |]
                                                 :: !constraints)
                        else constraints := [| negEncode(AT(n,j,!cnt,j)); posEncode(AT(n,j,!cnt,j+1)) |] :: !constraints);
                        (*    subcase ONE *)
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(AO(n,j,!cnt,j)) ^
                                            " -> " ^ showVar(AO(n,j,!cnt,j+1)) ^ 
                                            if StringIntSet.mem (c,2) nullable || StringIntSet.mem (c,1) nullable
                                            then (" \\/ " ^ showVar(N(cfg,b,0,j)) ^ " <<\n    [ " ^ 
                                                  string_of_int(negEncode(AO(n,j,!cnt,j))) ^ ", " ^
                                                  string_of_int(posEncode(AO(n,j,!cnt,j+1))) ^ ", " ^
                                                  string_of_int(posEncode(N(cfg,b,0,j))) ^ " ]\n")
                                            else (" <<\n    [ " ^ string_of_int(negEncode(AO(n,j,!cnt,j))) ^ ", " ^
                                                  string_of_int(posEncode(AO(n,j,!cnt,j+1))) ^ " ]\n"));
                        (if (StringIntSet.mem (c,2) nullable) || (StringIntSet.mem (c,1) nullable)
                        then constraints := [| negEncode(AO(n,j,!cnt,j)); posEncode(AO(n,j,!cnt,j+1)); posEncode(N(cfg,b,0,j)) |] ::
                                             !constraints
                        else constraints := [| negEncode(AO(n,j,!cnt,j)); posEncode(AO(n,j,!cnt,j+1)) |] :: !constraints);

                        (* Finish *)
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(AT(n,j,!cnt,j+1)) ^ " -> " ^
                                            showVar(Two(n,j,!cnt-1)) ^ " <<\n    [ " ^ string_of_int(negEncode(AT(n,j,!cnt,j+1))) ^
                                            ", " ^ string_of_int(posEncode(Two(n,j,!cnt-1))) ^ " ]\n");
                        message 3 (fun _ -> "  Creating rule counting constraint >> " ^ showVar(AO(n,j,!cnt,j+1)) ^ " -> " ^
                                            showVar(One(n,j,!cnt-1)) ^ " <<\n    [ " ^ string_of_int(negEncode(AO(n,j,!cnt,j+1))) ^
                                            ", " ^ string_of_int(posEncode(One(n,j,!cnt-1))) ^ " ]\n");
                        constraints := [| negEncode(AT(n,j,!cnt,j+1)); posEncode(Two(n,j,!cnt-1)) |] ::
                                       [| negEncode(AO(n,j,!cnt,j+1)); posEncode(One(n,j,!cnt-1)) |] :: !constraints;
                        decr cnt
		   | _ -> failwith "Unknown rule format!")
           rules;

         message 3 (fun _ -> "  Creating rule counting constraint >> -" ^ showVar(Two(n,j,0)) ^
                             " <<\n    [ " ^ string_of_int (negEncode(Two(n,j,0))) ^ " ]\n" ^
                             "  Creating rule counting constraint >> -" ^ showVar(One(n,j,0)) ^
                             " <<\n    [ " ^ string_of_int (negEncode(One(n,j,0))) ^ " ]\n");
         constraints := [| negEncode(Two(n,j,0)) |] :: [| negEncode(One(n,j,0)) |] ::
                        !constraints)
      cfg.cfg
  done;

(*
  let rng = range lower_k upper_k in
  (Array.of_list 
    (List.concat
      (List.map 
         (fun n -> let rules = List.assoc n cfg.cfg in
                   List.map 
                     (fun j -> posEncode(Two(n,j,List.length rules)))
                      rng)
         (StringSet.elements cfg.ambnonterminals)))) :: *)

  !constraints



(*
let ambiguity_base cfg lower_k upper_k =
  let constraints = ref [] in

  for i=lower_k to upper_k do
    List.iter
      (fun (a,ts) ->
         let nna = negEncode(A(cfg,a,i,i,0,1)) in
         message 3 (fun _ -> "  Creating ambiguity base constraint  >> " ^ showVar(A(cfg,a,i,i,0,1)) ^ " -> " ^
                             String.concat " \\/ " (List.map (fun t -> showVar(T(t,i))) ts) ^ " <<\n    [ " ^
                             string_of_int nna ^ ", " ^ 
                             String.concat ", " (List.map (fun t -> string_of_int (posEncode(T(t,i)))) ts)
                             ^ " ]\n");
         constraints := (Array.of_list (nna :: (List.map (fun t -> posEncode(T(t,i))) ts))) :: !constraints;
         let nna = negEncode(A(cfg,a,i,i,0,2)) in
         message 3 (fun _ -> "  Creating ambiguity base constraint  >> -" ^ showVar(A(cfg,a,i,i,0,2)) ^ 
                             " <<\n    [ " ^ string_of_int nna ^ " ]\n");
         constraints := [| nna |] :: !constraints)
      cfg.termprods
  done;

  !constraints


let ambiguity_derivable cfg lower_k upper_k =
  let s = cfg.start in

  let rs = range lower_k upper_k in
  let constr = List.map (fun j -> posEncode(A(cfg,s,0,j,1,2))) rs in

  message 3 (fun _ -> let ns = List.map (fun j -> showVar(A(cfg,s,0,j,1,2))) rs in
                      "  Creating ambiguity derivability constraint  >> " ^ String.concat " \\/ " ns ^ 
                      " <<\n    [ " ^ String.concat ", " (List.map string_of_int constr) ^ " ]\n");
  [ Array.of_list constr ]


let ambiguity_closure cfg lower_k upper_k =
  let constraints = ref [] in

  for i=0 to upper_k do
    for j=max i lower_k to upper_k do
      StringMap.iter
        (fun a -> fun bs -> 
           let nna = negEncode(A(cfg,a,i,j,1,1)) in
           let nbs = StringSet.fold (fun b -> fun l -> (posEncode(A(cfg,b,i,j,0,1))) :: l) bs [] in
           message 3 (fun _ -> "  Creating ambiguity closure constraint  >> " ^ showVar(A(cfg,a,i,j,1,1)) ^ " -> " 
                               ^ String.concat " \\/ " (StringSet.fold (fun b -> fun l -> (showVar(A(cfg,b,i,j,0,1))) :: l) bs [])
                               ^ " <<\n    [ " ^ string_of_int nna ^ ", " ^ 
                               String.concat ", " (List.map string_of_int nbs) ^ " ]\n");
           constraints := (Array.of_list (nna :: nbs)) :: !constraints)
        cfg.closure;
      StringMap.iter
        (fun a -> fun bs -> 
           let nna = negEncode(A(cfg,a,i,j,1,2)) in
           let nbs = StringIntSet.fold (fun (b,n) -> fun l -> (posEncode(A(cfg,b,i,j,0,3-n))) :: l) bs [] in
           let ones = StringIntSet.fold (fun (b,_) -> fun l -> b::l) bs [] in
           let pairs = ordered_pairs ones in
           let pcs = List.map (fun (b,c) -> posEncode(H'(cfg,a,b,c,i,j))) pairs in
           message 3 (fun _ -> "  Creating ambiguity closure constraint  >> " ^ showVar(A(cfg,a,i,j,1,2)) ^ " -> " 
                               ^ String.concat " \\/ " (StringIntSet.fold 
                                                          (fun (b,n) -> fun l -> 
                                                             (showVar(A(cfg,b,i,j,0,3-n))) :: l) 
                                                          bs 
                                                          [])
                               ^ " \\/ " ^
                               String.concat " \\/ " (List.map (fun (b,c) -> showVar(H'(cfg,a,b,c,i,j))) pairs) 
                               ^ " <<\n    [ " ^ string_of_int nna ^ ", " ^ 
                               String.concat ", " (List.map string_of_int nbs) ^ ", " ^
                               String.concat ", " (List.map string_of_int pcs) ^ " ]\n");
           constraints := (Array.of_list (nna :: (nbs @ pcs))) :: !constraints;
           List.iter 
             (fun (b,c) -> 
                let nh = negEncode(H'(cfg,a,b,c,i,j)) in
                let nb = posEncode(A(cfg,b,i,j,0,1)) in
                let nc = posEncode(A(cfg,c,i,j,0,1)) in
                message 3 (fun _ -> "  Creating ambiguity closure constraint  >> " ^
                                    showVar(H'(cfg,a,b,c,i,j)) ^ " -> " ^ showVar(A(cfg,b,i,j,0,1)) ^ " <<\n    [ "
                                    ^ string_of_int nh ^ ", " ^ string_of_int nb ^ " ]\n");
                constraints := [| nh ; nb |] :: !constraints;
                message 3 (fun _ -> "  Creating ambiguity closure constraint  >> " ^
                                    showVar(H'(cfg,a,b,c,i,j)) ^ " -> " ^ showVar(A(cfg,c,i,j,0,1)) ^ " <<\n    [ "
                                    ^ string_of_int nh ^ ", " ^ string_of_int nc ^ " ]\n");
                constraints := [| nh ; nc |] :: !constraints)
             pairs)
        cfg.ambclosure;
    done
  done;

  !constraints 



let ambiguity_composition cfg lower_k upper_k =
  let constraints = ref [] in

  for i=0 to upper_k-1 do
    for j=max (i+1) lower_k to upper_k do
      List.iter 
        (fun a -> let rules = List.filter (function [_;_] -> true | _ -> false) (List.assoc a cfg.cfg) in
                  let constr = ref [ (negEncode(A(cfg,a,i,j,0,1)), "-" ^ showVar(A(cfg,a,i,j,0,1))) ] in
                  for h=i to j-1 do
                    constr := !constr @ (List.map 
                                 (function [Nonterminal b; Nonterminal c] ->
                                             let nhbc = negEncode(H(cfg,b,c,i,j,h)) in
                                             let nb = posEncode(A(cfg,b,i,h,1,1)) in
                                             let nc = posEncode(A(cfg,c,h+1,j,1,1)) in
                                             message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^
                                                                 showVar(H(cfg,b,c,i,j,h)) ^ " -> " ^ 
                                                                 showVar(A(cfg,b,i,h,1,1)) ^ " <<\n    [ " ^ 
                                                                 string_of_int nhbc ^ ", " ^ string_of_int nb ^ 
                                                                 " ]\n");  
                                             message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^
                                                                 showVar(H(cfg,b,c,i,j,h)) ^ " -> " ^ 
                                                                 showVar(A(cfg,c,h+1,j,1,1)) ^ " <<\n    [ " ^ 
                                                                 string_of_int nhbc ^ ", " ^ string_of_int nc ^ 
                                                                 " ]\n");  
                                             constraints := [| nhbc ; nb |] :: [| nhbc ; nc |] :: !constraints; 
                                             (posEncode(H(cfg,b,c,i,j,h)), showVar(H(cfg,b,c,i,j,h)))
                                         | _ -> raise Unexpected_rule)
                                 rules) 
                  done;
                  let ca = List.map fst !constr in
                  message 3 (fun _ -> let na = List.map snd !constr in
                                      "  Creating ambiguity composition constraint  >> " ^ 
                                      String.concat " \\/ " na ^ " <<\n    [ " ^ 
                                      String.concat ", " (List.map string_of_int ca) ^ "]\n");
                  constraints := (Array.of_list ca) :: !constraints;

                  message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^
                                      showVar(A(cfg,a,i,j,0,2)) ^ " -> " ^ showVar(C(cfg,a,i,j)) ^ " \\/ " ^
                                      String.concat " \\/ " (List.concat (List.map (function [Nonterminal b; Nonterminal c] -> List.map (fun h -> showVar(H12(cfg,b,c,i,j,h)) ^ " \\/ " ^ showVar(H21(cfg,b,c,i,j,h))) (range i (j-1)) | _ -> raise Unexpected_rule) rules))
                                      ^ " <<\n    [ " ^ string_of_int (negEncode(A(cfg,a,i,j,0,2))) ^ ", " ^
                                      String.concat ", " (List.concat (List.map (function [Nonterminal b; Nonterminal c] -> List.map (fun h -> string_of_int (posEncode(H12(cfg,b,c,i,j,h))) ^ ", " ^ string_of_int (posEncode(H21(cfg,b,c,i,j,h)))) (range i (j-1)) | _ -> raise Unexpected_rule) rules))
                                      ^ " ]\n");

                  let constr = ref [ negEncode(A(cfg,a,i,j,0,2)); posEncode(C(cfg,a,i,j)) ] in
                  for h=i to (j-1) do
                    List.iter (function [Nonterminal b; Nonterminal c] ->
                                           let nb = posEncode(H12(cfg,b,c,i,j,h)) in
                                           let nc = posEncode(H21(cfg,b,c,i,j,h)) in
                                           constr := nb :: nc :: !constr
                                         | _ -> raise Unexpected_rule)
                    rules
                  done;
                  constraints := (Array.of_list !constr) :: !constraints;

                  for h=i to j-1 do
                    List.iter (function [Nonterminal b; Nonterminal c] -> (
                                 let nhbc = negEncode(H12(cfg,b,c,i,j,h)) in
                                 let nb = posEncode(A(cfg,b,i,h,1,1)) in
                                 let nc = posEncode(A(cfg,c,h+1,j,1,2)) in
                                 message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^
                                                     showVar(H12(cfg,b,c,i,j,h)) ^ " -> " ^ showVar(A(cfg,b,i,h,1,1)) ^ 
                                                     " <<\n    [ " ^ string_of_int nhbc ^ ", " ^ string_of_int nb ^ 
                                                         " ]\n");  
                                 message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^
                                                     showVar(H12(cfg,b,c,i,j,h)) ^ " -> " ^ showVar(A(cfg,c,h+1,j,1,2)) ^ 
                                                     " <<\n    [ " ^ string_of_int nhbc ^ ", " ^ string_of_int nc ^ 
                                                     " ]\n");  
                                 constraints := [| nhbc ; nb |] :: [| nhbc ; nc |] :: !constraints; 
                                 let nhbc = negEncode(H21(cfg,b,c,i,j,h)) in
                                 let nb = posEncode(A(cfg,b,i,h,1,2)) in
                                 let nc = posEncode(A(cfg,c,h+1,j,1,1)) in
                                 message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^
                                                     showVar(H21(cfg,b,c,i,j,h)) ^ " -> " ^ showVar(A(cfg,b,i,h,1,2)) ^ 
                                                     " <<\n    [ " ^ string_of_int nhbc ^ ", " ^ string_of_int nb ^ 
                                                         " ]\n");  
                                 message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^
                                                     showVar(H21(cfg,b,c,i,j,h)) ^ " -> " ^ showVar(A(cfg,c,h+1,j,1,1)) ^ 
                                                     " <<\n    [ " ^ string_of_int nhbc ^ ", " ^ string_of_int nc ^ 
                                                     " ]\n");  
                                 constraints := [| nhbc ; nb |] :: [| nhbc ; nc |] :: !constraints) 
                                 | _ -> raise Unexpected_rule)
                               rules 
                  done;

		  constr := [ negEncode(C(cfg,a,i,j)) ];
                  let ns = ref [] in 
                  List.iter (function [Nonterminal b; Nonterminal c] -> (
                    List.iter (function [Nonterminal b'; Nonterminal c'] -> (
                      for h = i to j-1 do
                        for h' = i to j-1 do
			  if (b<>b' || c<>c' || h<>h') then (
			    constr := (posEncode(D(cfg,b,c,b',c',i,j,h,h'))) :: !constr;
                            ns := (showVar(D(cfg,b,c,b',c',i,j,h,h'))) :: !ns;
                            let nd = negEncode(D(cfg,b,c,b',c',i,j,h,h')) in
			    let py = posEncode(A(cfg,b,i,h,1,1)) in
			    message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^ 
                                                showVar(D(cfg,b,c,b',c',i,j,h,h')) ^ " -> " ^
                                                showVar(A(cfg,b,i,h,1,1)) ^ " <<\n    [ " ^ 
                                                string_of_int nd ^ ", " ^
                                                string_of_int py ^ " ]\n");
			    constraints := [| nd ; py |] :: !constraints;
			    let py = posEncode(A(cfg,c,h+1,j,1,1)) in
			    message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^ 
                                                showVar(D(cfg,b,c,b',c',i,j,h,h')) ^ " -> " ^
                                                showVar(A(cfg,c,h+1,j,1,1)) ^ " <<\n    [ " ^ 
                                                string_of_int nd ^ ", " ^
                                                string_of_int py ^ " ]\n");
			    constraints := [| nd ; py |] :: !constraints;
			    let py = posEncode(A(cfg,b',i,h',1,1)) in
			    message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^ 
                                                showVar(D(cfg,b,c,b',c',i,j,h,h')) ^ " -> " ^
                                                showVar(A(cfg,b',i,h',1,1)) ^ " <<\n    [ " ^ 
                                                string_of_int nd ^ ", " ^
                                                string_of_int py ^ " ]\n");
			    constraints := [| nd ; py |] :: !constraints;
			    let py = posEncode(A(cfg,c',h'+1,j,1,1)) in
			    message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^ 
                                                showVar(D(cfg,b,c,b',c',i,j,h,h')) ^ " -> " ^
                                                showVar(A(cfg,c',h'+1,j,1,1)) ^ " <<\n    [ " ^ 
                                                string_of_int nd ^ ", " ^
                                                string_of_int py ^ " ]\n");
			    constraints := [| nd ; py |] :: !constraints);
                        done           
		      done)
		      | _ -> raise Unexpected_rule) rules)
		    |_ -> raise Unexpected_rule) rules;
		  message 3 (fun _ -> "  Creating ambiguity composition constraint  >> " ^ showVar(C(cfg,a,i,j)) ^ " -> "
                                      ^ String.concat " \\/ " !ns ^ " <<\n    [ " ^ 
                                      String.concat ", " (List.map string_of_int !constr) ^ "]\n");
                  constraints := (Array.of_list !constr) :: !constraints)
        cfg.nonterminals
    done
  done;

  !constraints

 
*)
