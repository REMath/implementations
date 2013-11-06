open Basics ;;
open Coding ;;
open Cfg ;;
open Zchaff ;;
open Varencoding ;;
open Dotty ;;
(* open Parsetree ;;
open Latex ;; *)

type constraintMaker = int -> int -> constraints

type formalParameter = UpperBound
                     | LowerBound
                     | Null

type problem = { permanent : constraintMaker list;
                 temporary : constraintMaker list;
                 negativeReport : int -> int -> string;
                 positiveReport : int -> int -> string
}


let showWord = String.concat ""

let extractWord alphabet j =
  List.map 
    (fun h -> try
                List.find (fun t -> 1 = zchaff_GetVarAsgnment zchaff (posEncode(T(t,h)))) 
                          alphabet
              with Not_found -> failwith ("No terminal symbol in position " ^ string_of_int h ^ 
                                            ". How absurd!\n")) 
    (range 0 j)


let dummyProblem _ = {
  permanent = [] ;
  temporary = [] ;
  negativeReport = (fun _ -> fun _ -> "") ;
  positiveReport = (fun _ -> fun _ -> "") 
  }


let emptiness cfgs = 
  let cfg = List.hd cfgs in
  let retrieve lower_k upper_k =
    let j = List.find (fun h -> 1 = getValue(N(cfg,cfg.start,0,h))) 
                      (range lower_k upper_k) 
    in
    extractWord cfg.alphabet j
  in 
  {
  permanent = [ (unique_symbols cfg.alphabet) ;
                (composition_topdown cfg) ] ;
  temporary = [ (derivable cfg) ] ;
  negativeReport = (fun lower -> fun upper -> 
                      "L(G1) does not contain any word of length k with " ^ string_of_int (lower+1) ^ " <= k <= " 
                      ^ string_of_int (upper+1) ^ ".\n") ; 
  positiveReport = (fun lower -> fun upper ->
                      let word = retrieve lower upper in
                      let k = List.length word in
                      if !writeOutput 
                      then (let o = try
                                      open_out !outputFile
                                    with _ -> failwith ("Cannot open file \"" ^ !outputFile ^ "\" for writing!")
                            in
                            output_string o dottyParseTreeHeader;
                            output_string o (dottyWord cfg.alphabet k);
                            output_string o (dottyParseTree cfg k);
                            output_string o dottyParseTreeFooter;
                            close_out o);
                      "A word in L(G1) is, e.g., \"" ^ showWord word ^ "\" of length " ^ string_of_int k ^ "\n") 
  }


let universality cfgs = 
  let cfg = List.hd cfgs in
  let retrieve lower_k upper_k =
    let j = List.find (fun h -> 0 = getValue(N(cfg,cfg.start,0,h))) 
                      (range lower_k upper_k) 
    in
    extractWord cfg.alphabet j
  in
  {
  permanent = [ (unique_symbols cfg.alphabet) ;
                (composition_bottomup cfg) ] ;
  temporary = [ (underivable cfg) ] ;
  negativeReport = (fun lower -> fun upper -> 
                      "L(G1) contains every word of length k with " ^ string_of_int (lower+1) ^ " <= k <= " ^ 
                      string_of_int (upper+1) ^ ".\n") ; 
  positiveReport = (fun lower -> fun upper ->
                      let word = retrieve lower upper in
                      let k = List.length word in
                      if !writeOutput 
                      then (let o = try
                                      open_out !outputFile
                                    with _ -> failwith ("Cannot open file \"" ^ !outputFile ^ "\" for writing!")
                            in
                            output_string o dottyParseTreeHeader;
                            output_string o (dottyWord cfg.alphabet k);
                            output_string o (dottyParseTree cfg k);
                            output_string o dottyParseTreeFooter;
                            close_out o);
                      "A word not in L(G1) is, e.g., \"" ^ showWord word ^ "\" of length " ^ 
                      string_of_int (List.length word) ^ "\n")
  }


let mergeAlphabets alphs =
  let makeSet = List.fold_left (fun s -> fun x -> StringSet.add x s) StringSet.empty in
  StringSet.elements (List.fold_left (fun s -> fun s' -> StringSet.union s s') 
                                     StringSet.empty 
                                     (List.map makeSet alphs))

  
let inclusion cfgs =
  let cfg1 = List.hd cfgs in
  let cfg2 = List.hd (List.tl cfgs) in
  let alphabet = mergeAlphabets [cfg1.alphabet; cfg2.alphabet] in
  let retrieve lower_k upper_k =
    let j = List.find (fun h -> 1 = getValue(B(h))) 
                      (range lower_k upper_k) 
    in
    extractWord cfg1.alphabet j
  in {
  permanent = [ (unique_symbols alphabet) ;
                (composition_topdown cfg1) ;
                (composition_bottomup cfg2) ;
                (derives_one_but_not_the_other_implications cfg1 cfg2) ] ;
  temporary = [ (derives_one_but_not_the_other) ] ;
  negativeReport = (fun lower -> fun upper -> 
                      "L(G1) is included in L(G2) when restricted to words of length k with " ^ 
                      string_of_int (lower+1) ^ " <= k <= " ^ string_of_int (upper+1) ^ ".\n") ; 
  positiveReport = (fun lower -> fun upper ->
                      let word = retrieve lower upper in
                      let k = List.length word in
                      if !writeOutput 
                      then (let o = try
                                      open_out !outputFile
                                    with _ -> failwith ("Cannot open file \"" ^ !outputFile ^ "\" for writing!")
                            in
                            output_string o dottyParseTreeHeader;
                            output_string o (dottyWord alphabet k);
                            output_string o (dottyParseTree cfg1 k);
                            output_string o (dottyParseTree cfg2 k);
                            output_string o dottyParseTreeFooter;
                            close_out o);
                      "A word in L(G1)-L(G2) is, e.g., \"" ^ showWord word ^ "\" of length " ^ 
                      string_of_int (List.length word) ^ "\n")
  }


let equivalence cfgs =
  let cfg1 = List.hd cfgs in
  let cfg2 = List.hd (List.tl cfgs) in
  let alphabet = mergeAlphabets [cfg1.alphabet; cfg2.alphabet] in
  let retrieve lower_k upper_k =
    let (j,b,b') = List.find 
                     (fun (h,b,b') -> b=1 || b'=1)  
                     (List.map (fun h -> (h, getValue(B(h)), getValue(B'(h)))) (range lower_k upper_k)) 
    in
    (extractWord cfg1.alphabet j,b-b')
  in {
  permanent = [ (unique_symbols alphabet) ;
                (composition_topdown cfg1) ;
                (composition_topdown cfg2) ;
                (composition_bottomup cfg1) ;
                (composition_bottomup cfg2) ;
                (derives_exactly_one_implications cfg1 cfg2) ] ;
  temporary = [ (derives_exactly_one) ] ;
  negativeReport = (fun lower -> fun upper -> 
                      "L(G1) and L(G2) agree when restricted to words of length k with " ^ 
                      string_of_int (lower+1) ^ " <= k <= " ^ string_of_int (upper+1) ^ ".\n") ; 
  positiveReport = (fun lower -> fun upper ->
                      let (word,d) = retrieve lower upper in
                      let k = List.length word in
                      if !writeOutput 
                      then (let o = try
                                      open_out !outputFile
                                    with _ -> failwith ("Cannot open file \"" ^ !outputFile ^ "\" for writing!")
                            in
                            output_string o dottyParseTreeHeader;
                            output_string o (dottyWord alphabet k);
                            output_string o (dottyParseTree cfg1 k);
                            output_string o (dottyParseTree cfg2 k);
                            output_string o dottyParseTreeFooter;
                            close_out o);
                      "A word in " ^ 
                      (match d with
                             1  -> "L(G1)-L(G2)"
		           | -1 -> "L(G2)-L(G1)"
			   | _  -> failwith "Equivalence check yields inconsistent answer!")
                      ^ " is, e.g., \"" ^ showWord word ^ "\" of length " ^ string_of_int (List.length word) ^ "\n")
  }


let intersection cfgs =
  let cfg = List.hd cfgs in
  let l = List.length cfgs in
  let retrieve lower_k upper_k =
    let j = List.find (fun h -> 1 = getValue(B(h))) 
                      (range lower_k upper_k) 
    in
    extractWord cfg.alphabet j
  in {
  permanent = (all_derivable_implications cfgs) :: 
              (unique_symbols (mergeAlphabets (List.map (fun cfg -> cfg.alphabet) cfgs))) ::
              (List.concat (List.map (fun cfg -> [ composition_topdown cfg ]) cfgs)) ;
  temporary = [ (all_derivable) ] ;
  negativeReport = (fun lower -> fun upper -> 
                      "The intersection of L(G1) ... L(G" ^ string_of_int l ^ ") is empty when restricted " ^
                      " to words of length k with " ^ string_of_int (lower+1) ^ " <= k <= " ^ 
                      string_of_int (upper+1) ^ ".\n") ; 
  positiveReport = (fun lower -> fun upper ->
                      let word = retrieve lower upper in
                      let k = List.length word in
                      if !writeOutput 
                      then (let o = try
                                      open_out !outputFile
                                    with _ -> failwith ("Cannot open file \"" ^ !outputFile ^ "\" for writing!")
                            in
                            output_string o dottyParseTreeHeader;
                            output_string o (dottyWord cfg.alphabet k);
                            List.iter (fun cfg -> output_string o (dottyParseTree cfg k)) cfgs;
                            output_string o dottyParseTreeFooter;
                            close_out o);
                      "A word in the intersection of L(G1) ... L(G" ^ string_of_int l ^ ") is, e.g., \"" ^ 
                      showWord word ^ "\" of length " ^ string_of_int (List.length word) ^ "\n")
  }


let ambiguity cfgs =
  let cfg = List.hd cfgs in
  let retrieve lower_k upper_k =
    let ns = ref cfg.nonterminals in
    let n = ref "" in
    let j = ref (-1) in
    
    while !ns <> [] && !j = (-1) do
      n := List.hd !ns;
      ns := List.tl !ns;

      j := try
             List.find (fun h -> let r = number_of_productions cfg !n in
                                 let var = if StringSet.mem !n cfg.ambnonterminals 
                                           then N(cfg,!n,0,h)
                                           else Two(!n,h,r)
                                 in 1 = getValue(var)) 
                       (range lower_k upper_k)
           with Not_found -> (-1)
    done;
    if !j = (-1) then failwith "No reason for ambiguity found!";
    (!n, extractWord cfg.alphabet !j)
  in 
  {
  permanent = [ (unique_symbols cfg.alphabet) ;
                (composition_topdown cfg) ] ;
  temporary = [ (two_productions cfg) ] ;
  negativeReport = (fun lower -> fun upper -> 
                      "L(G1) does not contain a word with an ambiguous subword of length k with " ^ string_of_int (lower+1) ^ 
                      " <= k <= " ^ string_of_int (upper+1) ^ ".\n") ; 
  positiveReport = (fun lower -> fun upper ->
                      let (n,word) = retrieve lower upper in
                      let k = List.length word in
                      if !writeOutput 
                      then (let o = try
                                      open_out !outputFile
                                    with _ -> failwith ("Cannot open file \"" ^ !outputFile ^ "\" for writing!")
                            in
                            output_string o dottyParseTreeHeader;
                            output_string o (dottyWord cfg.alphabet k);
                            output_string o (dottyParseTree cfg k);
                            output_string o dottyParseTreeFooter;
                            close_out o);
                      "An ambiguous subword of a word in L(G1) is, e.g., \"" ^ showWord word ^ "\" of length " ^ 
                      string_of_int (List.length word) ^ " derived from nonterminal " ^ n ^ "\n")
  }

