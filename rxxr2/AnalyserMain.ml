(* © Copyright University of Birmingham, UK *)

open Common

let enumerate_verbose nfa =
  (* find all pumpable kleene and the corresponding branch points *)
  let ktbl = Util.find_pumpable_kleene nfa in
  (* form the set of pumpable kleene *)
  let kset = Hashtbl.fold (fun k _ s -> IntSet.add k s) ktbl IntSet.empty in
  (* function for searching z *)
  let search_z (lead, y2p) kont =
    let zs = ZAnalyser.init (nfa, lead, y2p) in
    let rec explore () = match ZAnalyser.next zs with
      |None -> kont () (* exhausted, invoke continuation *)
      |Some (z, zp) -> (
        Printf.printf "> Z  : (%s) : {%s}\n%!" (Word.print z) (Phi.print zp);
        explore ()
      ) in
    explore () in
  (* function for searching y2 *)
  let search_y2 ik (lead, y1_tpl) xp kont =
    let y2s = Y2Analyser.init (nfa, lead, y1_tpl) ik in
    let rec explore () = match Y2Analyser.next y2s with
      |None -> kont () (* exhausted, invoke continuation *)
      |Some (y2, y2p) -> (
        Printf.printf "> Y2 : (%s) : <%d, {%s}>\n%!" (Word.print y2) ik (Phi.print y2p);
        (* check inclusion *)
        if Phi.subset y2p xp then
          (* search z with a fallback to self *)
          search_z (Word.append lead y2, y2p) explore
        else explore ()
      ) in
    explore () in
  (* function for searching y1 *)
  let search_y1 ik (lead, xp) kont =
    let y1s = Y1Analyser.init (nfa, lead, xp) (ik, (Hashtbl.find ktbl ik)) in
    let rec explore () = match Y1Analyser.next y1s with
      |None -> kont () (* exhausted, invoke continuation *)
      |Some (y1, y1_tpl) -> (
        let (i, j, y1p) = Triple.elems y1_tpl in
        Printf.printf "> Y1 : (%s) : <%d, %d, {%s}>\n%!" (Word.print y1) i j (Phi.print y1p);
        (* search y2 with a fallback to self *)
        search_y2 ik (Word.append lead y1, y1_tpl) xp explore;
      ) in
    explore () in
  (* function for searching x *)
  let search_x () =
    let xs = XAnalyser.init nfa kset in
    let rec explore () = match XAnalyser.next xs with
      |None -> Printf.printf "Done.\n%!"
      |Some (ik, x, xp) -> (
        Printf.printf "Kleene: %d\n> X : (%s) : [%s]\n%!" ik (Word.print x) (Phi.print xp);
        (* search y1 with a fallback to self *)
        search_y1 ik (x, xp) explore;
      ) in
    explore () in
  if not (IntSet.is_empty kset) then search_x () else Printf.printf "Done.\n%!";;

let search_exhaustive nfa =
  (* find all pumpable kleene and the corresponding branch points *)
  let ktbl = Util.find_pumpable_kleene nfa in
  (* form the set of pumpable kleene *)
  let kset = Hashtbl.fold (fun k _ s -> IntSet.add k s) ktbl IntSet.empty in
  (* function for searching z *)
  let search_z (x, y, y2p) kont =
    let zs = ZAnalyser.init (nfa, Word.append x y, y2p) in
    let rec explore () = match ZAnalyser.next zs with
      |None -> kont () (* exhausted, invoke continuation *)
      |Some (z, zp) -> Some (x, y, z) in
    explore () in
  (* function for searching y2 *)
  let search_y2 ik (x, y1, y1_tpl) xp kont =
    let y2s = Y2Analyser.init (nfa, Word.append x y1, y1_tpl) ik in
    let rec explore () = match Y2Analyser.next y2s with
      |None -> kont () (* exhausted, invoke continuation *)
      |Some (y2, y2p) ->
        (* check inclusion *) 
        if Phi.subset y2p xp then
          (* search z with a fallback to self *)
          search_z (x, Word.append y1 y2, y2p) explore
        else explore () in
    explore () in
  (* function for searching y1 *)
  let search_y1 ik (x, xp) kont =
    let y1s = Y1Analyser.init (nfa, x, xp) (ik, (Hashtbl.find ktbl ik)) in
    let rec explore () = match Y1Analyser.next y1s with
      |None -> kont () (* exhausted, invoke continuation *)
      |Some (y1, y1_tpl) ->
        (* search y2 with a fallback to self *)
        search_y2 ik (x, y1, y1_tpl) xp explore in
    explore () in
  (* function for searching x *)
  let search_x () =
    let xs = XAnalyser.init nfa kset in
    let rec explore () = match XAnalyser.next xs with
      |None -> None
      |Some (ik, x, xp) ->
        (* search y1 with a fallback to self *)
        search_y1 ik (x, xp) explore in
    explore () in
  if not (IntSet.is_empty kset) then search_x () else None;;

(* checks if the phi p is stable under the word y *)
let is_saturated (nfa, y, p) =
  let pumpable = Word.select y in
  let (_, _, p2) = Phi.simulate (nfa, y, p) pumpable in
  Phi.subset p2 p;;

(* eliminate obviously non-vulnerable kleene states *)
let eliminate_non_vulnerable nfa kpumpable =
  IntSet.fold (fun ik s ->
    let p = Phi.make (IntSet.singleton ik) in
    let zs = ZAnalyser.init (nfa, Word.empty, p) in
    match ZAnalyser.next zs with
      |None -> s 
      |Some _ -> IntSet.add ik s
  ) kpumpable IntSet.empty;;

let search_optimized nfa slim =
  (* find all pumpable kleene and the corresponding branch points *)
  let ktbl = Util.find_pumpable_kleene nfa in
  (* form the set of pumpable kleene *)
  let kpumpable = Hashtbl.fold (fun k _ s -> IntSet.add k s) ktbl IntSet.empty in
  (* filter out non-vulenrable kleene *)
  let kanalyse = eliminate_non_vulnerable nfa kpumpable in
  let flgs = ref Flags.empty in
  (* function for searching z *)
  let search_z ik (x, y, y2p) kont =
    let zs = ZAnalyser.init (nfa, Word.append x y, y2p) in
    let rec explore () = match ZAnalyser.next zs with
      |None -> 
        flgs := Flags.union (ZAnalyser.flags zs) !flgs;
        kont () (* exhausted, invoke continuation *)
      |Some (z, zp) -> (!flgs, kpumpable, Some (ik, x, y, z)) in
    explore () in
  (* function for searching y2 *)
  let search_y2 ik (x, y1, y1_tpl) xp kont =
    let y2s = Y2Analyser.init (nfa, Word.append x y1, y1_tpl) ik in
    (* number of unstable derivations *)
    let sfails = ref 0 in
    let rec explore () = match Y2Analyser.next y2s with
      |None ->
        flgs := Flags.union (Y2Analyser.flags y2s) !flgs;
        kont () (* exhausted, invoke continuation *)
      |Some (y2, y2p) ->
        let y = Word.append y1 y2 in
        (* check inclusion or extended inclusion *)
        if (Phi.subset y2p xp || is_saturated (nfa, y, y2p)) then (
          (* stable derivation, reset counter *)
          sfails := 0;
          (* search z with a fallback to self *)
          search_z ik (x, y, y2p) explore
        ) else (
          (* one more unstable derivations *)
          sfails := !sfails + 1;
          if !sfails > slim then (
            (* too many unstable derivations *)
            flgs := Flags.set_pruned !flgs;
            (* give up on this y2 *)
            kont ()
          ) else explore () (* try one more y2 *)
        ) in
    explore () in
  (* function for searching y1 *)
  let search_y1 ik (x, xp) kont =
    let y1s = Y1Analyser.init (nfa, x, xp) (ik, (Hashtbl.find ktbl ik)) in
    let rec explore () = match Y1Analyser.next y1s with
      |None ->
        flgs := Flags.union (Y1Analyser.flags y1s) !flgs;
        kont () (* exhausted, invoke continuation *)
      |Some (y1, y1_tpl) -> 
        (* search y2 with a fallback to self *)
        search_y2 ik (x, y1, y1_tpl) xp explore in
    explore () in
  (* function for searching x *)
  let search_x () =
    let xs = XAnalyser.init nfa kanalyse in
    let rec explore () = match XAnalyser.next xs with
      |None ->
        flgs := Flags.union (XAnalyser.flags xs) !flgs;
        (* completed, no attack strings found *)
        (!flgs, kpumpable, None) 
      |Some (ik, x, xp) ->
        (* search y1 with a fallback to self *)
        search_y1 ik (x, xp) explore in
    explore () in
  if not (IntSet.is_empty kanalyse) then search_x () else (!flgs, kpumpable, None);;
