(************************************************************
 *                                                          *
 * RXXR - Regular eXpression eXponential Runtime analyser   *
 *                                                          *
 * Copyright (C) 2012 University of Birmingham              *
 *                                                          *
 * All rights reserved.                                     *
 *                                                          *
 * For license conditions, see the file LICENSE.rtf.        *
 *                                                          *
 ***********************************************************)

open Data;;

(*
  streaming input reader
*)
type ireader = {next_line : unit -> string option};;

(*
  streaming regex reader
*)
type rreader = {next_regex : unit -> (string * regex option * string) option};;

(*
  create an ireader from a file source
*)
let make_ireader file_name =
  let rchannel = open_in file_name in
  let read_next_line = fun () ->
    try
      Some (Scanf.fscanf rchannel "%[^\r\n]\n" (fun x -> x))
    with
      End_of_file ->
        None in
  {next_line = read_next_line};;

(*
  create an rreader from an ireader
*)
let rec make_rreader reader = 
  let rec read_next_regex = fun () -> 
    match reader.next_line () with
      None ->
        None|
      Some s when (String.length s = 0) || (s.[0] = '#') -> (* skip comment / empty lines *)
        read_next_regex ()|
      Some s ->
        try
          let (r, _, _) = Parser.parse_thompson s in
          Some (s, Some r, "")
        with
          Lexer.LexicalError (msg) ->
            Some (s, None, msg)|
          Parser.SyntaxError (msg) ->
            Some (s, None, msg)|
          Parser.ParserError (msg) ->
            Some (s, None, msg) in
  {next_regex = read_next_regex};;

(*
  extract the sub-expression within the input string corresponding to the given regex node
*)
let subexp r s = String.sub s (meta r)#spos ((meta r)#epos - (meta r)#spos);;

(*
  return the continution of the given regex
*)
let kont r = match r with
  Kleene (_, _, _, k) -> !k|
  Atom (_, _, k) -> !k|
  Empty (_, k) -> !k|
  Anchor (_, _, k) -> !k|
  _ -> End;;

(*
  kleene vulnerability report
*)
type vreport = {nd : regex; sexp : string; pref : string; pump : string; suffix : string option};;

(*
  analyse the given list of kleene expressions and produce a summary of vulnerabilities (if found)
*)
let analyse klist s pbound sbound = 
  let ovflw = ref false in
  let suffd = ref false in
  try
    let vulns = List.fold_left (
      fun acc (r, pref) ->
        let (pump, ovflw') = Hf.search_kleene r pbound in
        let _ = ovflw := !ovflw || ovflw' in
        if pump <> [] then 
          let suffix = match Gen.derive_nomatch r pref sbound with
            None ->
              None|
            Some atms ->
              let _ = suffd := true in
              Some (Util.atoms_to_nice atms) in
          {nd = r; sexp = subexp r s; pref = Util.atoms_to_nice pref; pump = Util.atoms_to_nice pump; suffix = suffix} :: acc 
        else 
          acc
    ) [] klist in
    (Some (vulns, !ovflw, !suffd), "")
  with
    Hf.HfError msg ->
      (None, msg);;

(*
  scan a stream of regexes for exponential vulnerabilities (print all results)
*)
let scan_verbose reader pbound sbound = 
  let tbegin = Unix.gettimeofday () in
  let total = ref 0 in
  let parsable = ref 0 in
  let analysable = ref 0 in
  let vulnerable = ref 0 in
  let nvulnerable = ref 0 in
  let suffixed = ref 0 in
  let rec scan' () = match reader.next_regex () with
    None ->
      let elapsed = Unix.gettimeofday () -. tbegin in
      Printf.printf "Max search depth: %d, Time: %f (s), Total: %d, Parsable: %d, Analysable: %d, Vulnerable: %d, Suffixed: %d, Not Vulnerable: %d\n"
        pbound elapsed !total !parsable !analysable !vulnerable !suffixed !nvulnerable|
    Some (s, None, msg) ->
      let _ = total := !total + 1 in
      let _ = Printf.printf "=[%d]=\n- Regex: %s\n- Parse: Failed (%s)\n%!" !total s msg in
      scan' ()|
    Some (s, Some r, _) -> begin
      let _ = total := !total + 1 in
      let _ = parsable := !parsable + 1 in
      let _ = Printf.printf "=[%d]=\n- Regex: %s\n- Parse: Ok\n%!" !total s in
      let klns = Gen.find_reachable_kleene r in
      let _ = Printf.printf "- Kleene count: %d\n%!" (List.length klns) in
      let _ = match analyse klns s pbound sbound with
        (None, msg) ->
          Printf.printf "- Analysis: Failed (%s)\n" msg|
        (Some (vulns, ovflw, suffd), _) ->
          let _ = analysable := !analysable + 1 in
          let _ = Printf.printf "+ Analysis: Completed\n" in
          if (vulns = []) then
            let _ = Printf.printf "- Vulnerable: %s\n" (if ovflw then "Unknown (insufficient search depth)" else "No") in
            nvulnerable := if not ovflw then !nvulnerable + 1 else !nvulnerable
          else
            let _ = vulnerable := !vulnerable + 1 in
            let _ = suffixed := if suffd then !suffixed + 1 else !suffixed in
            let _ = Printf.printf "+ Vulnerable: Yes\n" in
            List.fold_left (
              fun u vuln ->
                Printf.printf "  + Kleene: %s\n    - Prefix: %s\n    - Pumpable: %s\n    - Suffix: %s\n" vuln.sexp vuln.pref vuln.pump (
                  match vuln.suffix with
                    None -> "(Not available)"|
                    Some suffix when suffix = "" -> "(The empty string)"|
                    Some suffix -> suffix
                )
            ) () vulns in
      scan' ()
    end in
  scan' ();;

(*
  scan a stream of regexes for exponential vulnerabilities (print just the statistics)
*)
let scan_stats reader pbound sbound = 
  let tbegin = Unix.gettimeofday () in
  let total = ref 0 in
  let parsable = ref 0 in
  let analysable = ref 0 in
  let vulnerable = ref 0 in
  let nvulnerable = ref 0 in
  let suffixed = ref 0 in
  let rec scan' () = match reader.next_regex () with
    None ->
      Printf.printf "%d, %f, %d, %d, %d, %d, %d, %d\n" pbound (Unix.gettimeofday () -. tbegin) !total !parsable !analysable !vulnerable !suffixed !nvulnerable|
    Some (s, None, msg) ->
      let _ = total := !total + 1 in
      scan' ()|
    Some (s, Some r, _) -> begin
      let _ = total := !total + 1 in
      let _ = parsable := !parsable + 1 in
      let klns = Gen.find_reachable_kleene r in
      let _ = match analyse klns s pbound sbound with
        (None, msg) -> ()|
        (Some (vulns, ovflw, suffd), _) ->
          let _ = analysable := !analysable + 1 in
          if (vulns = []) then
            nvulnerable := if not ovflw then !nvulnerable + 1 else !nvulnerable
          else
            let _ = vulnerable := !vulnerable + 1 in
            suffixed := if suffd then !suffixed + 1 else !suffixed in
      scan' ()
    end in
  scan' ();;          

(* entry point *)          
match Sys.argv with
  [|_; pbound; sbound; "-stats" ;finput|] -> begin
    try
      let ir = make_ireader finput in
      let pbound = Scanf.sscanf pbound "%d" (fun x -> x) in
      let sbound = Scanf.sscanf sbound "%d" (fun x -> x) in
      scan_stats (make_rreader ir) pbound sbound
    with
      Sys_error msg ->
        Printf.printf "%s\n" msg|
      Scanf.Scan_failure msg ->
        Printf.printf "%s\n" msg
  end|
  [|_; pbound; sbound; finput|] -> begin
    try
      let ir = make_ireader finput in
      let pbound = Scanf.sscanf pbound "%d" (fun x -> x) in
      let sbound = Scanf.sscanf sbound "%d" (fun x -> x) in
      scan_verbose (make_rreader ir) pbound sbound
    with
      Sys_error msg ->
        Printf.printf "%s\n" msg|
      Scanf.Scan_failure msg ->
        Printf.printf "%s\n" msg
  end|
  _->
   Printf.printf "USAGE: wdp pbound sbound [-stats] finput\n";;
