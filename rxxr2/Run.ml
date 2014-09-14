(* © Copyright University of Birmingham, UK *)

open ParsingData
open Nfa
open Common

let rec print_exp e = match e with
  |Zero -> Printf.sprintf "\\0"
  |One -> Printf.sprintf "\\1"
  |Dot -> Printf.sprintf "."
  |Pred(Bol) -> Printf.sprintf "\\p(^)"
  |Pred(Eol) -> Printf.sprintf "\\p($)"
  |Pred(Wordb) -> Printf.sprintf "\\p(b)"
  |Pred(NWordb) -> Printf.sprintf "\\p(B)"
  |Pred(Boi) -> Printf.sprintf "\\p(A)"
  |Pred(Eom) -> Printf.sprintf "\\p(G)"
  |Pred(Eoi1) -> Printf.sprintf "\\p(Z)"
  |Pred(Eoi2) -> Printf.sprintf "\\p(z)"
  |Atom(Char c) -> zprint c
  |Atom(Cls cls) -> cls_print cls
  |Group(CAP(_), _, _, r) -> Printf.sprintf "(%s)" (print_exp (fst r))
  |Backref(i) -> Printf.sprintf "(?:\\%d)" i
  |Group(MODS, m_on, m_off, _) -> Printf.sprintf "(?%d-%d)" m_on m_off
  |Group(NOCAP, m_on, m_off, r) -> Printf.sprintf "(?%d-%d:%s)" m_on m_off (print_exp (fst r))
  |Group(PLA, _, _, r) -> Printf.sprintf "(?=%s)" (print_exp (fst r))
  |Group(NLA, _, _, r) -> Printf.sprintf "(?!%s)" (print_exp (fst r))
  |Group(PLB, _, _, r) -> Printf.sprintf "(?<=%s)" (print_exp (fst r))
  |Group(NLB, _, _, r) -> Printf.sprintf "(?<!%s)" (print_exp (fst r))
  |Group(ATOMIC, _, _, r) -> Printf.sprintf "(?>%s)" (print_exp (fst r))
  |Conc(r1, r2) -> Printf.sprintf "%s%s" (print_exp (fst r1)) (print_exp (fst r2))
  |Alt(r1, r2) -> Printf.sprintf "(%s|%s)" (print_exp (fst r1)) (print_exp (fst r2))
  |Kleene(Gq, r1) -> Printf.sprintf "%s*" (print_exp (fst r1))
  |Kleene(Rq, r1) -> Printf.sprintf "%s*?" (print_exp (fst r1));;

let print_regex r = Printf.sprintf "%s" (print_exp (fst r));;

let print_pattern p = Printf.printf "/%s/%d\n" (print_regex (fst p)) (snd p);;

let print_nfa nfa =
  let _ = Printf.printf "= (root: %d) =\n" (Nfa.root nfa) in
  let print_state s = match s with
    |End -> "END"
    |Kill -> "KILL"
    |Pass i -> Printf.sprintf "PASS, %d" i
    |Match (cls, i) -> Printf.sprintf "MATCH %s, %d" (cls_print cls) i
    |CheckPred (P_BOL ul, i) -> Printf.sprintf "P(BOL, %B), %d" ul i
    |CheckPred (P_EOL ul, i) -> Printf.sprintf "P(EOL, %B), %d" ul i
    |CheckPred (P_WB, i) -> Printf.sprintf "P(WB), %d" i
    |CheckPred (P_NWB, i) -> Printf.sprintf "P(NWB), %d" i
    |CheckPred (P_BOI, i) -> Printf.sprintf "P(BOI), %d" i
    |CheckPred (P_EOM, i) -> Printf.sprintf "P(EOM), %d" i
    |CheckPred (P_EOI, i) -> Printf.sprintf "P(EOI), %d" i
    |CheckPred (P_EOIX ul, i) -> Printf.sprintf "P(EOIX, %B), %d" ul i
    |CheckBackref (i, j) -> Printf.sprintf "\\%d, %d" i j
    |BeginCap (i, j) -> Printf.sprintf "BEGIN_CAP %d, %d" i j
    |EndCap (i, j) -> Printf.sprintf "END_CAP %d, %d" i j
    |BranchAlt (i, j) -> Printf.sprintf "ALT (%d|%d)" i j
    |MakeB (i) -> Printf.sprintf "MAKE_B, %d" i
    |EvalB (i) -> Printf.sprintf "EVAL_B, %d" i
    |BranchKln (true, i, j) -> Printf.sprintf "KLN_G (%d|%d)" i j
    |BranchKln (false, i, j) -> Printf.sprintf "KLN_R (%d|%d)" i j in
  let rec print_states i = 
    if i == Nfa.size nfa then () else
      let _ = Printf.printf "%d: %s\n" i (print_state (Nfa.get_state nfa i)) in
      print_states (i + 1) in
  print_states 0;;

let print_flags f =
  let s = if Flags.is_interrupted f then "INTERRUPTED, " else "" in
  if Flags.is_pruned f then Printf.sprintf "%sPRUNED" s else s;;

let std_scan slim =
  while true do
    let lexbuf = Lexing.from_channel stdin in
    let p = ParsingMain.parse_pattern lexbuf in
    let nfa = Nfa.make p in
(*
    let _ = print_nfa nfa in
    print_newline ();
*)
    Printf.printf "= Analysis =\n%!";
    AnalyserMain.enumerate_verbose nfa;

(*
    begin
      (*match AnalyserMain.search_exhaustive nfa with*)
      let ts = Unix.gettimeofday () in
      match AnalyserMain.search_optimized nfa slim with
        |(f, _, None) -> Printf.printf "None.\nF : {%s}\nT : %f (s)\n" (print_flags f) (Unix.gettimeofday () -. ts)
        |(f, _, Some (ik, x, y, z)) -> Printf.printf "KLEENE: %d\nPREFIX : %s\nPUMPABLE : %s\nSUFFIX : %s\nFLAGS : {%s}\nTIME : %f (s)\n"
          ik (Word.print x) (Word.print y) (Word.print z) (print_flags f) (Unix.gettimeofday () -. ts)
    end;
*)
    print_newline ();
    flush stdout
  done;;

let batch_scan fname zlim =
  let rs = RegexScanner.make fname in
  let c_total = ref 0 in
  let c_parsed = ref 0 in
  let c_pumpable = ref 0 in
  let c_vulnerable = ref 0 in
  let c_interrupted = ref 0 in
  let c_pruned = ref 0 in
  let t_total = ref 0.0 in
  let t_max = ref 0.0 in
  let s_max = ref 0 in
  let s_total = ref 0 in
  let rec scan () = match RegexScanner.next rs with
    |RegexScanner.Eof ->
      Printf.printf ">> TOTAL: %d\n" !c_total;
      Printf.printf ">> PARSED: %d\n" !c_parsed;
      Printf.printf ">> MAX NFA SIZE: %d\n" !s_max;
      Printf.printf ">> AVG NFA SIZE: %d\n" (!s_total / !c_parsed);
      Printf.printf ">> PUMPABLE: %d\n" !c_pumpable;
      Printf.printf ">> VULNERABLE: %d\n" !c_vulnerable;
      Printf.printf ">> INTERRUPTED: %d\n" !c_interrupted;
      Printf.printf ">> PRUNED: %d\n" !c_pruned;
      Printf.printf ">> TIME TOTAL: %f (s)\n" !t_total;
      Printf.printf ">> TIME MAX: %f (s)\n" !t_max;
    |RegexScanner.Error (e, s) ->
      c_total := !c_total + 1;
      Printf.printf "= [%d] =\n" !c_total;
      Printf.printf "INPUT: %s\n" s;
      Printf.printf "PARSE: ERROR {%s}\n%!" (Printexc.to_string e);
      scan ()
    |RegexScanner.Regex (nfa, s) ->
      c_total := !c_total + 1;
      c_parsed := !c_parsed + 1;
      s_total := !s_total + (Nfa.size nfa);
      s_max := if (Nfa.size nfa > !s_max) then (Nfa.size nfa) else !s_max;
      Printf.printf "= [%d] =\n" !c_total;
      Printf.printf "INPUT: %s\n" s;
      Printf.printf "PARSE: OK\n";
      Printf.printf "SIZE: %d\n%!" (Nfa.size nfa);
      begin
        let ts = Unix.gettimeofday () in
        match AnalyserMain.search_optimized nfa zlim with
          |(f, kset, None) ->
            let t_this = Unix.gettimeofday () -. ts in
            let _ = if IntSet.is_empty kset then (
              Printf.printf "PUMPABLE: NO\n"
            ) else (
              c_pumpable := !c_pumpable + 1;
              Printf.printf "PUMPABLE: YES\n";
              Printf.printf "VULNERABLE: NO {%s}\n" (print_flags f)
            ) in
            c_interrupted := if Flags.is_interrupted f then !c_interrupted + 1 else !c_interrupted;
            c_pruned := if Flags.is_pruned f then !c_pruned + 1 else !c_pruned;
            t_total := !t_total +. t_this;
            t_max := if t_this > !t_max then t_this else !t_max;
            Printf.printf "TIME: %f (s)\n" t_this
          |(f, _, Some (ik, x, y, z)) ->
            c_pumpable := !c_pumpable + 1;
            c_vulnerable := !c_vulnerable + 1;
            c_pruned := if Flags.is_pruned f then !c_pruned + 1 else !c_pruned;
            Printf.printf "PUMPABLE: YES\n";
            Printf.printf "VULNERABLE: YES {%s}\n" (print_flags f);
            Printf.printf "KLEENE: %s\n" (let (i, j) = Nfa.get_subexp_location nfa ik in String.sub s (i + 1) (j - i + 1));
            Printf.printf "PREFIX: %s\n" (Word.print x);
            Printf.printf "PUMPABLE: %s\n" (Word.print y);
            Printf.printf "SUFFIX: %s\n" (Word.print z);
            Printf.printf "TIME: %f (s)\n" (Unix.gettimeofday () -. ts)
      end;
      scan () in
  scan ();;

let snort_scan fname slim qmode =
  let rs = RuleScanner.make fname in
  let total_regexes = ref 0 in
  let analysed_regexes = ref 0 in
  let vulnerable_regexes = ref 0 in
  let unknown_regexes = ref 0 in
  let current_file = ref "" in
  let rec scan () = match RuleScanner.next rs with
    |None -> Printf.printf "TOTAL: %d\nANALYSED: %d\nVULNERABLE: %d\nUNKNOWN: %d\n" !total_regexes !analysed_regexes !vulnerable_regexes !unknown_regexes
    |Some (file, line, regex_string) ->
      total_regexes := !total_regexes + 1;
      if (!current_file != file) then (
        current_file := file;
        Printf.printf "Processing file: %s\n" file
      );
      let lexbuf = Lexing.from_string (Printf.sprintf "%s\n" regex_string) in
      try
        let p = ParsingMain.parse_pattern lexbuf in
        let nfa = Nfa.make p in
        begin
          match AnalyserMain.search_optimized nfa slim with
            |(f, _, None) when (Flags.is_empty f) -> ()
            |(f, _, None) ->
              unknown_regexes := !unknown_regexes + 1;
              Printf.printf "Line: %d, Flags : {%s}\n%!" line (print_flags f)
            |(f, _, Some (ik, x, y, z)) -> 
              vulnerable_regexes := !vulnerable_regexes + 1;
              let (ks, ke) = Nfa.get_subexp_location nfa ik in
              Printf.printf "Line: %d\n  KLEENE: %s\n  PREFIX : %s\n  PUMPABLE : %s\n  SUFFIX : %s\n  FLAGS : {%s}\n%!"
                line (String.sub regex_string (ks + 1) (ke - ks + 1)) (Word.print x) (Word.print y) (Word.print z) (print_flags f)
        end;
        analysed_regexes := !analysed_regexes + 1;
        scan ()
      with e ->
        unknown_regexes := !unknown_regexes + 1;
        if not qmode then Printf.printf "Line: %d, Parsing error (%s)\n%!" line (Printexc.to_string e);
        scan () in
  scan ();;

let slim = ref 100 in (* default z search limit, rarely touched *)
let input_file = ref None in
let snort_mode = ref false in
let quiet_mode = ref false in
let spec = Arg.align [("-slim", Arg.Int (fun i -> if i > 1 then slim := i), "<n> Abandon current search path after this many unstable xy derivations");
            ("-i", Arg.String (fun s -> input_file := Some s), "<file> Analyse regular expressions from this input file");
            ("-q", Arg.Unit (fun () -> quiet_mode := true), " Quiet mode (hide parsing erros)");
            ("-snort", Arg.Unit (fun () -> snort_mode := true), " Snort rule processing mode (use -i to specify the rules file / directory)")] in
let message = "USAGE: run.bin [-slim n] [-i file] [-snort]" in
let _ = Arg.parse spec (fun s -> ()) message in
match !input_file with
  |Some f when !snort_mode -> snort_scan f !slim !quiet_mode 
  |Some f -> batch_scan f !slim
  |None -> 
    if !snort_mode then
      Arg.usage spec message
    else
      std_scan !slim;; 
