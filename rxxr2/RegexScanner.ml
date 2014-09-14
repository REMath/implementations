(* © Copyright University of Birmingham, UK *)

type result =
  |Eof
  |Error of exn * string
  |Regex of Nfa.t * string;;

type t = unit -> result;;

(* initialize a line-by-line reader on the input file *)
let make_line_reader fname =
  let in_channel = open_in fname in
  let closed = ref false in
  fun () ->
    if !closed then
      None
    else
      try
        Some (Scanf.fscanf in_channel "%[^\r\n]\n" (fun x -> x))
      with
        End_of_file ->
          close_in_noerr in_channel;
          closed := true;
          None;;

let make fname =
  let read_line = make_line_reader fname in
  let rec read_regex () = match read_line () with
    |None -> Eof
    |Some s when (String.length s = 0) || (s.[0] = '#') -> read_regex () (* skip comments / empty lines *)
    |Some s ->
      try
        let lexbuf = Lexing.from_string (Printf.sprintf "%s\n" s) in
        let p = ParsingMain.parse_pattern lexbuf in
        let nfa = Nfa.make p in
        Regex (nfa, s)
      with e -> Error (e, s) in
  read_regex;;

let next f = f ();;
