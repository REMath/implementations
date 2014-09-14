type t = {mutable current_file : string; mutable next_regex : unit -> (int * string) option; mutable file_stack : string list};;

let make s = {current_file = s; next_regex = (fun () -> None); file_stack = [s]};;

let rule_file_filter = Str.regexp ".*[.]rules$";;
let pcre_regex_filter = Str.regexp ".*pcre[ \t]*:[ \t]*\"\\([^\"]*\\)\"";;

let rec next_rules_file file_stack = match file_stack with
  |[] -> None
  |s :: t ->
    if Sys.file_exists s then
      if Sys.is_directory s then (
        next_rules_file ((Array.fold_left (fun lst fname -> (Printf.sprintf "%s/%s" s fname) :: lst) [] (Sys.readdir s)) @ t);
      ) else (
        if (Str.string_match rule_file_filter s 0) then Some (s, t) else next_rules_file t
      )
    else next_rules_file t;;

let make_line_reader fname =
  let in_channel = open_in fname in
  let closed = ref false in
  let next_line = fun () ->
    if !closed then
      None
    else
      try
        Some (Scanf.fscanf in_channel "%[^\r\n]\n" (fun x -> x))
      with
        End_of_file ->
          let _ = close_in_noerr in_channel in
          let _ = closed := true in
          None in
  next_line;;

let make_regex_reader line_reader =
  let line_count = ref 0 in
  let rec next_regex = fun () -> match (line_reader ()) with
    |None -> None
    |Some s ->
      line_count := !line_count + 1;
      if (Str.string_match pcre_regex_filter s 0) then
        Some (!line_count, Str.matched_group 1 s)
      else
        next_regex () in
  next_regex;;

let rec next m = match (m.next_regex ()) with
  |None -> 
    begin
      match (next_rules_file m.file_stack) with
        |None -> None
        |Some (f, t) -> 
          m.current_file <- f;
          m.next_regex <- make_regex_reader (make_line_reader f);
          m.file_stack <- t;
          next m
    end
  |Some (i, r) -> Some (m.current_file, i, r);;
