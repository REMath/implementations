(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ./LICENSE for authorship and licensing information    *)

open X86Types

(* help functions for trimming a string *)
let left_pos s len =
  let rec aux i =
    if i >= len then None
    else match s.[i] with
    | ' ' | '\n' | '\t' | '\r' -> aux (succ i)
    | _ -> Some i
  in
  aux 0
 
let right_pos s len =
  let rec aux i =
    if i < 0 then None
    else match s.[i] with
    | ' ' | '\n' | '\t' | '\r' -> aux (pred i)
    | _ -> Some i
  in
  aux (pred len)
 
(* trim a string - remove whitespace before and after string*)
let trim s =
  let len = String.length s in
  match left_pos s len, right_pos s len with
  | Some i, Some j -> String.sub s i (j - i + 1)
  | None, None -> ""
  | _ -> assert false


(* Returns a list of lines in file filename *)
let read_lines filename = 
let lines = ref [] in
let chan = open_in filename in
try
  while true; do
    lines := input_line chan :: !lines
  done; []
with End_of_file ->
  close_in chan; !lines

type cache_params =
{
    cache_s: int; (* in bytes *)
    line_s: int;  (* same as "data block size"; in bytes *)
    assoc: int;
    inst_cache_s: int; (* in bytes *)
    inst_line_s: int;  (* same as "data block size"; in bytes *)
    inst_assoc: int;
    inst_base_addr: int64;
}

let setInitialValue addr lower upper mem =
  let parse_interval_bound n =
    if Int64.compare n 0L = -1 then failwith "Negative numbers are not allowed"
    else if Int64.compare n 0xFFFFFFFFL = 1 then failwith "Numbers have to be in the 32bit range"
    else n in
  let lower = parse_interval_bound lower in
  let upper = parse_interval_bound upper in
  if Int64.compare lower upper = 1 then failwith "lower bound should be lower or equal than upper bound"
  else (addr,lower,upper) :: mem



let config filename =
  let scanned = 
    List.map (fun x ->
        (* Remove whitespaces *)
        let x = trim x in
        (* Remove comments *)
        let x = if String.contains x '#' then
                  String.sub x 0 (String.index x '#')
                else x
        in
        if x = "" then ("",0L,0L)
        else 
          (* Quick fix in order to accept intervals as starting values *)
          try Scanf.sscanf x "%s %Li" (fun s i -> (s,i,i))
          with Scanf.Scan_failure _ -> Scanf.sscanf x "%s [%Li, %Li]" (fun s l h -> (s,l,h))
        ) (read_lines filename) in
  (* scanned returns a list of strings with two numbers; the two numbers correspond to an interval *)
  let rec auxmatch lss (start,registers,cache) =
    match lss with
    | [] -> (start,registers,cache)        
    | l::ls -> 
    (let (st,(mem,regs),ca) = auxmatch ls (start,registers,cache)
    in let vals = (mem,regs)
    in match l with
      | ("START",i,_) ->  (Some (Int64.to_int i), vals, ca)
      | ("cache_s",i,_) -> (st,vals,{ca with cache_s = Int64.to_int i})
      | ("line_s",i,_) -> (st,vals,{ca with line_s = Int64.to_int i})
      | ("assoc",i,_) -> (st,vals,{ca with assoc = Int64.to_int i})
      | ("inst_cache_s",i,_) -> (st,vals,{ca with inst_cache_s = Int64.to_int i})
      | ("inst_line_s",i,_) -> (st,vals,{ca with inst_line_s = Int64.to_int i})
      | ("inst_assoc",i,_) -> (st,vals,{ca with inst_assoc = Int64.to_int i})
      | ("INST_BASE",i,_) -> (st,vals,{ca with inst_base_addr = i})
      | ("LOG",i,_) -> MemAD.log_address i; (st,vals,ca)
      | ("",0L,_)  -> (st,vals,ca)
      | (str, l, h) ->
                  try (
                    (st, (mem,(X86Util.string_to_reg32 str, l, h) :: regs),ca)
                  ) with Invalid_argument arg -> try (
                    (st,(setInitialValue (Int64.of_string str) l h mem, regs), ca)
                  ) with Failure arg -> failwith (Printf.sprintf "Configuration not supported. %s is not a valid register or a memory location" arg)
            )
  in let empty_cparams = {cache_s = 0; line_s = 0; assoc = 0; inst_cache_s = 0; inst_line_s = 0; inst_assoc = 0; inst_base_addr = (Int64.of_int 0)}
  in auxmatch scanned (None,([],[]),empty_cparams)
