(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ./LICENSE for authorship and licensing information    *)


(** Module for parsing the configuration file *)

val left_pos : string -> int -> int option
val right_pos : string -> int -> int option
val trim : string -> string
val read_lines : string -> string list
type cache_params = {
  cache_s : int;
  line_s : int;
  assoc : int;
  inst_cache_s : int;
  inst_line_s : int;
  inst_assoc : int;
  inst_base_addr : int64;
}
val config :
  string ->
  int option * MemAD.mem_param * cache_params
