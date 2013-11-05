(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

(** Parsing of ELF executables *)

exception NonElfFile

type t

val parse : AsmUtil.bits -> t

val read : string -> t

val sections : t -> ExecInterfaces.section list

val virtual_start : t -> int64
