(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

(** Analysis of headers for executable files.
   So far, only ELF is supported       
 *)

type t 

exception InvalidVirtualAddress
exception AddressNotInFile

val read_exec: string -> t

val starting_offset: t -> int

(* Raises InvalidVirtualAddress when the address is not mapped by the executable   Raises AddressNotInFile when the adress is valid but not mapped in the executable file *)

val virtual_to_offset: t -> int64 -> int

val get_bits : t -> AsmUtil.bits

(* lookup mem addr returns the content of addr (which is a virtual address *)
(* May raise InvalidVirtualAddress *)
val lookup : t -> int64 ->  int64

(* May raise InvalidVirtualAddress *)
(* May raise AddressNotInFile *)
val write : t -> int64 -> int -> int64 -> t
