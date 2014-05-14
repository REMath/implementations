(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

(** Some shared functions *)

open Big_int
open NumAD.DS

(** Computes the logarithm to base 2 of a Bigint number,
the result is a floating-point number *)
val log2 : big_int -> float

(** Gives the product of a list of Int64's; the result is a big_int*)
val prod : int64 list -> big_int

(** [partition elts pfn] partitions the NumSet [elts] according to the 
    function [pfn]. The result is an IntMap wich maps integers to their
    images in [pfn] *)
val partition : NumSet.t -> (NumSet.elt -> int) -> NumSet.t IntMap.t
