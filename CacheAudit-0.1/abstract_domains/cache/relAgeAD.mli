(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)

(** An [AgeAD]-implementation using relational sets for keeping track of ages *)

open NumAD.DS

module type S = AgeAD.S

module RelAgeAD : S
