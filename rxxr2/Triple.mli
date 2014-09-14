(* © Copyright University of Birmingham, UK *)

open Common
open Phi

(* internal representation of a triple *)
type t;;

module TripleSet : (Set.S with type elt = t);;

(* make a triple consisting of two parallel NFA states and a phi *)
val make : int -> int -> Phi.t -> t;;

(* extract elements of a triple *)
val elems : t -> int * int * Phi.t;;

(* compute all single-character (or class) reachable triples *)
val advance : (Nfa.t * Word.t * t) -> (Word.t * t) list;;
