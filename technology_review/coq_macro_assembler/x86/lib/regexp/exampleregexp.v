Require Import ssreflect ssrfun ssrbool finfun fintype ssrnat eqtype seq tuple.
Require Import bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr monad reader writer procstate procstatemonad mem exn eval decinstr
               monadinst ioaction bitsrep bitsops eval step encinstr pointsto cursor.
Require Import program programassem reg instrsyntax instrrules.
Require Import spectac iltac triple.


(* ATBR *)
Require Import ATBR.DecideKleeneAlgebra.
Require Import ATBR.DKA_Definitions.

Require Import interfaceATBR.
Require Import regexpsyntax.

Local Open Scope regex_scope.
Open Scope char_scope.

(**********************************)
(* Floating point regexp          *)
(**********************************)

Definition alphabet: seq DWORD := 
cat [seq (# c) | c <- iota (Ascii.nat_of_ascii "0") 10 ] 
    [:: #(Ascii.nat_of_ascii "-") 
      ; #(Ascii.nat_of_ascii "+")
      ; #(Ascii.nat_of_ascii "e")
      ; #(Ascii.nat_of_ascii ".")].


(* ^[-+]?[0-9]*\.?[0-9]+([e][-+]?[0-9]+)?$ *)
Definition fp: regex :=  
  [[ "-" , "+"]]? ' [{ "0" , "9" }] * '
   $"." ? '
  [{ "0" , "9" }]+ '
  ($"e" ' [[ "-" , "+"]] ? ' [{ "0" , "9" }]+) ?.

(**********************************)
(* Examples:                      *)
(**********************************)

Definition code_zero: program := code rO [:: #1 ; #2 ; #3 ] #42 #24 #0.
Definition bytes_zero := assemble #x"C0000000" code_zero.
(* Compute (bytesToHex bytes_zero). *)

Definition code_var1: program := code $"1" [:: #1 ; #2 ; #3 ] #42 #24 #0.
Definition bytes_var1 := assemble #x"C0000000" code_var1.
(* Compute (bytesToHex bytes_var1). *)


Local Close Scope regex_scope.