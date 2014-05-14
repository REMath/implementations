(*===========================================================================
  Information for reviewers of the PPDP 2013 submission
  "Coq: The world's best macro assembler?" by
  Andrew Kennedy, Nick Benton, Jonas Jensen, and Pierre-Evariste Dagand
  ===========================================================================*)

(*
This tar file contains sources related to the submission. 
For linux, there is a GNUmakefile for building the samples; 
on Windows, there is a Makefile and build.bat script, and additionally a
"buildiso.bat" batch file that can be used to build an ISO CD image
which can be booted on a Virtual PC of burned onto disc and booted
directly on a machine. The example in the ISO image is "Game of Life"
using the legacy text-mode. You can find the Coq assembler source in
x86/lifeimp.v.

Section by section, the Coq sources for the paper can be found as follows.
*)

(* Section 1.1: factorial example, game of life *)

Require Import fact.
Require Import winfact.
Require Import String.
Require Import lifeimp.

(* Section 2.1 (Bits, bytes and all that) *)

Require Import bitsrep bitsops bitsprops bitsopsprops.

(* Section 2.2 (Memory) *)

Require Import pmap pmapprops mem.

(* Section 2.3 (Monads) *)

Require Import monad monadinst.

(* Section 2.4 (Readers and writers) *)
  
Require Import cursor reader writer pointsto roundtrip.

(* Section 2.5 (Instructions): *)
  
Require Import reg instr.

(* Section 2.6 (Operational semantics) *)

Require Import flags exn regstate procstate procstatemonad
               eval step encdechelp emb decinstr.

(* Section 3.1 (Basics of assembly code) *)

Require Import encinstr examples roundtripinstr program programassem.

(* Section 3.2 (Macros) *)

Require Import call instrsyntax macros examples.

(* Section 4.1 (Multiplication macro) *)

Require Import mulc.

(* Section 4.2 (Calling conventions) *)

Require Import cfunc.

(* Also see following for a trivial memory allocator and list-cell functions, 
  as mentioned in our previous POPL'13 paper: another example of assembler syntax in Coq. *)

Require Import inlinealloc listspec listimp listproof.

(* Section 4.3 (Regular expressions) *)

Require Import compiler regexpsyntax exampleregexp regexpexe.
