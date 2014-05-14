(*===========================================================================
  Some simple examples used in the ITP 2013 submission
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor programassem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(*=max *)
(* Determine max(r1,r2), leaving result in r1 *) 
Definition max (r1 r2: Reg) : program :=
  LOCAL Bigger;
    CMP r1, r2;; JG Bigger;; MOV r1, r2;;
  Bigger:; . 
(*=End *)

(*=letproc *)
Definition callproc f :=
  LOCAL iret;
   MOV EDI, iret;; 
   JMP f;; 
  iret:;.

Definition defproc (p: program) :=
  p;; JMP EDI.

Notation "'letproc' f ':=' p 'in' q" := 
  (LOCAL skip; LOCAL f; 
    JMP skip;; 
   f:;;    defproc p;; 
   skip:;; q) 
  (at level 65, f ident, right associativity).

(* Multiply EAX by nine, trashing EBX *)
Example ex :=
  letproc tripleEAX := 
    MOV EBX, EAX;; SHL EAX, 2;; ADD EAX, EBX
  in 
    callproc tripleEAX;; callproc tripleEAX.
(*=End *)

(* Example taken verbatim from TALx86: A Realistic Typed Assembly Language *)
Example talx86_4_1 :=
LOCAL test; LOCAL body;
  MOV EAX, ECX;;
  INC EAX;;
  MOV EBX, 0;;
  JMP test;;
body:;;           (* EAX: DWORD, EBX: DWORD *)
  ADD EBX, EAX;;
test:;;           (* EAX: DWORD, EBX: DWORD *)
  DEC EAX;;
  CMP EAX, 0;;
  JG body.


(* Inline data *)
Example exdata :=
  LOCAL data; LOCAL skip;
    MOV EDI, data;;
    ADD EAX, [EDI];;
    JMP skip;;
  data:;;
    dw #123;;
  skip:;.

(* Alignment *)
(*=exalign *)
Example exalign :=
LOCAL str; LOCAL num;
str:;;  ds "Characters";;
num:;;  align 2;; (* Align on 2^2 boundary i.e. DWORD *)
        dd #x"87654321". (* DWORD value *)
(*=End *)
  