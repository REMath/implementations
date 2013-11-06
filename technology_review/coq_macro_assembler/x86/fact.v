(*===========================================================================
  Factorial example, from Section 1.1 of the PPDP 2013 submission
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor programassem pecoff.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Definition defproc (p: program) :=
  p;; JMP EDI.

Notation "'letproc' f ':=' p 'in' q" := 
  (LOCAL skip; JMP skip;; LOCAL f; f:;; defproc p;; skip:;; q) 
  (at level 65, f ident, right associativity).

Definition callproc f :=
  LOCAL iret; MOV EDI, iret;; JMP f;; 
  iret:;.

(*=main *)
Definition call_cdecl3 f arg1 arg2 arg3 := 
  PUSH arg3;; PUSH arg2;; PUSH arg1;; 
  CALL f;; ADD ESP, 12.

Definition main (printfSlot: DWORD) :=  
  (* Argument in EBX *)
  letproc fact :=
    MOV EAX, 1;; 
    MOV ECX, 1;;
      (* while ECX <= EBX *)
      while (CMP ECX, EBX) CC_LE true ( 
        MUL ECX;; (* Multiply EAX by ECX *)
        INC ECX
      )
  in
    LOCAL format;   
      MOV EBX, 10;; callproc fact;;
      MOV EDI, printfSlot;; 
      call_cdecl3 [EDI] format EBX EAX;;
      MOV EBX, 12;; callproc fact;;
      MOV EDI, printfSlot;; 
      call_cdecl3 [EDI] format EBX EAX;;
      RET 0;;
    format:;;
      ds "Factorial of %d is %d";; db #10;; db #0.
(*=End *)

(*=bytes *)
Definition bytes := 
  assemble #x"C0000004" (main #x"C0000000").
Goal True.
  let b := eval cbv in (bytesToHex bytes) in idtac b. 
  done. Qed.
(*=End *)





