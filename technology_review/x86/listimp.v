(*===========================================================================
  Implementation of linked lists
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor inlinealloc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Definition inlineHead (r1 r2:Reg) :program :=
  mov r1, [r2+0]. 

Definition inlineTail (r1 r2:Reg) :program :=
  mov r1, [r2+4]. 

(* Head is in r1, tail is in r2, result in EDI, ESI trashed *)
Definition updateCons (r1 r2:Reg) :program :=
    sub EDI, 8;;
    mov [EDI], r1;;
    mov [EDI+4], r2.

Definition inlineCons (r1 r2:Reg) heapInfo failAddr: program :=
  allocImp heapInfo 8 failAddr;;
  updateCons r1 r2.
    

