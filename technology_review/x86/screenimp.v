(*===========================================================================
  Implementation of CGA screen functions
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor screenspec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(* Compute (in EDI) the screen address of the character specified by ECX (column)
   and EDX (row). ECX and EDX get trashed. *)
Definition inlineComputeCharPos: program :=
     mov EDI, screenBase;;
     shl EDX, 5;;
     add EDI, EDX;;
     shl EDX, 2;;
     add EDI, EDX;;
     shl ECX, 1;;
     add EDI, ECX.

(* Output character in AL at position specified by CX (column) and DX (row) *)
Definition inlineOutputChar :=
  inlineComputeCharPos;;
  mov byte [EDI], EAX.

Definition clearColour := toNat (n:=8) (#x"4F").

(* Code for clear screen. *)
Definition clsProg:program := 
      mov EBX, screenBase;; 
      while (cmp EBX, screenLimit) CC_B true ( (* while EBX < screenLimit *)
        mov byte [EBX], (Ascii.nat_of_ascii " ");; 
        mov byte [EBX+1], clearColour;;
        inc EBX;; inc EBX (* move one character right on the screen *) 
      ).

