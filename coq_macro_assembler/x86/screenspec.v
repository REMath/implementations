(*===========================================================================
  Specification of CGA screen functions
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program.
Require Import instr decinstr reader pointsto cursor instrrules.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* This should be hidden behind an abstraction *)
Definition screenBase: DWORD := #x"000b8000".
Definition numCols := 80.
Definition numRows := 50.
Definition screenLimit : DWORD := screenBase +# numCols*numRows*2.
Definition screenMapped := memAny screenBase screenLimit.

Definition charPos col row := screenBase +# col*2 +# row*160.

Definition charIs (p: DWORD) (b: BYTE) := p :-> b. 
Definition colourIs (p: DWORD) (c: BYTE) := p+#1 :-> c. 

Definition inlineComputeLinePos_spec (row:nat) (base:DWORD) (instrs: program) :=
  basic (EDX ~= # row ** EDI ~= base) instrs
        (EDX ~= # row ** EDI ~= base +# row*160) @ OSZCP_Any.


Definition inlineComputeCharPos_spec (col row:nat) (instrs: program) :=
  basic (ECX ~= # col ** EDX ~= # row ** EDI?) instrs
        (ECX?         ** EDX? **         EDI ~= charPos col row) @ OSZCP_Any.

Definition inlineOutputChar_spec (col row: nat) (char: BYTE) (instrs: program) :=
  basic 
    (ECX ~= # col ** EDX ~= # row ** BYTEregIs AL char ** (Exists old, charIs (charPos col row) old))
    instrs
    (ECX?        ** EDX?        ** BYTEregIs AL char ** charIs (charPos col row) char) 
  @ (OSZCP_Any ** EDI?).
  
Definition inlineReadChar_spec (col row: nat) (char:BYTE) (instrs: program) :=
  basic 
    (ECX ~= # col ** EDX ~= # row ** EAX? ** charIs (charPos col row) char)
    instrs
    (ECX?        ** EDX?        ** BYTEregIs AL char ** charIs (charPos col row) char) 
  @ (OSZCP_Any ** EDI?).
  

