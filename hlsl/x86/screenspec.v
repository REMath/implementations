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
Definition screenBase: DWORD := #x"b8000".
Definition numCols := 80.
Definition numRows := 50.
Definition screenLimit : DWORD := screenBase +# numCols*numRows*2.
Definition screenMapped := memAny screenBase screenLimit.

Definition charPos col row := screenBase +# col*2 +# row*160.

Definition inlineComputeCharPos_spec (i j:DWORD) (col row:nat) (instrs: program) :=
  |-- 
  (safe @ (EIP ~= j ** ECX? ** EDX? ** EDI ~= charPos col row) -->>
   safe @ (EIP ~= i ** ECX ~= #col ** EDX ~= #row ** EDI?)) @
  (i -- j :-> instrs ** OSZCP_Any).

