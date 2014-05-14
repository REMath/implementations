(*===========================================================================
  Lists
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor inlinealloc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Fixpoint listSeg (p e:DWORD) (vs: seq DWORD) :SPred :=
  if vs is v::vs
  then Exists q, p :-> v ** p +#4 :-> q ** listSeg q e vs
  else p == e /\\ empSP.

Definition inlineHead_spec (r1 r2:Reg) (i j p e: DWORD) v vs (instrs: program) :=
  |-- 
  (safe @ (EIP ~= j ** r1~=v) -->>
   safe @ (EIP ~= i ** r1?)) @
  (listSeg p e (v::vs) ** r2~=p) <@ (i -- j :-> instrs).

Definition inlineTail_spec (r1 r2:Reg) (i j p e: DWORD) v vs (instrs: program) :=
  |-- 
  (safe @ (Exists q, EIP ~= j ** r1~=q ** listSeg p q (v::nil) ** listSeg q e vs) -->>
   safe @ (EIP ~= i ** r1? ** listSeg p e (v::vs))) @ 
  (r2~=p) <@ (i -- j :-> instrs).

(* Head is in EAX, tail is in EDI, result in EDI, ESI trashed *)
Definition inlineCons_spec (r1 r2:Reg) heapInfo (failLabel:DWORD) (i j h t e: DWORD) vs (instrs: program):=
  |-- (
      safe @ (EIP ~= failLabel ** r1? ** r2? ** EDI?) //\\
      safe @ (EIP ~= j ** Exists pb, r1? ** r2? ** EDI ~= pb ** listSeg pb t [::h])
    -->>
      safe @ (EIP ~= i ** r1~=h ** r2~=t ** EDI?)
    ) @
    (ESI? ** OSZCP_Any ** allocInv heapInfo ** listSeg t e vs)
    <@ (i -- j :-> instrs).

