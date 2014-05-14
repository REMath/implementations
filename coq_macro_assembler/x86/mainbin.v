Require Import ssreflect seq finfun tuple fintype.
Require Import bitsrep bitsops mem reg instr instrsyntax encinstr update screenspec.
Require Import main.

Open Scope string_scope.

Goal True.
(* vm_compute crashes. tail recursion not supported? *)
  let b := eval compute in (bytesToHex mainBytes) in
  idtac b.
done. Qed.


