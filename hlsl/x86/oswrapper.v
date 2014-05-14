Require Import ssreflect seq finfun tuple fintype.
Require Import bitsrep bitsops mem reg instr instrsyntax encinstr update.
Require Import program programassem entry gcdex.

Open Scope string_scope.
Goal True.
  let b := eval vm_compute in (bytesToHex gcdEx) in
  idtac b.
done. Qed.
