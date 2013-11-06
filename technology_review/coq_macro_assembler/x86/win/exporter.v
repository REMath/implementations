Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program.
Require Import pecoff.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope string_scope.
Open Scope instr_scope.

Example main (dataAddress:DWORD) (imports: seq (seq DWORD)) :=
  GLOBAL add "add";
  add:;;
  ADD EAX, EBX;;
  JMP add;; (* for debug purposes *)
  RET 0.

Definition mainBytes :=
  makePEfile DLL "exporter.dll" #x"22770000"
    [:: Build_DLLImport "MSVCRT.DLL" [:: ImportByName "printf"]]
    (dd #0)
    main.

Goal True.
(* vm_compute crashes. tail recursion not supported? *)
  let b := eval compute in (bytesToHex mainBytes) in
  idtac b.
done. Qed.
