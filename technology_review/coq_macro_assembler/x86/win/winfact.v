Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program programassem cursor.
Require Import pecoff cfunc fact.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import List.
(*=bytes *)
Definition bytes :=
  makePEfile EXE "winfact.exe" #x"00760000"
    [::Build_DLLImport "MSVCRT.DLL" [::ImportByName "printf"]]
    (dd #0) 
    (fun _ imports => main (hd #0 (hd nil imports))).

Open Scope string_scope.
Goal True.
  let b := eval cbv in (bytesToHex bytes) in idtac b. 
  done. Qed.
(*=End *)

