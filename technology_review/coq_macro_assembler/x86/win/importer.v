Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program programassem cursor.
Require Import pecoff cfunc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.
Open Scope string_scope.

Definition call_cdecl2 f arg1 arg2 := 
  PUSH arg2;; PUSH arg1;; CALL f;; ADD ESP, 8.

Definition main (printf add : DWORD) :=
LOCAL greeting;
LOCAL answer;
  MOV EDI, printf;; PUSH greeting;; CALL [EDI];; ADD ESP, 4;;
  MOV EDI, add;;
  MOV EAX, 19;;
  MOV EBX, 23;;
  CALL [EDI];;
(*
  call_cdecl2 [EDI] EAX EBX;;
*)
  MOV EDI, printf;;
  call_cdecl2 [EDI] answer EAX;;
  RET 0;;
greeting:;;
  ds "Hello!";; db #10;; db #0;;
answer:;;
  ds "The answer is %d.";; db #10;; db #0.

Require Import List.
(*=bytes *)
Definition bytes :=
  makePEfile EXE "importer.exe" #x"00AB0000"
    [ :: Build_DLLImport "MSVCRT.DLL"   [:: ImportByName "printf"]
       ; Build_DLLImport "exporter.dll" [:: ImportByName "add"]
    ]
    (dd #0)
    (fun dataAddr imports =>
       let import dll idx := nth idx (nth dll imports nil) #0 in
       main (import 0 0) (import 1 0)).

Open Scope string_scope.
Goal True.
  let b := eval cbv in (bytesToHex bytes) in idtac b.
  done. Qed.
(*=End *)

