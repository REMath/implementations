(*===========================================================================
  GUI version of hello world for Windows
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program.
Require Import pecoff.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope string_scope.
Open Scope instr_scope.

Definition messageBoxCode (dataAddress:DWORD) (imports: seq (seq DWORD)) : program :=
let messageBox: DWORD := List.nth 0 (List.nth 0 imports [::]) #0 in
  MOV EDI, dataAddress;;
  PUSH 0;;
  PUSH [EDI+4];;
  PUSH [EDI];;
  PUSH 0;;
  MOV EDI, messageBox;;
  CALL [EDI];;    (* stdcall calling convention for MessageBox *)
  RET 0.

Definition messageBoxData: program :=
  LOCAL message; LOCAL title;
  dd message;; dd title;;
message:;; ds "Hello, world";; db #0;;
title:;;   ds "My first app";; db #0.

Definition messageBoxBytes := 
  makePEfile EXE "messagebox.exe" #x"10E30000"
    [::Build_DLLImport "USER32.DLL" [::ImportByName "MessageBoxA"]]
    messageBoxData messageBoxCode.


Goal True.
(* vm_compute crashes. tail recursion not supported? *)
  let b := eval compute in (bytesToHex messageBoxBytes) in
  idtac b.
done. Qed.
