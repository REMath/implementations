(*===========================================================================
  Hello world for Windows
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program.
Require Import pecoff.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope string_scope.
Open Scope instr_scope.

Example helloWorldCode (dataAddress:DWORD) (imports: seq (seq DWORD)) :=
let printf: DWORD := List.nth 0 (List.nth 0 imports [::]) #0 in
LOCAL formatString;
 MOV EDI, formatString;;
 PUSH EDI;;
 MOV EDI, printf;;
 CALL [EDI];;
 ADD ESP, 4;;    (* cdecl calling convention for printf *)
 RET 0;;
formatString:;;
  ds "Hello, world";; db #10;; db #0.

Definition helloWorldBytes := 
  makePEfile EXE "helloworld.exe" #x"10E30000"
    [::Build_DLLImport "MSVCRT.DLL" [::ImportByName "printf"]]
    (dd #0) helloWorldCode.


Goal True.
(* vm_compute crashes. tail recursion not supported? *)
  let b := eval compute in (bytesToHex helloWorldBytes) in
  idtac b.
done. Qed.
