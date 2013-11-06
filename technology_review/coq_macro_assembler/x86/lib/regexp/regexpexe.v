Require Import ssreflect ssrfun ssrbool finfun fintype ssrnat eqtype seq tuple.
Require Import path fingraph  finset.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr monad reader writer procstate procstatemonad mem exn eval decinstr
               monadinst ioaction bitsrep bitsops eval step encinstr pointsto cursor.
Require Import program programassem reg instrsyntax instrrules.
Require Import spectac iltac triple.
Require Import pecoff.

Require Import stringbuff.
Require Import interfaceATBR.
Require Import exampleregexp.
Require Import compiler.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(*****************************************************************)
(* Pe/Coff                                                       *)
(*****************************************************************)


Fixpoint compileString (s: string): program :=
  match s with
    | EmptyString => dd #0
    | String c s =>
        dd #(Ascii.nat_of_ascii c);;
        compileString s
  end.

Definition buffSize := 32.


Definition exampleCode (dataAddress:DWORD) (imports: seq (seq DWORD)) : program :=
let data:DWORD := dataAddress in
let buffer:DWORD := dataAddress+#(((buffSize + 1) * 8) %nat) in
let puts:DWORD := List.nth 0 (List.nth 2 imports [::]) #0 in
let gets:DWORD := List.nth 1 (List.nth 2 imports [::]) #0 in
 LOCAL succMsg; LOCAL failMsg; LOCAL errMsg; 
 LOCAL print;
 LOCAL succ; LOCAL fail; LOCAL err;
 LOCAL loop; LOCAL run_dfa;
 LOCAL load_any; LOCAL load_minus; LOCAL load_plus; LOCAL load_dot; LOCAL load_exp;
 LOCAL cap; LOCAL num; LOCAL symb;
 LOCAL next;
  (* Load input in [buffer] *)
  MOV EDI, gets;;
  PUSH buffer;;
  CALL [EDI];;
  ADD ESP, 4;;

  (* Reformat input in [data] *)
  (* Got: BYTE with ascii characters *)
  (* Want: DWORD containing these ascii characters *)
  (* Output in [buffer] *)
  MOV EAX, buffer;;
  MOV EBX, data;;
(*  MOV ECX, (#0: DWORD);; *)
 loop:;;
  CMP BYTE [EAX], #0;;
  JE run_dfa;;
  (* Copy Byte in [EAX] to DWORD [EBX] *)
  MOV CL, [EAX];;
  MOV [EBX], CL;;

  (* Next char *)
  INC EAX;;
  ADD EBX, (#4: DWORD);;
  JMP loop;;

  (* Run DFA on [data] *)
 run_dfa:;;
  MOV [EBX], (#0: DWORD);;
  MOV EAX, data;;
  code fp alphabet succ fail err;;
 succ:;;
  MOV EAX, succMsg;;
  JMP print;;
fail:;;
  MOV EAX, failMsg;;
  JMP print;;
err:;;
  MOV EAX, errMsg;;
print:;;
  MOV EDI, puts;;
  PUSH EAX;;
  CALL [EDI];;
  ADD ESP, 4;;
  RET 0;;
succMsg:;;
  dd #c"Acc.";; db #0;;
failMsg:;;
  dd #c"Rej.";; db #0;;
errMsg:;;
  dd #c"Err.";; db #0.


Definition exampleData: program :=
  LOCAL data; LOCAL buffer;
data:;;
    pad ((buffSize + 1) * 8);;
buffer:;;
    pad (buffSize + 1).


Definition minimalPEFile := 
  makePEfile EXE "compiler.exe" #x"10E30000"
    [::Build_DLLImport "USER32.DLL" [::ImportByName "MessageBoxA"; ImportByName "MessageBoxW"];
       Build_DLLImport "KERNEL32.DLL" [::ImportByName "ExitProcess"];
       Build_DLLImport "MSVCRT.DLL" [::ImportByName "puts"; ImportByName "gets"]]
    exampleData exampleCode.

Goal True.
(* vm_compute crashes. tail recursion not supported? *)
  let b := eval vm_compute in (bytesToHex minimalPEFile) in
  idtac b.
done. Qed.