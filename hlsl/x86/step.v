(*===========================================================================
    Single-step transition function

    As well as ordinary x86 instruction semantics, this incorporates I/O 
    actions, which are "faked" by assuming that the semantics of entering 
    two well-known memory locations is to perform input or output.
  ===========================================================================*)
Require Import ssreflect ssrnat ssrbool eqtype tuple seq. 
Require Import instr monad reader procstate procstatemonad exn eval decinstr 
               monadinst action bitsrep bitsops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Decode instruction at EIP, move EIP to next instruction, execute instruction *)
Definition step : ST unit := 
  let! oldIP = getRegFromProcState EIP; 
  let! (instr,newIP) = readFromProcState oldIP;
  do! setRegInProcState EIP newIP;
  evalInstr instr.




