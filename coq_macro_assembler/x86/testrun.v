(*===========================================================================
    Actually run the transition function on some code
  ===========================================================================*)
Require Import ssreflect ssrnat ssrbool eqtype tuple seq. 
Require Import instr monad reader writer procstate procstatemonad mem exn eval decinstr 
               monadinst ioaction bitsrep bitsops eval step encinstr cursor fact.

Require Import program programassem reg instrsyntax. 

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition codeAddr := #x"C0000004".
Definition codeSpace := 256.
Definition stackAddr := #x"D0000000".
Definition stackSpace := 256.

Definition reservedMemory := 
  reserveMemory 
  (reserveMemory initialMemory codeAddr # codeSpace) 
  (stackAddr -# stackSpace) # stackSpace.

(* We expect this to succeed *)
Definition initializedMemory := 
  if writeMem write_program reservedMemory (mkCursor codeAddr) (main #x"C0000000") is Some (_,m) then m else reservedMemory.

Definition initialState := 
  mkProcState ((initialReg ! EIP:=codeAddr ! regToAnyReg ESP:=stackAddr)) initialFlagState initializedMemory. 

Definition runFor n s := 
  let: (output,r) := doMany n step s
  in (output, if r is Success r then fst r else s).

Fixpoint outputToString (s: seq (Chan*Data)) :=
  if s is (c,d)::s 
  then toHex c ++ ":" ++ toHex d ++ " " ++ outputToString s
  else "".

Definition resultToString r := outputToString (fst r) ++ procStateToString (snd r).

(* We need some better pretty-printing! *)
(*
Compute resultToString (runFor 0 initialState).
Compute resultToString (runFor 1 initialState).
Compute resultToString (runFor 2 initialState).
*)
