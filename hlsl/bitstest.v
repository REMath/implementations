(*===========================================================================
  Test the performance of bits operations
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import ssralg.
Open Scope ring_scope.

Definition n' := Eval cbv in 31.
Definition n := n'.+1.

Example ex:BITS n := #59 + #23 *+ 3. 

Example incTest := 
  let v:=@fromZ n 12345 in
  toZ (n:=n') (iter 100 (iter 200 (@incB n)) v).

Example addTest := 
  let v:=@fromZ n 12345 in
  toZ (n:=n') (iter 100 (iter 200 (@addB n v)) v).

(*Extraction "bitstest" incTest addTest.*)

(* We can do around 70,000 increments a second *)
Time Compute incTest.

(* We can do around 5,000 adds a second *)
Time Compute addTest.

(* Compare against compcert 
Add LoadPath "Compcert\compcert-1.10\lib".
Require Import Integers.

Example auxIncTest :=
  let v := Int.repr 12345 in
  Int.unsigned (iter 100 (iter 200 (fun x => Int.add x (Int.repr 1))) v).

Example auxAddTest :=
  let v := Int.repr 12345 in
  Int.unsigned (iter 100 (iter 200 (fun x => Int.add x v)) v).

Time Compute auxIncTest.  
Time Compute auxAddTest.  
*)