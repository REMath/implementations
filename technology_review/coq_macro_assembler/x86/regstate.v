(*===========================================================================
    State of the registers
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype seq fintype finfun .
Require Import reg bitsrep update.
Local Open Scope update_scope.

(* State of the registers, including IP and flags *)
(* Lookup is just function application *)
(*=RegState *)
Definition RegState := AnyReg -> DWORD. 
(*=End *)

(* Avoid == to permit extraction *)
Instance RegStateUpdateOps : UpdateOps RegState AnyReg DWORD :=
  fun rs r v => fun r' => if r == r' then v else rs r'.

Lemma setThenGetDistinct r1 v r2 (rs: RegState) : 
  ~~ (r1 == r2) -> (rs !r1:=v) r2 = rs r2.
Proof. move => neq. rewrite /update /RegStateUpdateOps. by rewrite (negbTE neq). Qed.

Lemma setThenGetSame r v rs : (rs !r:=v) r = v.
Proof. rewrite /update /RegStateUpdateOps. 
by rewrite (introT (eqP) (refl_equal _)). 
Qed. 

Require Import FunctionalExtensionality.

Instance RegStateUpdate : Update RegState AnyReg DWORD. 
apply Build_Update. 
(* Same register *)
move => rs r v w. rewrite /update /RegStateUpdateOps.
apply functional_extensionality => r'. by case: (r == r').
(* Different register *)
move => rs r1 r2 v1 v2 neq. rewrite /update /RegStateUpdateOps. 
apply functional_extensionality => r. 
case E1: (r2 == r).
case E2: (r1 == r). rewrite (elimT (eqP) E1) in neq. 
rewrite (elimT (eqP) E2) in neq. done. done. 
done. 
Qed. 

Definition initialReg : RegState := fun _ => #0. 

Require Import String.
Definition regStateToString (rs:RegState) :=
  (" EIP=" ++ toHex (rs EIP) ++
   " ESP=" ++ toHex (rs ESP) ++
   " EBP=" ++ toHex (rs EBP) ++
   " EAX=" ++ toHex (rs EAX) ++
   " EBX=" ++ toHex (rs EBX) ++
   " ECX=" ++ toHex (rs ECX) ++
   " EDX=" ++ toHex (rs EDX) ++
   " ESI=" ++ toHex (rs ESI) ++
   " EDI=" ++ toHex (rs EDI) ++
   " EBP=" ++ toHex (rs EBP)
   )%string.
