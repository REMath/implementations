(*===========================================================================
    Model for x86 flags
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat tuple.
Require Import bitsrep bitsops update.
Local Open Scope update_scope.

(* Represent a flag finitely! *)
Definition Flag  := BITS 5.

(* Some instructions leave the state of certain flags "unspecified" *)
Inductive FlagVal := 
| mkFlag :> bool -> FlagVal
| FlagUnspecified. 

(* State of the flags *)
(* Lookup is just function application *)
Definition FlagState := Flag -> FlagVal.

Instance FlagStateUpdateOps : UpdateOps FlagState Flag FlagVal :=
  fun fs f v => fun f' => if f == f' then v else fs f'.

Lemma setFlagThenGetDistinct (f1:BITS 5) (v:FlagVal) (f2:BITS 5) (fs: FlagState) : 
  ~~ (f1 == f2) -> (fs !f1:=v) f2 = fs f2.
Proof. move => neq. rewrite /update /FlagStateUpdateOps. by rewrite (negbTE neq). Qed.

Lemma setFlagThenGetSame f v fs : (fs !f:=v) f = v.
Proof. rewrite /update /FlagStateUpdateOps. 
by rewrite (introT (eqP) (refl_equal _)). 
Qed. 

Require Import FunctionalExtensionality.

Instance FlagStateUpdate : Update FlagState Flag FlagVal.
apply Build_Update. 
(* Same flag *)
move => fs f v w. rewrite /update /FlagStateUpdateOps.
apply functional_extensionality => f'. by case: (f == f').
(* Different flag *)
move => fs f1 f2 v1 v2 neq. rewrite /update /FlagStateUpdateOps. 
apply functional_extensionality => f. 
case E1: (f2 == f) => //.
case E2: (f1 == f) => //. rewrite (elimT (eqP) E1) in neq. 
by rewrite (elimT (eqP) E2) in neq. 
Qed. 

Definition noFlags : FlagState := fun _ => FlagUnspecified. 

Definition getFlag (flags: FlagState) (f: Flag) := flags f.
Coercion getFlag : FlagState >-> Funclass. 

Open Scope update_scope. 
Definition updateFlag (flags: FlagState) (f: Flag) (b:FlagVal) := flags ! f := b.
Definition forgetFlag (flags: FlagState) (f: Flag) := flags !f := FlagUnspecified.

(* The only flags we care about! *)
Definition CF:Flag := #0. 
Definition PF:Flag := #2. 
Definition ZF:Flag := #6. 
Definition SF:Flag := #7. 
Definition OF:Flag := #11. 

Definition initialFlagState := 
  noFlags
  ! CF := mkFlag false
  ! PF := mkFlag false
  ! ZF := mkFlag false
  ! SF := mkFlag false
  ! OF := mkFlag false.

Require Import String.
Definition showFlag s res := (if res is mkFlag f then (if f then s else ".") else "?")%string.
Definition flagsToString (f:FlagState) :=
  (showFlag "C" (f CF) ++
   showFlag "P" (f PF) ++ 
   showFlag "Z" (f ZF) ++
   showFlag "S" (f SF) ++ 
   showFlag "O" (f OF))%string.

