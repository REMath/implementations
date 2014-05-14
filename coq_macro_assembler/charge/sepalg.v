Require Import Setoid Morphisms RelationClasses Program.Basics Omega.
Require Import CSetoid.

Set Implicit Arguments.
Unset Strict Implicit.

Section FunEq.
  Context A `{eT: type A}.

  Global Instance FunEquiv {T} : Equiv (T -> A) := {
    equiv P Q := forall a, P a === Q a
  }.

  Global Instance FunType T : type (T -> A).
  Proof. firstorder. Qed.
End FunEq.

(* Separation algebras *)
Section SepAlgSect.
  Class SepAlgOps T `{eT : type T}:= {
    sa_unit : T;
    (* sa_mul s1 s2 s if s = s1*s2 *)
    sa_mul : T -> T -> T -> Prop
  }.
  
  Class SepAlg T `{SAOps: SepAlgOps T} : Type := {
    sa_mul_eqL a b c d : sa_mul a b c -> c === d -> sa_mul a b d;
    sa_mul_eqR a b c d : sa_mul a b c -> sa_mul a b d -> c === d;
    sa_mon a b c   : a === b -> sa_mul a c === sa_mul b c;
    sa_mulC a b        : sa_mul a b === sa_mul b a;
    sa_mulA a b c      : forall bc abc, sa_mul a bc abc -> sa_mul b c bc ->
                                        exists ac, sa_mul b ac abc /\ sa_mul a c ac;
    sa_unitI a         : sa_mul a sa_unit a
  }.

End SepAlgSect.

Implicit Arguments SepAlgOps [[e] [eT]].
Implicit Arguments SepAlg [[e] [eT] [SAOps]].

Section SepAlgCompat.
  Context A `{SA: SepAlg A}.
  
  Definition compat (a b : A) := exists s, sa_mul a b s.
  Definition subheap (a b : A) := exists c, sa_mul a c b.
  
  Lemma sa_mulC2 a b c : sa_mul a b c <-> sa_mul b a c.
  Proof.
    apply sa_mulC.
  Qed.

End SepAlgCompat.

Module SepAlgNotations.
Notation "a '·' b" := (sa_mul a b) (at level 50, left associativity) : sa_scope.
Notation "a '·' b |-> c" := (sa_mul a b c) (at level 52, no associativity) : sa_scope.
Notation "^" := sa_unit : sa_scope.
Notation "a # b" := (compat a b) (at level 70, no associativity) : sa_scope.
Notation "a <= b" := (subheap a b) (at level 70, no associativity) : sa_scope.
End SepAlgNotations.

Instance sa_mul_equiv_proper T `{SAP : SepAlg T} :
  Proper (equiv ==> equiv ==> equiv ==> equiv) sa_mul.
Proof.
  intros x y Heqxy t u Heqtu s v Heqsv.
  transitivity (sa_mul y t s); [apply sa_mon; assumption|].
  etransitivity; [apply sa_mulC| etransitivity; [|apply sa_mulC]].
  etransitivity; [apply sa_mon; eassumption|].
  split; intros; (eapply sa_mul_eqL; [eassumption|firstorder]).
Qed.

Import SepAlgNotations.

Delimit Scope sa_scope with sa.

Instance subheap_preo A `{sa : SepAlg A} : PreOrder (@subheap A e eT SAOps).
Proof. 
  split.
  + intros s; eexists; apply sa_unitI.
  + intros s0 s1 s2 [s10 HEq1] [s21 HEq2].
    pose proof (sa_mulA).
    apply sa_mulC in HEq2.
    specialize (H _ _ _ _ _ HEq2 HEq1).
    destruct H as [s3 [HEqs2 HEqs3]].
    exists s3; assumption.
Qed.

Instance compat_symm Σ `{sa : SepAlg Σ} : Symmetric (compat (A := Σ)).
Proof.
  intros s s0 [s1 Hs]; exists s1; apply sa_mulC; assumption.
Qed.

Section Properties.
  Context Σ `{sa : SepAlg Σ}.
  Open Scope sa_scope.

  Global Instance sa_subheap_equiv_proper :
    Proper (equiv ==> equiv ==> iff) (subheap (A := Σ)).
  Proof.
    intros x y Heqxy t u Heqtu; split; [intros [s Heqxst] | intros [s Heqysu]]; exists s.
    + rewrite <- Heqxy, <- Heqtu; assumption.
    + rewrite Heqxy, Heqtu; assumption.
  Qed.

  Global Instance sa_compat_equiv_proper :
    Proper (equiv ==> equiv ==> iff) (compat (A := Σ)).
  Proof.
    intros x y Heqxy t u Heqtu; split; [intros [s Heqxst] | intros [s Heqysu]]; exists s.
    + rewrite <- Heqxy, <- Heqtu; assumption.
    + rewrite Heqxy, Heqtu; assumption.
  Qed.

  Lemma compat_subheap {r t : Σ} (s : Σ) (Hsr: r <= s) (Hst: s # t) : r # t.
  Proof.
    destruct Hsr as [sr Hsr]; destruct Hst as [st Hst].
    apply sa_mulC in Hst.
    apply sa_mulC in Hsr.
    pose proof sa_mulA.
    specialize (H _ _ _ _ _ Hst Hsr).
    destruct H as [u [Hst2 Hu]].
    exists u. apply sa_mulC; assumption.
  Qed.

  Close Scope sa_scope.

End Properties.

Implicit Arguments compat_subheap [[Σ] [e] [eT] [sa] [r] [t] [SAOps]].
