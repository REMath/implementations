Require Import Setoid Morphisms RelationClasses Program.Basics Omega.
Require Import ilogic.

Set Implicit Arguments.
Unset Strict Implicit.

Section LaterSect.
  Context {A : Type}.
  Context `{ILOps: ILogicOps A}.
          

Class ILLOperators (A : Type) := {
  illater : A -> A
}.

Class ILLater {ILLOps: ILLOperators A} := {
  illogic :> ILogic A;                                           
  spec_lob P : illater P |-- P -> |-- P;
  spec_later_weaken P : P |-- illater P;
  spec_later_impl P Q : illater (P -->> Q) -|- (illater P) -->> (illater Q);
  spec_later_forall {T} (F : T -> A) : illater (Forall x:T, F x) -|- Forall x:T, illater (F x);
  spec_later_exists {T} (F : T -> A) : Exists x : T, illater (F x) |-- illater (Exists x : T, F x);
  spec_later_exists_inhabited {T} (F : T -> A) : inhabited T -> illater (Exists x : T, F x) |-- Exists x : T, illater (F x)
}.
End LaterSect.
Implicit Arguments ILLater [[ILLOps] [ILOps]].
Notation "'|>' a"  := (illater a) (at level 71).

Section ILogicLaterCoreRules.
  Context {A} `{IL: ILLater A}.

  Global Instance spec_later_entails:
    Proper (lentails ==> lentails) illater.
  Proof.
    intros P P' HP.
    rewrite <- limplValid, <- spec_later_impl, <- spec_later_weaken, limplValid.
    assumption.
  Qed.

  Global Instance spec_later_equiv:
    Proper (lequiv ==> lequiv) illater.
  Proof.
    intros P P' HP. split; cancel1; rewrite HP; reflexivity.
  Qed.

  Lemma spec_later_and P P': |>(P //\\ P') -|- |>P //\\ |>P'.
  Proof.
    do 2 rewrite land_is_forall; rewrite spec_later_forall;
    split; apply lforallR; intro x; apply lforallL with x;
    destruct x; reflexivity.
  Qed.

  Lemma spec_later_or P P': |>(P \\// P') -|- |>P \\// |>P'.
  Proof.
    do 2 rewrite lor_is_exists; split;
    [rewrite spec_later_exists_inhabited; [|firstorder]| rewrite <- spec_later_exists];
    apply lexistsL; intro x; apply lexistsR with x; destruct x; reflexivity.
  Qed.    

  Lemma spec_later_true : |>ltrue -|- ltrue.
  Proof.
    split; [intuition|].
    rewrite ltrue_is_forall, spec_later_forall.
    apply lforallR; intro x; destruct x.
  Qed.

End ILogicLaterCoreRules.

Hint Rewrite
  @spec_later_and
  @spec_later_impl
  @spec_later_true
  @spec_later_forall
  : push_later.

Print Acc.

Section ILogic_nat.
  Context {A : Type}.
  Context `{IL: ILogic A}.

  Program Definition ILLaterPreOps : ILLOperators (ILPreFrm ge A)  := 
    {|
      illater P := mkILPreFrm (fun x => Forall y : nat, y < x ->> P y) _
    |}.
  Next Obligation.
    apply lforallR; intro x; apply lforallL with x.
    apply lpropimplR; intro Hx.
    apply lpropimplL; unfold complement in *; intros; [omega | reflexivity].
  Qed.

Local Transparent ILPre_Ops.
Local Existing Instance ILLaterPreOps.
Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.

  Definition ILLaterPre : ILLater (ILPreFrm ge A).
  Proof.
    split.
    + apply _.
    + intros P H x; induction x. 
      - rewrite <- H; simpl; apply lforallR; intro y.
        apply lpropimplR; intros; omega.
      - rewrite <- H; simpl; apply lforallR; intro y.
        apply lpropimplR; intros Hyx.
        assert (x >= y) by omega.
        rewrite <- ILPreFrm_closed; eassumption.
    + intros P x; simpl; apply lforallR; intro y.
      apply lpropimplR; intros Hyx.
      apply ILPreFrm_closed; omega.
    + intros P Q; split; intro x; simpl.
      - apply lforallR; intro y.
        apply lpropimplR; intros Hxy.
        apply limplAdj.
        apply lforallR; intro z.
        apply lpropimplR; intros Hzy.
        apply landAdj.
        apply lforallL with z.
        apply lpropimplL; [omega|].
        apply lforallL with z.
        apply lpropimplL; [omega|].
        apply limplAdj.
        apply limplL.
        apply lforallL with z.
        apply lpropimplL; [assumption| reflexivity].        
        apply landL1; reflexivity.
      - eapply lforallR; intro y.
        eapply lpropimplR; intros Hyx.
        eapply lforallR; intro z.
        eapply lpropimplR; intro Hyz.
        eapply lforallL with (z + 1).
        eapply lpropimplL.
        omega.
        eapply limplAdj.
        eapply limplL.
        eapply lforallR; intro w. eapply lpropimplR; intro Hwy.
        eapply ILPreFrm_closed.
        omega.
        eapply landL1.
        eapply lforallL with z.
        eapply lpropimplL; [firstorder|].
        eapply lequivEqu.
    + intros T F; split; simpl; intro x.
      - apply lforallR; intro a.
        apply lforallR; intro y.
        apply lpropimplR; intro Hyx.
        apply lforallL with y.
        apply lpropimplL; [assumption|].
        apply lforallL with a; reflexivity.
      - apply lforallR; intro y.
        apply lpropimplR; intro Hyx.
        apply lforallR; intro a.
        apply lforallL with a.
        apply lforallL with y.
        apply lpropimplL; [assumption|reflexivity].
    + intros T F x; simpl.
      apply lexistsL; intro a.
      apply lforallR; intro y.
      apply lpropimplR; intro Hyx.
      apply lexistsR with a.
      apply lforallL with y.
      apply lpropimplL; [assumption|reflexivity].
    + intros T F Hin x; simpl.      
      inversion Hin as [a]; destruct x.
      - apply lexistsR with a.
        apply lforallR; intro y.
        apply lpropimplR; intro Hyx; omega.
      - apply lforallL with x.
        apply lpropimplL; [omega|].
        apply lexistsL; intro b.
        apply lexistsR with b.
        apply lforallR; intro y.
        apply lpropimplR; intro Hyx.
        apply ILPreFrm_closed.
        omega.
  Qed.

End ILogic_nat.

Global Opaque ILLaterPreOps.
