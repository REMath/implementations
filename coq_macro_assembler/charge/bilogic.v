Require Import Setoid Morphisms RelationClasses Program.Basics. 
Require Import ilogic iltac CSetoid.

Set Implicit Arguments.
Unset Strict Implicit.

Section BILogic.
  Context {A : Type}.
  Context `{IL: ILogic A}.

  Class BILOperators (A : Type) := {
    empSP : A;
    sepSP : A -> A -> A;
    wandSP : A -> A -> A
  }.

  Class BILogic {BILOp: BILOperators A} := {
    bilil :> ILogic A;
    sepSPC1 P Q : sepSP P Q |-- sepSP Q P;
    sepSPA1 P Q R : sepSP (sepSP P Q) R |-- sepSP P (sepSP Q R);
    wandSepSPAdj P Q R : sepSP P Q |-- R <-> P |-- wandSP Q R;
    bilsep P Q R : P |-- Q -> sepSP P R |-- sepSP Q R;
    empSPR P : sepSP P empSP -|- P
  }.

End BILogic.

Implicit Arguments BILogic [[BILOp] [ILOps]].

Notation "a '**' b"  := (sepSP a b)
  (at level 75, right associativity).
Notation "a '-*' b"  := (wandSP a b)
  (at level 77, right associativity).

Section CoreInferenceRules.

  Context {A} `{BILogic A}.

  Definition strict P := forall Q, ((Q ** ltrue) //\\ P) |-- (Q ** (Q -->> P)).

  Lemma wandSPAdj P Q C (HSep: C ** P |-- Q) : C |-- P -* Q.
  Proof. 
    apply wandSepSPAdj; assumption.
  Qed.

  Lemma sepSPAdj P Q C (HWand: C |-- P -* Q) : C ** P |-- Q.
  Proof. 
    apply wandSepSPAdj; assumption.
  Qed.

  Lemma sepSPC (P Q : A) : P ** Q -|- Q ** P.
  Proof.
    split; apply sepSPC1.
  Qed.

  Lemma sepSPA2 (P Q R : A) : P ** (Q ** R) |-- (P ** Q) ** R.
  Proof.
    rewrite sepSPC.
    etransitivity; [apply sepSPA1|].
    rewrite sepSPC.
    etransitivity; [apply sepSPA1|].
    rewrite sepSPC.
    reflexivity.
  Qed.

  Lemma sepSPA (P Q R : A) : (P ** Q) ** R -|- P ** (Q ** R).
  Proof.
    split; [apply sepSPA1 | apply sepSPA2].
  Qed.
    
  Lemma wandSPI (P Q R : A) (HQ : P ** Q |-- R) : (P |-- Q -* R).
  Proof.
    apply wandSPAdj; assumption.
  Qed.

  Lemma wandSPE (P Q R T : A) (HQR: Q |-- T -* R) (HP : P |-- Q ** T) : P |-- R.
  Proof.
    apply sepSPAdj in HQR.
    rewrite <- HQR, HP. reflexivity.
  Qed.

  Lemma empSPL P : empSP ** P -|- P.
  Proof.
    rewrite sepSPC; apply empSPR.
  Qed.

  Lemma bilexistsscL {T} (P : A) (Q : T -> A):
    Exists x : T, P ** Q x |-- P ** Exists x : T, Q x.
  Proof.
    apply lexistsL; intros x.
    rewrite sepSPC. etransitivity; [|rewrite <- sepSPC; reflexivity].
    apply bilsep. eapply lexistsR; reflexivity.
  Qed.

  Lemma bilexistsscR {T} (P : A) (Q : T -> A) :
    P ** (Exists x : T, Q x) |-- Exists x : T, P ** Q x.
  Proof.
    rewrite sepSPC; rewrite wandSepSPAdj.
    apply lexistsL; intros x; rewrite <- wandSPAdj. reflexivity.
    eapply lexistsR; rewrite sepSPC; reflexivity.
  Qed.

  Lemma bilexistssc {T} (P : A) (Q : T -> A) :
    Exists x : T, P ** Q x -|- P ** Exists x : T, Q x.
  Proof.
    split; [apply bilexistsscL | apply bilexistsscR].
  Qed.

  Lemma bilforallscR {T} (P : A) (Q : T -> A) :
    P ** (Forall x : T, Q x) |-- Forall x : T, P ** Q x.
  Proof.
    lforallR; intro x.
    rewrite sepSPC; etransitivity; [|rewrite <- sepSPC; reflexivity].
    apply bilsep. lforallL x; reflexivity.
  Qed.

End CoreInferenceRules.

Section BILogicMorphisms.
  Context {A : Type} `{BIL: BILogic A}.

  Global Instance sepSP_lentails_m:
    Proper (lentails ++> lentails ++> lentails) sepSP.
  Proof.
    intros P P' HP Q Q' HQ.
    etransitivity; [apply bilsep; exact HP|].
    rewrite -> sepSPC.
    etransitivity; [apply bilsep; exact HQ|].
    rewrite -> sepSPC. reflexivity.
  Qed.  

  Global Instance sepSP_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) sepSP.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply sepSP_lentails_m; (apply HP || apply HQ).
  Qed.  

  Global Instance wandSP_lentails_m:
    Proper (lentails --> lentails ++> lentails) wandSP.
  Proof.
    intros P P' HP Q Q' HQ. red in HP.
    apply wandSPAdj. rewrite <- HQ, -> HP.
    apply sepSPAdj. reflexivity.
  Qed.

  Global Instance wandSP_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) wandSP.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply wandSP_lentails_m; (apply HP || apply HQ).
  Qed.  

End BILogicMorphisms.

Section DerivedInferenceRules.

  Context {A} `{BILogic A}.

  Lemma sepSP_falseR P : P ** lfalse -|- lfalse.
  Proof.
    rewrite lfalse_is_exists; rewrite <- bilexistssc.
    split; apply lexistsL; intro x; destruct x.
  Qed.

  Lemma sepSP_falseL P : lfalse ** P -|- lfalse.
  Proof.
    rewrite -> sepSPC; apply sepSP_falseR.
  Qed.

  Lemma land_sepSP P Q R : (P//\\Q) ** R |-- (P ** R) //\\ (Q**R).  
  Proof. apply landR. apply sepSP_lentails_m. apply landL1. reflexivity. reflexivity. 
                      apply sepSP_lentails_m. apply landL2. reflexivity. reflexivity. 
  Qed. 

End DerivedInferenceRules.

Require Import sepalg.

Section BISepAlg.
  Context {A} `{sa : SepAlg A}.
  Context {B} `{IL: ILogic B}.

  Open Scope sa_scope.

  Program Instance SABIOps: BILOperators (ILFunFrm A B) := {
    empSP := mkILFunFrm e (fun x => sa_unit === x /\\ ltrue) _;
    sepSP P Q := mkILFunFrm e (fun x => Exists x1, Exists x2, sa_mul x1 x2 x /\\
                                                P x1 //\\ Q x2) _;
    wandSP P Q := mkILFunFrm e (fun x => Forall x1, Forall x2, sa_mul x x1 x2 ->> 
                                                 P x1 -->> Q x2) _
  }.
  Next Obligation.
    lpropandL; intro Ht; lpropandR; [apply ltrueR|].
    rewrite <- H; assumption.
  Qed.
  Next Obligation.
    lexistsL; intro x1; lexistsL; intro x2.
    lexistsR x1; lexistsR x2.
    lpropandL; intro Ht.
    lpropandR; [reflexivity |rewrite <- H; assumption].
  Qed.
  Next Obligation.
    lforallR; intro x1; lforallR; intro x2.
    lforallL x1; lforallL x2.
    lpropimplR Ht; lpropimplL; [rewrite H; assumption | reflexivity].
  Qed.

  Local Existing Instance ILFun_Ops.
  Local Existing Instance ILFun_ILogic.
  Local Transparent ILFun_Ops.
  
  Definition SABILogic : BILogic (ILFunFrm A B).
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl.
      lexistsL; intro x1. lexistsL; intro x2.
      lexistsR x2; lexistsR x1.
      lpropandL; intro H1.
      lpropandR; [intuition | apply sa_mulC; assumption].
    + intros P Q R x; simpl.
      lexistsL; intro x1; lexistsL; intro x2; lexistsL; intro x3; lexistsL; intro x4.
      lexistsR x3.
      lpropandL; intro Hx; lpropandL; intro Hx1.
      pose proof sa_mulA as H.
      apply sa_mulC in Hx.
      specialize (H _ _ _ _ _ Hx Hx1).
      destruct H as [x5 [Hx2 Hx5]].
      lexistsR x5; lpropandR; [|assumption].
      apply landR; [apply landL1; apply landL1; reflexivity|].
      lexistsR x4; lexistsR x2.
      apply sa_mulC in Hx5.
      lpropandR; [|assumption].
      rewrite landA; apply landL2; reflexivity.
    + intros P Q R; split; intros H x; simpl.
      - lforallR; intro x1; lforallR; intro x2.
        apply lpropimplR; intro Hx1.
        apply limplAdj.
        specialize (H x2); simpl in H.
        rewrite <- H.
        lexistsR x; lexistsR x1.
        lpropandR; [reflexivity|assumption].
      - lexistsL; intro x1; lexistsL; intro x2; lpropandL; intro Hx.
        specialize (H x1); simpl in H.
        setoid_rewrite H.
        lforallL x2; lforallL x.
        lpropimplL; [assumption| apply landAdj; reflexivity].
    + intros P Q R H x; simpl.
      lexistsL; intro x1; lexistsL; intro x2.
      lexistsR x1; lexistsR x2; specialize (H x1); setoid_rewrite H.
      reflexivity.
    + intros P; split; intros x; simpl.
      - lexistsL; intro x1; lexistsL; intro x2.
        lpropandL; intro H1; lpropandL; intro H2.
        apply landL1; rewrite <- H2 in H1.
        apply ILFunFrm_closed.
        assert (sa_mul x1 sa_unit x1) by (apply sa_unitI).
        eapply sa_mul_eqR; eassumption.
      - lexistsR x; lexistsR sa_unit.
        lpropandR; [|apply sa_unitI].
        lpropandR; [apply landR; auto|].
        replace (e sa_unit sa_unit) with (sa_unit === sa_unit) by reflexivity.
        reflexivity.
  Qed.

End BISepAlg.
  
Global Opaque SABIOps.

