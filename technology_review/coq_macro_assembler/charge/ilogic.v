(*---------------------------------------------------------------------------
    This file axiomatises the inference rules of an intuitionistic logic and
    offers some parametric instances to make it straightforward to create a new
    logic that satisfies those axioms. The purpose is to factor out what the
    assertion logic and specification logic of a separation logic framework
    have in common.
  ---------------------------------------------------------------------------*)
Require Import Setoid Morphisms RelationClasses Program.Basics Omega.
Require Import CSetoid.

Set Implicit Arguments.
Unset Strict Implicit.

(* The natural numbers in descending order. *)
Global Instance ge_Pre: PreOrder ge.
Proof. repeat constructor. hnf. eauto with arith. Qed.

(* These tactics are meant to relieve the user from remembering morphism names.
   In most cases they will apply the most general morphism for the arity
   requested. *)
(* TODO: move this somewhere more general. *)
Ltac postcancel := unfold Basics.flip; trivial.
Ltac cancel1 :=
  apply (proper_prf (Proper := _: Proper (_ ==> _) _));
  postcancel.
Ltac cancel2 :=
  apply (proper_prf (Proper := _: Proper (_ ==> _ ==> _) _));
  postcancel.
Ltac cancel3 :=
  apply (proper_prf (Proper := _: Proper (_ ==> _ ==> _ ==> _) _));
  postcancel.

Class Inhabited A := { cinhabited : inhabited A}.

Instance blr: Inhabited nat.
Proof. split; split; apply 0. Qed.

Generalizable Variables Frm.

(* Logical connectives *)
Class ILogicOps Frm := {
  lentails: relation Frm;
  ltrue: Frm;
  lfalse: Frm;
  limpl: Frm -> Frm -> Frm;
  land: Frm -> Frm -> Frm;
  lor: Frm -> Frm -> Frm;
  lforall: forall {T}, (T -> Frm) -> Frm;
  lexists: forall {T}, (T -> Frm) -> Frm
}.

(* These notations have to sit strictly between level 80 (precendence of /\)
   and level 70 (precedence of =). *)
Infix "|--"  := lentails (at level 79, no associativity).
Infix "//\\"   := land (at level 75, right associativity).
Infix "\\//"   := lor (at level 76, right associativity).
Infix "-->>"   := limpl (at level 77, right associativity).
Notation "'Forall' x : T , p" := 
  (lforall (fun x : T => p)) (at level 78, x ident, right associativity).
Notation "'Forall' x , p" := 
  (lforall (fun x => p)) (at level 78, x ident, right associativity).
Notation "'Exists' x : T , p" := 
  (lexists (fun x : T => p)) (at level 78, x ident, right associativity).
Notation "'Exists' x , p" := 
  (lexists (fun x => p)) (at level 78, x ident, right associativity).

(* Axioms of an intuitionistic logic, presented in a sequent calculus style
   with singleton contexts on the left of the turnstile. This form is
   particularly suited for the undisciplined context manipulation that tends to
   happen in separation logic.

   Every connective has a number of L-rules and a number of R-rules describing
   what can be done to prove a goal that has the connective as the head symbol
   of the left, respectively right, side of a turnstile. The notable exception
   to this pattern is implication, which is required to be the right adjoint of
   conjunction. This makes singleton contexts work. *)
Class ILogic Frm {ILOps: ILogicOps Frm} := {
  lentailsPre:> PreOrder lentails;
  ltrueR: forall C, C |-- ltrue;
  lfalseL: forall C, lfalse |-- C;
  lforallL: forall T x (P: T -> Frm) C, P x |-- C -> lforall P |-- C;
  lforallR: forall T (P: T -> Frm) C, (forall x, C |-- P x) -> C |-- lforall P;
  lexistsL: forall T (P: T -> Frm) C, (forall x, P x |-- C) -> lexists P |-- C;
  lexistsR: forall T x (P: T -> Frm) C, C |-- P x -> C |-- lexists P;
  landL1: forall P Q C, P |-- C  ->  P //\\ Q |-- C;
  landL2: forall P Q C, Q |-- C  ->  P //\\ Q |-- C;
  lorR1:  forall P Q C, C |-- P  ->  C |-- P \\// Q;
  lorR2:  forall P Q C, C |-- Q  ->  C |-- P \\// Q;
  landR:  forall P Q C, C |-- P  ->  C |-- Q  ->  C |-- P //\\ Q;
  lorL:   forall P Q C, P |-- C  ->  Q |-- C  ->  P \\// Q |-- C;
  landAdj: forall P Q C, C |-- (P -->> Q) -> C //\\ P |-- Q;
  limplAdj: forall P Q C, C //\\ P |-- Q -> C |-- (P -->> Q)
}.
Implicit Arguments ILogic [[ILOps]].

Notation "|-- P" := (ltrue |-- P) (at level 85, no associativity).
Hint Extern 0 (?x |-- ?x) => reflexivity.
Hint Extern 0 (_ |-- ltrue) => apply ltrueR.
Hint Extern 0 (lfalse |-- _) => apply lfalseL.
Hint Extern 0 (?P |-- ?Q) => (is_evar P; reflexivity) || (is_evar Q; reflexivity).
 
Section ILogicExtra.
  Context `{IL: ILogic Frm}.
  
  Definition lequiv P Q := P |-- Q /\ Q |-- P.
  Definition lpropand (p: Prop) Q := Exists _: p, Q.
  Definition lpropimpl (p: Prop) Q := Forall _: p, Q.
End ILogicExtra.

Infix "/\\" := lpropand (at level 75, right associativity).
Infix "->>" := lpropimpl (at level 77, right associativity).
Infix "-|-"  := lequiv (at level 85, no associativity).

Hint Extern 0 (?x -|- ?x) => reflexivity.
Hint Extern 0 (?P -|- ?Q) => (is_evar P; reflexivity) || (is_evar Q; reflexivity).

Section ILogicMorphisms.
  Context `{IL: ILogic Frm}.
  
  Global Instance lequivEqu : Equivalence lequiv.
  Proof.
    unfold lequiv. constructor; red.
    + split; reflexivity.
    + intuition.
    + intros P Q R [HPQ HQP] [HQR HRQ]; 
      split; etransitivity; eassumption.
  Qed.

  Global Instance lequiv_lentails : subrelation lequiv lentails.
  Proof. firstorder. Qed.
  Global Instance lequiv_inverse_lentails: subrelation lequiv (inverse lentails).
  Proof. firstorder. Qed.

  Global Instance lforall_lentails_m T:
    Proper (pointwise_relation T lentails ++> lentails) lforall.
  Proof.
    intros P P' HP. apply lforallR; intro x; apply lforallL with x.
    rewrite HP; reflexivity.
  Qed.

  Global Instance lforall_lequiv_m T:
    Proper (pointwise_relation T lequiv ++> lequiv) lforall.
  Proof.
    intros P P' HP; split; apply lforall_lentails_m; intro x; apply HP.
  Qed.

  Global Instance lexists_lentails_m T:
    Proper (pointwise_relation T lentails ++> lentails) lexists.
  Proof.
    intros P P' HP. apply lexistsL; intro x; apply lexistsR with x.
    rewrite HP; reflexivity.
  Qed.

  Global Instance lexists_lequiv_m T:
    Proper (pointwise_relation T lequiv ++> lequiv) lexists.
  Proof.
    intros P P' HP; split; apply lexists_lentails_m; intro x; apply HP.
  Qed.

  Global Instance : Proper (lequiv ==> lequiv ==> iff) lequiv.
  Proof.
    intuition.
  Qed.

  Global Instance lequiv_lentails_m : Proper (lequiv ==> lequiv ==> iff) lentails.
  Proof.
    cbv; intuition; (etransitivity; [etransitivity|]); eassumption.
  Qed.

  Global Instance lentails_lentails_m: Proper (lentails --> lentails ++> impl) lentails.
  Proof.
    intuition.
  Qed.

  Global Instance land_lentails_m:
    Proper (lentails ++> lentails ++> lentails) land.
  Proof.
    intros P P' HP Q Q' HQ.
    apply landR; [apply landL1 | apply landL2]; assumption.
  Qed.

  Global Instance land_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) land.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply land_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance lor_lentails_m:
    Proper (lentails ++> lentails ++> lentails) lor.
  Proof.
    intros P P' HP Q Q' HQ.
    apply lorL; [apply lorR1 | apply lorR2]; assumption.
  Qed.

  Global Instance lor_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lor.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lor_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance limpl_lentails_m:
    Proper (lentails --> lentails ++> lentails) limpl.
  Proof.
    intros P P' HP Q Q' HQ; red in HP.
    apply limplAdj; rewrite <- HQ, HP; apply landAdj; reflexivity.
  Qed.

  Global Instance limpl_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) limpl.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply limpl_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance lpropand_lentails_m:
    Proper (impl ++> lentails ++> lentails) lpropand.
  Proof.
    intros p p' Hp Q Q' HQ.
    apply lexistsL; intro H. apply lexistsR; [apply Hp|]; assumption.
  Qed.

  Global Instance lpropand_lequiv_m:
    Proper (iff ==> lequiv ==> lequiv) lpropand.
  Proof.
    intros p p' Hp Q Q' HQ.
    split; cancel2; unfold impl; (apply Hp || apply HQ).
  Qed.
    
  Global Instance lpropimpl_lentails_m:
    Proper (impl --> lentails ++> lentails) lpropimpl.
  Proof.
    intros p p' Hp Q Q' HQ.
    apply lforallR; intro H. apply lforallL; [apply Hp|]; assumption.
  Qed.
  
  Global Instance lpropimpl_lequiv_m:
    Proper (iff ==> lequiv ==> lequiv) lpropimpl.
  Proof.
    intros p p' Hp Q Q' HQ.
    split; cancel2; unfold flip, impl; (apply Hp || apply HQ).
  Qed.
    
End ILogicMorphisms.

Section ILogicFacts.
  Context `{IL: ILogic Frm}.
  
  (* Experiments with proof search. *)
  Ltac landR :=
    repeat match goal with
    | |- _ |-- _ //\\ _ => apply landR
    end.
  
  Ltac landL :=
    repeat match goal with
    | |- ?L1 //\\ ?L2 |-- ?R =>
        match L1 with
        | context [R] => apply landL1
        | _ =>
          match L2 with
          | context [R] => apply landL2
          end
        end
    end.

  Lemma landC P Q: P //\\ Q -|- Q //\\ P.
  Proof. split; landR; landL; reflexivity. Qed.

  Lemma landA P Q R: (P //\\ Q) //\\ R -|- P //\\ (Q //\\ R).
  Proof. split; landR; landL; reflexivity. Qed.

  (* Derivable but useful *)
  Lemma lpropandTrue P : True /\\ P -|- P. 
  Proof. unfold lpropand. split; [apply lexistsL | apply lexistsR]; trivial. Qed. 

  Lemma lpropandFalse P : False /\\ P -|- lfalse. 
  Proof. unfold lpropand. split; [apply lexistsL |]; intuition. Qed.
  
  (* Left-rule for limpl. This breaks the discipline of the ILogic presentation
     since the implication is not strictly the top symbol of the left-hand side,
     but it remains a convenient rule. *)
  Lemma limplL P Q CL CR (HP: CL |-- P) (HR: Q //\\ CL |-- CR) :
    (P -->> Q) //\\ CL |-- CR.
  Proof.
    rewrite <-HR, <-HP. apply landR; [apply landAdj |apply landL2]; reflexivity.
  Qed.

  Lemma lpropandL (p: Prop) Q C (H: p -> Q |-- C) :
    p /\\ Q |-- C.
  Proof. apply lexistsL; intro Hp. apply H; assumption. Qed.

  Lemma lpropandR C (p: Prop) Q (Hp: p) (HQ: C |-- Q) :
    C |-- p /\\ Q.
  Proof. apply lexistsR with Hp; assumption. Qed.

  Lemma lpropimplL (p: Prop) (Q C: Frm) (Hp: p) (HQ: Q |-- C) :
    p ->> Q |-- C.
  Proof. apply lforallL with Hp; assumption. Qed.
  
  Lemma lpropimplR C (p: Prop) Q (H: p -> C |-- Q) :
    C |-- p ->> Q.
  Proof. apply lforallR; intro Hp. apply H; assumption. Qed.

  (* Special case of limplAdj/landAdj when there is just ltrue on the lhs *)
  Lemma limplValid P Q:
    |-- P -->> Q <->
    P |-- Q.
  Proof.
    split; intro H.
    - etransitivity; [apply landR; [apply ltrueR|reflexivity]|].
      apply landAdj; assumption.
    - apply limplAdj. apply landL2; assumption.
  Qed.

  Lemma landexistsD {A} (f : A -> Frm) (P : Frm) :
    (Exists a, f a) //\\ P -|- Exists a, (f a //\\ P).
  Proof.
    split.
    + apply landAdj; apply lexistsL; intro a; 
      apply limplAdj; apply lexistsR with a; reflexivity.
    + apply lexistsL; intro a; apply landR.
      - apply landL1; apply lexistsR with a; reflexivity.
      - apply landL2; reflexivity.
  Qed.

  Lemma landforallDL {A} (f : A -> Frm) (P : Frm) :
    (Forall a, f a) //\\ P |-- Forall a, (f a //\\ P).
  Proof.
    apply lforallR; intro a; apply landR.
    + apply landL1; apply lforallL with a; reflexivity.
    + apply landL2; reflexivity.
  Qed.

  Lemma landforallDR {A} {H: Inhabited A} (f : A -> Frm) (P : Frm) :
    Forall a, (f a //\\ P) |-- (Forall a, f a) //\\ P.
  Proof.
    apply landR.
    + apply lforallR; intro a; apply lforallL with a; apply landL1; reflexivity.
    + destruct H as [[a]]. apply lforallL with a; apply landL2; reflexivity.
  Qed.

  Lemma lpropandexistsD {A} (f : A -> Frm) (P : Prop) :
    P /\\ (Exists a, f a) -|- Exists a, (P /\\ f a).
  Proof.
    split.
    + apply lpropandL; intro HP; apply lexistsL; intro a.
      apply lexistsR with a; apply lpropandR; auto.
    + apply lexistsL; intro a; apply lpropandL; intro HP; apply lpropandR; [assumption|].
      apply lexistsR with a; reflexivity.
  Qed.

  Lemma lpropandforallDL {A} (f : A -> Frm) (P : Prop) :
    P /\\ (Forall a, f a) |-- Forall a, (P /\\ f a).
  Proof.
    apply lpropandL; intro HP; apply lforallR; intro a; apply lpropandR; [assumption|].
    apply lforallL with a; reflexivity.
  Qed.

  Lemma lpropandforallDR {A} {H: Inhabited A} (f : A -> Frm) (P : Prop) :
    Forall a, (P /\\ f a) |-- P /\\ (Forall a, f a).
  Proof.
    assert ((P /\\ ltrue) //\\ (Forall a, f a) |-- P /\\ (Forall a, f a)) as H0.
    + apply landAdj. apply lpropandL; intros HP. apply limplAdj; apply landL2.
      apply lpropandR; [assumption|].
      apply lforallR; intro a; apply lforallL with a; reflexivity.
    + rewrite <- H0; apply landR.
      - destruct H as [[a]]; apply lforallL with a;
        apply lpropandL; intros; apply lpropandR; auto.
      - apply lforallR; intro a; apply lforallL with a;
        apply lpropandL; intros; reflexivity.
  Qed.
  
End ILogicFacts.

(* Most of the connectives in ILogicOps are redundant. They can be derived from
   lexists, lforall and limpl, and the choice of limpl is unique up to lequiv
   since it is an adjoint. *)
Section ILogicEquiv.
  Context `{IL: ILogic Frm}.
  
  Lemma land_is_forall P Q :
    P //\\ Q -|- Forall b : bool, if b then P else Q.
  Proof.
    split.
    - apply lforallR; intro x; destruct x.
      + apply landL1; reflexivity.
      + apply landL2; reflexivity.
    - apply landR.
      + apply lforallL with true; reflexivity.
      + apply lforallL with false; reflexivity.
  Qed.

  Lemma lor_is_exists P Q:
    P \\// Q -|- Exists b : bool, if b then P else Q.
  Proof.
    split.
    - apply lorL.
      + apply lexistsR with true; reflexivity.
      + apply lexistsR with false; reflexivity.
    - apply lexistsL; intro x; destruct x.
      + apply lorR1; reflexivity.
      + apply lorR2; reflexivity.
  Qed.

  Lemma ltrue_is_forall:
    ltrue -|- Forall x: Empty_set, Empty_set_rect _ x.
  Proof. split; [apply lforallR|]; intuition. Qed.

  Lemma lfalse_is_exists:
    lfalse -|- Exists x: Empty_set, Empty_set_rect _ x.
  Proof. split; [|apply lexistsL]; intuition. Qed.
  
End ILogicEquiv.
(*
(* Tactics for doing forward reasoning from a hypothesis. *)
Lemma lforwardR {Frm} `{IL: ILogic Frm} P Q R:
  Q |-- R -> P |-- Q -> P |-- R.
Proof. intros; etransitivity; eassumption. Qed.
Tactic Notation "lforwardR" hyp(H) := eapply lforwardR in H; last first.

Lemma lforwardL {Frm} `{IL: ILogic Frm} P Q R:
  P |-- Q -> Q |-- R -> P |-- R.
Proof. intros; etransitivity; eassumption. Qed.
Tactic Notation "lforwardL" hyp(H) := eapply lforwardL in H; last first.

(* This tactic is a ilogic version of [move:]. Can it be done easier? *)
Ltac lrevert x :=
  move: x;
  match goal with
  | |- ?P -> _ |-- ?G =>
      move=> x;
      transitivity (P ->> G);
      [clear x | apply lpropimplL; [exact x|reflexivity] ]
  | |- forall a, _ |-- @?G a =>
      move=> x;
      transitivity (lforall G);
      [clear x | apply lforallL with x; reflexivity ]
  end.
*)

(* Given a pre-ordered type T and an intuitionistic logic with carrier Frm,
   the space of functions in [T -> Frm] that are monotone with respect to
   entailment is another intuitionistic logic. The semantics are standard
   Kripke semantics; i.e., all connectives are pointwise lifted from Frm,
   except implication, which is special. *)
Section ILogic_Pre.
  Context T (ord: relation T) {ord_Pre: PreOrder ord}.
  Context `{IL: ILogic Frm}.

  Record ILPreFrm := mkILPreFrm {
    ILPreFrm_pred :> T -> Frm;
    ILPreFrm_closed: forall t t': T, ord t t' ->
      ILPreFrm_pred t |-- ILPreFrm_pred t'
  }.

  Notation "'mk'" := @mkILPreFrm.

  Global Instance ILPreFrm_m (P: ILPreFrm): Proper (ord ++> lentails) P.
  Proof.
    intros t t' Ht. apply ILPreFrm_closed; assumption.
  Qed.

  Local Obligation Tactic :=
    repeat match goal with
    | |- ord _ _ -> _ => intros Hord; try setoid_rewrite Hord; reflexivity
    | |- _ => intro
    end.

  Program Definition ILPre_Ops : ILogicOps ILPreFrm := {|
    lentails P Q := forall t:T, P t |-- Q t;
    ltrue        := mk (fun t => ltrue) _;
    lfalse       := mk (fun t => lfalse) _;
    limpl    P Q := mk (fun t => Forall t', ord t t' ->> P t' -->> Q t') _;
    land     P Q := mk (fun t => P t //\\ Q t) _;
    lor      P Q := mk (fun t => P t \\// Q t) _;
    lforall  A P := mk (fun t => Forall a, P a t) _;
    lexists  A P := mk (fun t => Exists a, P a t) _
  |}.

  Local Existing Instance ILPre_Ops.

  Program Definition ILPre_ILogic : ILogic ILPreFrm.
  Proof.
    split; unfold lentails; simpl; intros.
    - split; red; [reflexivity|].
      intros P Q R HPQ HQR t. transitivity (Q t); [apply HPQ | apply HQR].
    - apply ltrueR.
    - apply lfalseL.
    - apply lforallL with x; apply H.
    - apply lforallR; intros; apply H.
    - apply lexistsL; intros; apply H.
    - apply lexistsR with x; apply H.
    - apply landL1; intuition.
    - apply landL2; intuition.
    - apply lorR1; intuition.
    - apply lorR2; intuition.
    - apply landR; intuition.
    - apply lorL; intuition.
    - apply landAdj.
      etransitivity; [apply H|]. clear H. apply lforallL with t.
      apply lpropimplL; reflexivity.
    - apply lforallR; intro t'. apply lpropimplR; intro Hord. apply limplAdj.
      rewrite ->Hord; intuition.
  Qed.

  Global Instance ILPreFrm_pred_m:
    Proper (lentails ++> ord ++> lentails) ILPreFrm_pred.
  Proof.
    intros P P' HP t t' Ht. rewrite ->Ht. apply HP.
  Qed.
End ILogic_Pre.

Implicit Arguments ILPreFrm [T [ILOps]].
Implicit Arguments mkILPreFrm [T ord Frm ILOps].

(** If [Frm] is a ILogic, then the function space [T -> Frm] is also an ilogic,
    for any type [T]. All connectives are just pointwise liftings. *)
Section ILogic_Fun.
  Context (T: Type) `{TType: type T}.
  Context `{IL: ILogic Frm}.

  Record ILFunFrm := mkILFunFrm {
    ILFunFrm_pred :> T -> Frm;
    ILFunFrm_closed: forall t t': T, t === t' ->
      ILFunFrm_pred t |-- ILFunFrm_pred t'
  }.

  Global Instance ILFunFrmEquiv {H: Equiv Frm} : Equiv ILFunFrm := {
     equiv p q := forall x, p x === q x 
  }.

  Global Instance ILfunFrmType `{H: type Frm} : type ILFunFrm.
  Proof.
    split.
    + intros x y; reflexivity.
    + intros x y Hxy z; symmetry. apply Hxy.
    + intros x y z Hxy Hyz a; etransitivity;
      [apply Hxy | apply Hyz].
  Qed.
  
  Notation "'mk'" := @mkILFunFrm.

  Program Definition ILFun_Ops : ILogicOps ILFunFrm := {|
    lentails P Q := forall t:T, P t |-- Q t;
    ltrue        := mk (fun t => ltrue) _;
    lfalse       := mk (fun t => lfalse) _;
    limpl    P Q := mk (fun t => P t -->> Q t) _;
    land     P Q := mk (fun t => P t //\\ Q t) _;
    lor      P Q := mk (fun t => P t \\// Q t) _;
    lforall  A P := mk (fun t => Forall a, P a t) _;
    lexists  A P := mk (fun t => Exists a, P a t) _
  |}.
  Next Obligation.
    apply limplAdj.
    rewrite <- ILFunFrm_closed; [|symmetry; eassumption].
    apply limplL; [reflexivity| apply landL1; apply ILFunFrm_closed; assumption].
  Qed.
  Next Obligation.
    apply landR; [apply landL1 | apply landL2]; apply ILFunFrm_closed; assumption.
  Qed.
  Next Obligation.
    apply lorL; [apply lorR1 | apply lorR2]; apply ILFunFrm_closed; assumption.
  Qed.
  Next Obligation.
    apply lforallR; intro a; apply lforallL with a; apply ILFunFrm_closed; assumption.
  Qed.
  Next Obligation.
    apply lexistsL; intro a; apply lexistsR with a; apply ILFunFrm_closed; assumption.
  Qed.
  
  Local Existing Instance ILFun_Ops.

  Program Definition ILFun_ILogic : ILogic ILFunFrm. 
  Proof.
    split; unfold lentails; simpl; intros.
    - split; red; [reflexivity|].
      intros P Q R HPQ HQR t. transitivity (Q t); [apply HPQ | apply HQR].
    - apply ltrueR.
    - apply lfalseL.
    - apply lforallL with x; apply H.
    - apply lforallR; intros; apply H.
    - apply lexistsL; intros; apply H.
    - apply lexistsR with x; apply H.
    - apply landL1; intuition.
    - apply landL2; intuition.
    - apply lorR1; intuition.
    - apply lorR2; intuition.
    - apply landR; intuition.
    - apply lorL; intuition.
    - apply landAdj; intuition.
    - apply limplAdj; intuition.
  Qed.

End ILogic_Fun.

Implicit Arguments ILFunFrm [[ILOps] [e]].
Implicit Arguments mkILFunFrm [T Frm ILOps].

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.

Program Definition ILFun_eq {T R} {ILOps: ILogicOps R} {ILogic: ILogic R} (P : T -> R) : 
  @ILFunFrm T _ R ILOps := 
  @mkILFunFrm T eq R ILOps P _.
Next Obligation.
  destruct H; simpl; reflexivity.
Qed.

(* Prop is an intuitionistic logic *)
Instance ILogicOps_Prop : ILogicOps Prop := {|
  lentails P Q := P -> Q;
  ltrue        := True;
  lfalse       := False;
  limpl    P Q := P -> Q;
  land     P Q := P /\ Q;
  lor      P Q := P \/ Q;
  lforall  T F := forall x:T, F x;
  lexists  T F := exists x:T, F x
|}.

Instance ILogic_Prop : ILogic Prop.
Proof.
  split; cbv; firstorder.
Qed.

(* Make the setoid system realize that these two are the same thing (in the
   direction that seems useful. *)
Instance: subrelation lentails Basics.impl.
Proof. reflexivity. Qed.

(* It does not seem possible to add a morphism that applies to an arbitrary
   function application. This is sometimes needed when we make a logic out of a
   function space, so the workaround is to rewrite by this lemma. *)
(*
Lemma lentails_eq T `{HT: type T} (P: ILFunFrm T Prop) t:
  P t <-> equiv t |-- P.
Proof.
  split.
  - simpl. intros; subst; assumption.
  - simpl. intros; firstorder.
Qed.

Lemma ILFun_exists_eq T (P: T -> Prop):
  P -|- Exists s, P s /\\ eq s.
Proof.
  split; intros s Hs.
  - exists s. constructor; intuition.
  - firstorder; subst; assumption.
Qed.
*)
(* Coq tends to unfold lentails on [simpl], which triggers unfolding of
   several other connectives. When that happens, the goal can become quite
   unreadable. The workaround is to make the definition of entailment and
   connectives opaque. If a module wants to unfold those definitions, it should
   do [Transparent IL?_Ops], where ? is Pre or Fun. *)

Global Opaque ILPre_Ops.
Global Opaque ILFun_Ops.
