(*---------------------------------------------------------------------------
    This file axiomatises the inference rules of an intuitionistic logic and
    offers some parametric instances to make it straightforward to create a new
    logic that satisfies those axioms. The purpose is to factor out what the
    assertion logic and specification logic of a separation logic framework
    have in common.
  ---------------------------------------------------------------------------*)
Require Import ssreflect ssrbool.
Require Import Setoid Morphisms RelationClasses Program.Basics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* These tactics are meant to relieve the user from remembering morphism names.
   In most cases they will apply the most general morphism for the arity
   requested. *)
(* TODO: move this somewhere more general. *)
Ltac postcancel := rewrite /Basics.flip => //.
Ltac cancel1 :=
  apply (proper_prf (Proper := _: Proper (_ ==> _) _));
  postcancel.
Ltac cancel2 :=
  apply (proper_prf (Proper := _: Proper (_ ==> _ ==> _) _));
  postcancel.
Ltac cancel3 :=
  apply (proper_prf (Proper := _: Proper (_ ==> _ ==> _ ==> _) _));
  postcancel.

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
Hint Extern 0 (_ |-- ltrue) => apply: ltrueR.
Hint Extern 0 (lfalse |-- _) => apply: lfalseL.
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
    - by split.
    - intuition.
    - move => P Q R [HPQ HQP] [HQR HRQ].
      split; etransitivity; eassumption.
  Qed.

  Global Instance lequiv_lentails : subrelation lequiv lentails.
  Proof. firstorder. Qed.
  Global Instance lequiv_inverse_lentails: subrelation lequiv (inverse lentails).
  Proof. firstorder. Qed.

  Global Instance lforall_lentails_m T:
    Proper (pointwise_relation T lentails ++> lentails) lforall.
  Proof.
    move => F F' HF. apply: lforallR => x. apply: lforallL.
    red in HF. rewrite ->HF. reflexivity.
  Qed.

  Global Instance lforall_lequiv_m T:
    Proper (pointwise_relation T lequiv ++> lequiv) lforall.
  Proof.
    move => F F' HF. split; apply lforall_lentails_m => x; apply HF.
  Qed.

  Global Instance lexists_lentails_m T:
    Proper (pointwise_relation T lentails ++> lentails) lexists.
  Proof.
    move => F F' HF. apply: lexistsL => x. apply: lexistsR.
    red in HF. rewrite ->HF. reflexivity.
  Qed.

  Global Instance lexists_lequiv_m T:
    Proper (pointwise_relation T lequiv ++> lequiv) lexists.
  Proof.
    move => F F' HF. split; apply lexists_lentails_m => x; apply HF.
  Qed.

  Global Instance : Proper (lequiv ==> lequiv ==> iff) lequiv.
  Proof.
    intuition; (etransitivity; first etransitivity; eassumption).
  Qed.

  Global Instance : Proper (lequiv ==> lequiv ==> iff) lentails.
  Proof.
    cbv; intuition; (etransitivity; first etransitivity; eassumption).
  Qed.

  Global Instance : Proper (lentails --> lentails ++> impl) lentails.
  Proof.
    cbv; intuition; (etransitivity; first etransitivity; eassumption).
  Qed.

  Global Instance land_lentails_m:
    Proper (lentails ++> lentails ++> lentails) land.
  Proof.
    move => P P' HP Q Q' HQ.
    apply: landR; [exact: landL1 | exact: landL2].
  Qed.

  Global Instance land_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) land.
  Proof.
    move => P P' HP Q Q' HQ.
    split; apply land_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance lor_lentails_m:
    Proper (lentails ++> lentails ++> lentails) lor.
  Proof.
    move => P P' HP Q Q' HQ.
    apply: lorL; [exact: lorR1 | exact: lorR2].
  Qed.

  Global Instance lor_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lor.
  Proof.
    move => P P' HP Q Q' HQ.
    split; apply lor_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance limpl_lentails_m:
    Proper (lentails --> lentails ++> lentails) limpl.
  Proof.
    move => P P' HP Q Q' HQ. red in HP.
    apply: limplAdj. rewrite <-HQ. rewrite ->HP. exact: landAdj.
  Qed.

  Global Instance limpl_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) limpl.
  Proof.
    move => P P' HP Q Q' HQ.
    split; apply limpl_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance lpropand_lentails_m:
    Proper (impl ++> lentails ++> lentails) lpropand.
  Proof.
    move=> p p' Hp Q Q' HQ.
    apply: lexistsL => H. apply lexistsR; last done. by apply Hp.
  Qed.

  Global Instance lpropand_lequiv_m:
    Proper (iff ==> lequiv ==> lequiv) lpropand.
  Proof.
    move=> p p' Hp Q Q' HQ.
    split; cancel2; unfold impl; (apply Hp || apply HQ).
  Qed.
    
  Global Instance lpropimpl_lentails_m:
    Proper (impl --> lentails ++> lentails) lpropimpl.
  Proof.
    move=> p p' Hp Q Q' HQ.
    apply: lforallR => H. apply lforallL; last done. by apply Hp.
  Qed.
  
  Global Instance lpropimpl_lequiv_m:
    Proper (iff ==> lequiv ==> lequiv) lpropimpl.
  Proof.
    move=> p p' Hp Q Q' HQ.
    split; cancel2; unfold flip, impl; (apply Hp || apply HQ).
  Qed.
    
End ILogicMorphisms.

Section ILogicFacts.
  Context `{IL: ILogic Frm}.
  
  (* Experiments with proof search. *)
  Ltac landR :=
    repeat match goal with
    | |- _ |-- _ //\\ _ => apply: landR
    end.
  
  Ltac landL :=
    repeat match goal with
    | |- ?L1 //\\ ?L2 |-- ?R =>
        match L1 with
        | context [R] => apply: landL1
        | _ =>
          match L2 with
          | context [R] => apply: landL2
          end
        end
    end.

  Lemma landC P Q: P //\\ Q -|- Q //\\ P.
  Proof. split; landR; by landL. Qed.

  Lemma landA P Q R: (P //\\ Q) //\\ R -|- P //\\ (Q //\\ R).
  Proof. split; landR; by landL. Qed.

  (* Derivable but useful *)
  Lemma lpropandTrue P : True /\\ P -|- P. 
  Proof. rewrite /lpropand. split; [by apply lexistsL | by apply lexistsR]. Qed. 

  Lemma lpropandFalse P : False /\\ P -|- lfalse. 
  Proof. rewrite /lpropand. split; [by apply lexistsL | done]. Qed.
  
  Lemma lpropandT P : true /\\ P -|- P. 
  Proof. rewrite /lpropand. split; [by apply lexistsL | by apply lexistsR]. Qed. 

  Lemma lpropandF P : false /\\ P -|- lfalse. 
  Proof. rewrite /lpropand. split; [by apply lexistsL | done]. Qed.
  
  (* Left-rule for limpl. This breaks the discipline of the ILogic presentation
     since the implication is not strictly the top symbol of the left-hand side,
     but it remains a convenient rule. *)
  Lemma limplL P Q CL CR:
    CL |-- P ->
    Q //\\ CL |-- CR ->
    (P -->> Q) //\\ CL |-- CR.
  Proof.
    move=> HP HR. rewrite <-HR, <-HP. apply: landR; last exact: landL2.
    exact: landAdj.
  Qed.

  Lemma lpropandL (p: Prop) Q C:
    (p -> Q |-- C) ->
    p /\\ Q |-- C.
  Proof. move=> H. apply: lexistsL => Hp. exact: H. Qed.

  Lemma lpropandR C (p: Prop) Q:
    p ->
    C |-- Q ->
    C |-- p /\\ Q.
  Proof. move=> Hp HQ. by apply lexistsR with Hp. Qed.

  Lemma lpropimplL (p: Prop) (Q C: Frm):
    p ->
    Q |-- C ->
    p ->> Q |-- C.
  Proof. move=> Hp HQ. by apply lforallL with Hp. Qed.
  
  Lemma lpropimplR C (p: Prop) Q:
    (p -> C |-- Q) ->
    C |-- p ->> Q.
  Proof. move=> H. apply: lforallR => Hp. exact: H. Qed.

  (* Special case of limplAdj/landAdj when there is just ltrue on the lhs *)
  Lemma limplValid P Q:
    |-- P -->> Q <->
    P |-- Q.
  Proof.
    split => H.
    - etransitivity; [apply landR; [apply ltrueR|reflexivity]|].
      exact: landAdj.
    - apply: limplAdj. exact: landL2.
  Qed.
End ILogicFacts.

(* Most of the connectives in ILogicOps are redundant. They can be derived from
   lexists, lforall and limpl, and the choice of limpl is unique up to lequiv
   since it is an adjoint. *)
Section ILogicEquiv.
  Context `{IL: ILogic Frm}.
  
  Lemma land_is_forall P Q:
    P //\\ Q -|- Forall b, if b then P else Q.
  Proof.
    split.
    - apply: lforallR => [[|]].
      - exact: landL1.
      - exact: landL2.
    - apply: landR.
      - by apply lforallL with true.
      - by apply lforallL with false.
  Qed.

  Lemma lor_is_exists P Q:
    P \\// Q -|- Exists b, if b then P else Q.
  Proof.
    split.
    - apply: lorL.
      - by apply lexistsR with true.
      - by apply lexistsR with false.
    - apply: lexistsL => [[|]].
      - exact: lorR1.
      - exact: lorR2.
  Qed.

  Lemma ltrue_is_forall:
    ltrue -|- Forall x: Empty_set, Empty_set_rect _ x.
  Proof. split; last done. by apply: lforallR => [[]]. Qed.

  Lemma lfalse_is_exists:
    lfalse -|- Exists x: Empty_set, Empty_set_rect _ x.
  Proof. split; first done. by apply: lexistsL => [[]]. Qed.
End ILogicEquiv.

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
    move=> t t' Ht. exact: ILPreFrm_closed.
  Qed.

  Local Obligation Tactic :=
    repeat match goal with
    | |- ord _ _ -> _ => intros Hord; try setoid_rewrite Hord; reflexivity
    | |- _ => intro
    end.

  Global Program Instance ILPre_Ops : ILogicOps ILPreFrm := {|
    lentails P Q := forall t:T, P t |-- Q t;
    ltrue        := mk (fun t => ltrue) _;
    lfalse       := mk (fun t => lfalse) _;
    limpl    P Q := mk (fun t => Forall t', ord t t' ->> P t' -->> Q t') _;
    land     P Q := mk (fun t => P t //\\ Q t) _;
    lor      P Q := mk (fun t => P t \\// Q t) _;
    lforall  A P := mk (fun t => Forall a, P a t) _;
    lexists  A P := mk (fun t => Exists a, P a t) _
  |}.

  Global Instance ILPre_ILogic : ILogic ILPreFrm.
  Proof.
    split; rewrite /lentails /=; intros.
    - split; red => //.
      move => P Q R HPQ HQR t. by transitivity (Q t).
    - exact: ltrueR.
    - exact: lfalseL.
    - exact: lforallL.
    - exact: lforallR.
    - exact: lexistsL.
    - exact: lexistsR.
    - exact: landL1.
    - exact: landL2.
    - exact: lorR1.
    - exact: lorR2.
    - exact: landR.
    - exact: lorL.
    - apply: landAdj.
      etransitivity; first by apply H. clear H. apply lforallL with t.
      apply: lpropimplL; reflexivity.
    - apply: lforallR => t'. apply: lpropimplR => Hord. apply: limplAdj.
      by rewrite ->Hord.
  Qed.

  Global Instance ILPreFrm_pred_m:
    Proper (lentails ++> ord ++> lentails) ILPreFrm_pred.
  Proof.
    move=> P P' HP t t' Ht. rewrite ->Ht. apply HP.
  Qed.
End ILogic_Pre.

Implicit Arguments ILPreFrm [T [ILOps]].
Implicit Arguments mkILPreFrm [T ord Frm ILOps].

(** If [Frm] is a ILogic, then the function space [T -> Frm] is also an ilogic,
    for any type [T]. All connectives are just pointwise liftings. *)
Section ILogic_Fun.
  Context (T: Type).
  Context `{IL: ILogic Frm}.

  Global Program Instance ILFun_Ops : ILogicOps (T -> Frm) := {|
    lentails P Q := forall t:T, P t |-- Q t;
    ltrue        := fun t => ltrue;
    lfalse       := fun t => lfalse;
    limpl    P Q := fun t => P t -->> Q t;
    land     P Q := fun t => P t //\\ Q t;
    lor      P Q := fun t => P t \\// Q t;
    lforall  A P := fun t => Forall a, P a t;
    lexists  A P := fun t => Exists a, P a t
  |}.

  Global Instance ILFun_ILogic : ILogic (T -> Frm).
  Proof.
    split; rewrite /lentails /=; intros.
    - split; red => //. move => P Q R HPQ HQR t. by transitivity (Q t).
    - exact: ltrueR.
    - exact: lfalseL.
    - exact: lforallL.
    - exact: lforallR.
    - exact: lexistsL.
    - exact: lexistsR.
    - exact: landL1.
    - exact: landL2.
    - exact: lorR1.
    - exact: lorR2.
    - exact: landR.
    - exact: lorL.
    - exact: landAdj.
    - exact: limplAdj.
  Qed.
End ILogic_Fun.

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
Lemma lentails_eq T (P: T -> Prop) t:
  P t <-> eq t |-- P.
Proof.
  split.
  - simpl. by move=> ? ? <-.
  - simpl. by apply.
Qed.

Lemma ILFun_exists_eq T (P: T -> Prop):
  P -|- Exists s, P s /\\ eq s.
Proof.
  split => s Hs /=.
  - exists s. by constructor.
  - by case: Hs => s' [? <-].
Qed.

(* Coq tends to unfold lentails on [simpl], which triggers unfolding of
   several other connectives. When that happens, the goal can become quite
   unreadable. The workaround is to make the definition of entailment and
   connectives opaque. If a module wants to unfold those definitions, it should
   do [Transparent IL?_Ops], where ? is Pre or Fun. *)
Global Opaque ILPre_Ops.
Global Opaque ILFun_Ops.
