(** Lattice signatures. *)

Require Import Utf8 String.
Require Import List Maps Coqlib Integers.

Definition incl {A} (P1 P2:A->Prop) :=
  forall a, P1 a -> P2 a.
(* Notation "P1 ⊆ P2" := (incl P1 P2)  (at level 20). *)
Notation "P1 ⊆ P2" := (forall a, P1 a -> P2 a)  (at level 20).
Notation "x ∈ P" := (P x) (at level 19, only parsing).
Notation "'℘' A" := (A -> Prop) (at level 0).
Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).
Notation "X ∩ Y" := (fun x => X x ∧ Y x) (at level 19).
Notation "X ∪ Y" := (fun x => X x ∨ Y x) (at level 19).
Notation "∅" := (fun _ => False).

(** * Definition of an abstract domain *)
Module Adom. (* Spurious module to work around an extraction bug. *)
Unset Elimination Schemes.
Class weak_lattice (A: Type) : Type := {
  leb: A -> A -> bool;
  top: A;
  join: A -> A -> A;
  widen: A -> A -> A
}.

Class gamma_op (A B: Type) : Type := γ : A -> ℘ B.
  
Record adom (A B:Type) (WL: weak_lattice A) (Gamma: gamma_op A B) : Prop := {
  gamma_monotone: forall {a1} {a2},
    leb a1 a2 = true -> γ a1 ⊆ γ a2;
  gamma_top: forall x, x ∈ γ top;
  join_sound: ∀ x y, γ x ∪ γ y ⊆ γ (join x y)
}.
Arguments gamma_monotone [A] [B] [WL] [Gamma] _ {a1} {a2} _ _ _.
End Adom.
Export Adom.

Notation "x ⊑ y" := (leb x y) (at level 39).
Notation "x ⊔ y" := (join x y) (at level 40).
Notation "x ∇ y" := (widen x y) (at level 40).
Notation "⊤" := top (at level 40).
(* Arguments γ {A} {B} {gamma_op} a b /. *)
(* Notation γ := gamma. *)

(** * Union of a list of abstract values *)
Section union_list.
Context {A B C:Type}.
Variable f : C -> A.
Variable bot : A.
Variable union : A -> A -> A.
Variable gamma : A -> B -> Prop.
Variable union_correct : forall ab1 ab2 m,
  gamma ab1 m \/ gamma ab2 m -> gamma (union ab1 ab2) m.

Fixpoint union_list' (l:list A) : A :=
  match l with
    | nil => bot
    | a::nil => a
    | a::q => union a (union_list' q)
  end.

Lemma union_list'_correct : forall l ab m,
  In ab l ->
  m ∈ gamma ab ->
  m ∈ gamma (union_list' l).
Proof.
  induction l; simpl.
  intuition.
  intros ab m [->|H] K; destruct l; intuition eauto.
  destruct H.
Qed.

Definition union_list (l: list A) : A :=
  match l with
  | nil => bot
  | a::q =>
    List.fold_left union q a
  end.

Lemma union_list_correct : forall l ab m,
  In ab l ->
  m ∈ gamma ab ->
  m ∈ gamma (union_list l).
Proof.
  unfold union_list.
  destruct l as [|a q]. intuition.
  revert q.
  refine (rev_ind _ _ _).
  intros ab m [->|()]. easy.
  intros b q HI.
  intros ab m.
  rewrite app_comm_cons, in_app, fold_left_app. simpl.
  intros [[->|H]|[->|()]] AB.
  apply union_correct. left. eapply HI; eauto. now left.
  apply union_correct. left. eapply HI; eauto. now right.
  apply union_correct. now right.
Qed.

Definition union_list_map (l: list C) : A :=
  match l with
  | nil => bot
  | a :: q => List.fold_left (λ u x, union u (f x)) q (f a)
  end.

Lemma union_list_map_correct l :
  union_list_map l = union_list (map f l).
Proof.
  unfold union_list_map, union_list.
  destruct l as [|a q]. reflexivity.
  induction q as [|b l IH] using rev_ind.
  reflexivity.
  simpl. rewrite fold_left_app, map_app, fold_left_app. simpl in *.
  now rewrite IH.
Qed.

End union_list.

Class EqDec (T: Type) := eq_dec : ∀ x y : T, { x = y } + { x ≠ y }.

Lemma eq_dec_true {T: Type} `{E: EqDec} x (A B: T):
  (if eq_dec x x then A else B) = A.
Proof. destruct eq_dec; congruence. Qed.
Lemma eq_dec_false {T: Type} `{E: EqDec} {x y}:
  x ≠ y →
  ∀ A B : T,
    (if eq_dec x y then A else B) = B.
Proof. destruct eq_dec; congruence. Qed.

Instance PosEqDec : EqDec positive := peq.
Instance ZEqDec : EqDec Z := zeq.
Instance IntEqDec : @EqDec Integers.int.
Proof.
  intros x y; generalize (Integers.Int.eq_spec x y).
  now destruct (Integers.Int.eq x y); auto.
Defined.

Instance ProdEqDec {X Y: Type} `{EqDec X} `{EqDec Y} : EqDec (X * Y).
Proof.
intros (x,y) (x',y').
destruct (eq_dec x x');[|right].
  destruct (eq_dec y y');[left|right];
  abstract congruence.
abstract congruence.
Defined.

Definition upd `{X: Type} `{EqDec X} {Y} (f: X → Y) (p: X) (v:Y) :=
  fun q => if eq_dec q p then v else f q.

Lemma upd_s `{X: Type} `{EqDec X} {Y} (f: X → Y) p v:
  (upd f p v) p = v.
Proof. unfold upd. case (eq_dec p p); tauto. Qed.

Lemma upd_o `{X: Type} `{EqDec X} {Y} (f: X → Y) p v p' :
  p' ≠ p → (upd f p v) p' = f p'.
Proof. unfold upd. case (eq_dec p' p); tauto. Qed.
