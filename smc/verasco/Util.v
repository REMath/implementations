Require Import Utf8 List.
Require Import DLib.

Set Implicit Arguments.

Section INV.

  Variables A B C : Type.
  
  Definition some_eq_inv (x y: A) :
    Some x = Some y → x = y :=
    λ H, match H with eq_refl => eq_refl _ end.

  Lemma None_not_Some (v: A) :
    None = Some v → ∀ X : Prop, X.
  Proof (λ H, match H with eq_refl => I end).

  Lemma false_eq_true_False : false ≠ true.
  Proof (λ H, match H in _ = b return if b then False else True with eq_refl => I end).

  Lemma false_not_true : false = true → ∀ P : Prop, P.
  Proof (λ H, match H in _ = b return if b then _ else _ with eq_refl => I end).

  Definition pair_eq_inv (x:A) (y:B) z w :
    (x,y) = (z,w) → x = z ∧ y = w :=
    λ H, match H with eq_refl => conj eq_refl eq_refl end.

  Definition triple_eq_inv (x: A) (y: B) (z: C) x' y' z' :
    (x,y,z) = (x',y',z') → (x = x' ∧ y = y') ∧ z = z' :=
    λ H, match H with eq_refl => conj (pair_eq_inv eq_refl) eq_refl end.

  Definition cons_eq_inv (x x': A) (l l': list A) :
    x :: l = x' :: l' → x = x' ∧ l = l' :=
    λ H, match H in _ = a return match a with nil => True | y :: m => x = y ∧ l = m end with eq_refl => conj eq_refl eq_refl end.

  Definition cons_nil_inv (x : A) (l: list A) :
    x :: l = nil → ∀ P : Prop, P :=
    λ H, match H in _ = a return match a with nil => ∀ P, P | _ => True end with eq_refl => I end.

  Definition eq_dec_of_beq (beq: A → A → bool) (beq_correct: ∀ a b : A, beq a b = true ↔ a = b)
             (x y: A) : { x = y } + { x ≠ y } :=
    (if beq x y as b return (b = true <-> x = y) → { x = y } + { x ≠ y }
     then λ H, left (proj1 H eq_refl)
     else λ H, right (λ K, false_eq_true_False (proj2 H K)))
      (beq_correct x y).

End INV.

Ltac eq_some_inv :=
  repeat match goal with
         | H : @None _ = Some _ |- _=>
           exact (None_not_Some H _)
         | H : Some _ = @None _ |- _=>
           exact (None_not_Some (eq_sym H) _)
         | H : Some ?a = Some ?b |- _ =>
           apply (@some_eq_inv _ a b) in H
         | H : _ :: _ = @nil _ |- _ =>
           exact (cons_nil_inv H _)
         | H : @nil = _ :: _ |- _ =>
           exact (cons_nil_inv (eq_sym H) _)
         | H : false = true |- _ =>
           exact (false_not_true H _)
         | H : true = false |- _ =>
           exact (false_not_true (eq_sym H) _)
         | H : (_, _) = (_, _) |- _ =>
           destruct (pair_eq_inv H); clear H
         end.

Notation "'do_opt' X <- A ; B" :=
 (match A with Some X => B | None => None end)
 (at level 200, X ident, A at level 100, B at level 200).

Definition option_bind A B (a: option A) (f: A → option B) : option B :=
  match a with Some a => f a | _ => None end.

Lemma fold_left_ext_m {A B} (f g: A → B → A) :
  (∀ u v, f u v = g u v) →
  ∀ l z, fold_left f l z = fold_left g l z.
Proof.
  intros EXT.
  induction l. reflexivity.
  simpl.
  congruence.
Qed.
  
Section MAPS.

  Variables A B C D : Type.

  Variable e : A → B.
  Variable f : A → B → C.
  Variable g : A → B → C → D.

  Definition rev_map_app (l: list A) (acc: list B) : list B :=
    fold_left (λ acc a, e a :: acc) l acc.

  Definition rev_map (l: list A) : list B :=
    rev_map_app l nil.

  Lemma rev_map_app_correct : ∀ l l', rev_map_app l l' = rev (map e l) ++ l'.
  Proof.
    unfold rev_map_app.
    induction l as [|x l IH] using rev_ind.
    reflexivity.
    intros l'.
    rewrite fold_left_app, map_app, rev_app_distr. simpl. congruence.
  Qed.

  Lemma rev_map_correct : ∀ l, rev_map l = rev (map e l).
  Proof.
    intros. unfold rev_map. rewrite rev_map_app_correct. intuition.
  Qed.

  Lemma rev_nil : ∀ l : list A, rev l = nil → l = nil.
  Proof. induction l. reflexivity. simpl. destruct (rev l); discriminate. Qed.

  Definition map' (l: list A) : list B :=
    rev' (fold_left (λ acc a, e a :: acc) l nil).

  Lemma map'_correct : ∀ l, map' l = map e l.
  Proof.
    intros l.
    unfold map'. erewrite <- rev_involutive.
    unfold rev'.
    rewrite <- rev_alt.
    f_equal.
    apply rev_map_correct.
  Qed.

  Definition map2 (l: list A) (m: list B) : list C :=
    fold_left (λ acc a, fold_left (λ acc b, f a b :: acc) m acc) l nil.

  Definition map2_spec (l: list A) (m: list B) : list C :=
    rev (flat_map (λ a, map (f a) m) l).

  Lemma map2_correct : ∀ l m, map2 l m = map2_spec l m.
  Proof.
    intros l m.
    unfold map2, map2_spec.
    rewrite (fold_left_ext_m _ (λ acc a, rev (map (f a) m) ++ acc)).
    now rewrite aux, app_nil_r.
    intros.
    now rewrite fold_left_cons_map_app.
  Qed.

  Corollary in_map2 l m a b :
    In a l → In b m → In (f a b) (map2 l m).
  Proof.
    intros L M.
    rewrite map2_correct. unfold map2_spec. rewrite <- in_rev.
    apply in_flat_map. exists a. split; auto.
    apply in_map; auto.
  Qed.

  Lemma map_cons_inv l b b' :
    map e l = b :: b' →
    ∃ a a', l = a :: a' ∧ b = e a ∧ map e a' = b'.
  Proof.
    destruct l as [|a a']; inversion 1.
    repeat econstructor.
  Qed.

  Lemma map_nil_inv l :
    map e l = nil → l = nil.
  Proof.
    destruct l. reflexivity. simpl; intros; eq_some_inv.
  Qed.

End MAPS.

Lemma map2_nil_inv A B C (f: A → B → C) l m :
  map2 f l m = nil → l = nil ∨ m = nil.
Proof.
  rewrite map2_correct. unfold map2_spec.
  intros H; generalize (rev_nil _ H); clear H.
  destruct l. auto. destruct m. auto. simpl. intros; eq_some_inv.
Qed.

Section FOLD2.
  (** Fold on two lists.
      The weak version ignores trailing elements of the longest list. *)
  Context (A B C: Type)
          (f: C → A → B → C)
          (ka: C → list A → C)
          (kb: C → list B → C).

  Fixpoint fold_left2_weak (la: list A) (lb: list B) (acc: C) {struct la} : C :=
    match la, lb with
    | a :: la, b :: lb => fold_left2_weak la lb (f acc a b)
    | nil, _
    | _, nil => acc
    end.

  Fixpoint fold_left2 (la: list A) (lb: list B) (acc: C) {struct la} : C :=
    match la, lb with
    | a :: la, b :: lb => fold_left2 la lb (f acc a b)
    | nil, nil => acc
    | la, nil => ka acc la
    | nil, lb => kb acc lb
    end.

End FOLD2.

Section FORALL2.
  Context (A B: Type)
          (P: A → B → bool).

  Local Open Scope bool_scope.

  Definition forallb2 (la: list A) (lb: list B) : bool :=
    fold_left2 (λ acc a b, acc && P a b) (λ _ _, false) (λ _ _, false) la lb true.

  Lemma forallb2_forall_aux la : ∀ b lb,
    fold_left2 (λ acc a b, acc && P a b) (λ _ _, false) (λ _ _, false) la lb b = true <->
    Forall2 (λ a b, P a b = true) la lb ∧ b = true.
  Proof.
    induction la as [|a la IH].
  - intros acc [|b lb]. intuition. split. easy. intros [H _]. inversion H.
  - intros acc [|b lb]. split. intuition. intros [H _]. inversion H.
    specialize (IH (acc && P a b) lb). destruct IH as [IH1 IH2].
    split. intros H. specialize (IH1 H).
    destruct IH1 as [X Y]. rewrite Bool.andb_true_iff in Y. destruct Y as [Y Y'].
    split. constructor; auto. auto.
    intros [H K]. inversion H. subst. simpl. apply IH2. intuition.
  Qed.

  Lemma forallb2_forall la lb : forallb2 la lb = true <-> Forall2 (λ a b, P a b = true) la lb.
  Proof.
    generalize (forallb2_forall_aux la true lb).
    intuition.
  Qed.

End FORALL2.
