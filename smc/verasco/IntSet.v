Require Import
  Coqlib Utf8 String PrintPos ToString
  Integers
  Maps TreeAl
  LatticeSignatures AdomLib
  IntervalDomain.

Module P := Tree_Properties( ZTree ).

Definition int_set : Type := ZTree.t unit.
Definition proj (i: int) : Z := Int.unsigned i.

Notation "x ∈ S" := (ZTree.get x S = Some tt): int_set_scope.

Local Open Scope int_set_scope.

Definition Mem (x: int) (S: int_set) := (proj x) ∈ S.

Definition mem x S : { x ∈ S } + { ¬ x ∈ S }.
refine (
  match ZTree.get x S as k return ZTree.get x S = k → { x ∈ S } + { ¬ x ∈ S } with
    | Some tt => left
    | None => fun K => right (fun H => _)
  end (eq_refl _)).
Proof.
  rewrite K in H. discriminate.
Defined.

Notation "x ∈? S" := (mem x S) (at level 19): int_set_scope.

Definition empty : int_set := ZTree.empty _.

Definition forallb (f: Z → bool) (s: int_set) : bool :=
  P.for_all s (fun x _ => f x).

Lemma forallb_forall {f x r} :
  forallb f r = true → x ∈ r → f x = true.
Proof.
  intros H. unfold forallb in H. rewrite P.for_all_correct in H. intros X; exact (H x tt X).
Qed.

Definition of_list' (l: list int) : int_set → int_set :=
  List.fold_left
    (fun acc i => ZTree.set (proj i) tt acc)
    l.

Definition of_list (l: list int) : int_set :=
  of_list' l (ZTree.empty _).

Lemma of_list'_iff : ∀ l acc i, List.In i l ∨ (proj i) ∈ acc <-> (proj i) ∈ (of_list' l acc).
Proof.
  refine (rev_ind _ _ _).
  intuition.
  intros x l IH.
  intros acc i. unfold of_list'. rewrite in_app, fold_left_app.
  fold (of_list' l).
  simpl. rewrite ZTree.gsspec. destruct ZTree.elt_eq as [H|H].
  intuition. left. right. left. case (Int.eq_dec i x); auto. intros K. elim (DLib.unsigned_inj i x K H).
  split; intros K. apply IH. intuition. elim H. congruence.
  specialize (IH acc i). destruct (proj2 IH K); intuition.
Qed.

Lemma of_list_iff : ∀ l i, List.In i l <-> (proj i) ∈ (of_list l).
Proof.
  intros l i. generalize (of_list'_iff l (ZTree.empty _) i).
  rewrite ZTree.gempty. intuition. discriminate.
Qed.

Definition fold {A} (f: A → int → A) : int_set → A → A :=
  ZTree.fold (fun x y (_:unit) => f x (Int.repr y)).

Definition as_list (m: int_set) : list int :=
  fold (λ l i, i :: l) m nil.

Lemma as_list_iff : ∀ m i, List.In i (as_list m) ↔ ∃ j, j ∈ m ∧ Int.repr j = i.
Proof.
  set (F := λ l (i: int), i :: l).
  cut (∀ acc m i, List.In i (fold F m acc) ↔ (∃ j, j ∈ m ∧ Int.repr j = i) ∨ List.In i acc).
  intros H m i. specialize (H nil m i). intuition.
  intros acc m.
  unfold fold, F.
  refine (P.fold_rec (λ l i _, Int.repr i :: l)
                     (λ m l, ∀ i, List.In i l ↔ (∃ j, j ∈ m ∧ Int.repr j = i) ∨ List.In i acc)
                     acc _ _ _
         ).
+ intros m0 m' a H H0 i. setoid_rewrite <- H. auto.
+ intros i. split. auto. intros [(j & J & _)|H]. rewrite ZTree.gempty in J. discriminate. exact H.
+ intros m0 a k () H H0 H1 i. split.
  - intros [EQ|IN].
    left. exists k. split. rewrite ZTree.gss. reflexivity. exact EQ.
    destruct (proj1 (H1 _) IN) as [(j & J & K)|K]. 2: auto.
    left. exists j. intuition.
    rewrite ZTree.gsspec. destruct ZTree.elt_eq. reflexivity. exact J.
  - intros [(j & J & K) | K ].
    rewrite ZTree.gsspec in J. destruct ZTree.elt_eq.
    left. congruence.
    right. exact (proj2 (H1 _) (or_introl (ex_intro _ j (conj J K)))).
    right. exact (proj2 (H1 _) (or_intror K)).
Qed.

Definition fs_size (x: int_set) : N :=
  ZTree.fold (fun n _ _ => Nsucc n) x N0.

Definition int_set_LE (x y: int_set) :=
  ∀ i : Z, i ∈ x → i ∈ y.

Definition int_set_LE_dec (x y: int_set) : { int_set_LE x y } + { ¬ int_set_LE x y }.
Proof.
  case_eq (forallb (fun i => i ∈? y) x); intros H; [left|right].
  intros i I. generalize (forallb_forall H I). destruct mem.
    easy. intros K. apply False_ind. discriminate.
  unfold forallb in H. rewrite P.for_all_false in H.
  destruct H as (u & () & H & K).
  intros E. specialize (E u H).
  destruct mem. discriminate. auto.
Defined.

Definition is_empty (x: int_set) : bool :=
  int_set_LE_dec x (ZTree.empty _).

Lemma is_empty_correct (x: int_set) :
  is_empty x = true →
  ∀ y, ¬ y ∈ x.
Proof.
  unfold is_empty.
  destruct int_set_LE_dec as [H|]. 2: intros K; apply False_ind; discriminate.
  intros _ y K.
  generalize (H y K).
  rewrite ZTree.gempty. discriminate.
Qed.

Definition singleton (i: int) : int_set := ZTree.set (proj i) tt (ZTree.empty _).

Definition union (x y: int_set) : int_set :=
  ZTree.combine
    (fun l r =>
       match l, r with
       | None, None => None
       | Some tt, _
       | _, Some tt => Some tt
       end) x y.

Lemma union_comm (x y: int_set) : union x y = union y x.
Proof. unfold union. now apply ZTree.combine_commut; intros [()|] [()|]. Qed.

Lemma union_in_l (x y: int_set) :
  ∀ i: Z, i ∈ x → i ∈ union x y.
Proof.
  unfold union. intros i I. rewrite ZTree.gcombine; auto. rewrite I; auto.
Qed.

Lemma union_in_r (x y: int_set) :
  ∀ i: Z, i ∈ y → i ∈ union x y.
Proof.
  rewrite union_comm. apply union_in_l.
Qed.

Definition intersection (x y: int_set) : int_set :=
  ZTree.combine
    (fun l r =>
       match l, r with
       | Some tt, Some tt => Some tt
       | _, _ => None
       end) x y.

Lemma intersection_correct (x y: int_set) :
  ∀ i : Z, i ∈ x → i ∈ y → i ∈ intersection x y.
Proof.
  intros i X Y.
  unfold intersection. rewrite ZTree.gcombine; auto.
  rewrite X, Y; auto.
Qed.

Lemma intersection_exact (x y: int_set) :
  ∀ i : Z, i ∈ intersection x y → i ∈ x ∧ i ∈ y.
Proof.
  intros i. unfold intersection. rewrite ZTree.gcombine; auto.
  repeat destruct ZTree.get as [()|]; intuition.
Qed.

Instance toString : ToString int_set :=
  { to_string x :=
  ("{ " ++
        ZTree.fold
        (fun s i _ => string_of_z i ++ "; " ++ s)
        x
        "}"
  )%string
  }.

(** Returns the minimal and maximal elements. None if empty. *)
Definition min_max (interp: Z → Z) (x: int_set) : option (Z * Z) :=
  ZTree.fold
    (fun m k _ =>
       match m with
       | None => Some (k,k)
       | Some (l, r) =>
         let k' := interp k in
         let l' := interp l in
         let r' := interp r in
         if Z_le_gt_dec k' l' then Some (k, r)
         else if Z_le_gt_dec r' k' then Some (l, k)
              else m
       end)
    x
    None.

Lemma min_max_spec (interp: Z → Z) (x: int_set) :
  match min_max interp x with
  | None => is_empty x = true
  | Some (l,r) => l ∈ x ∧ r ∈ x ∧ ∀ i, i ∈ x → interp l <= interp i <= interp r
  end.
Proof.
  unfold min_max.
  apply P.fold_rec.
  intros m m' [(l,r)|] H; trivial.
  intros (A & B & C). repeat rewrite <- H. split; auto; split; auto.
  intros i I. rewrite <- H in I. auto.
  intros E. unfold is_empty. destruct int_set_LE_dec as [|GT]. auto.
  elim GT. intros y Y. rewrite <- H in Y. elim (is_empty_correct _ E y Y).
  unfold is_empty. destruct int_set_LE_dec as [|GT]; auto. elim GT. now intro.
  intros m [(l,r)|] k () H H0.
  intros (A & B & C).
  repeat destruct Z_le_gt_dec;
  (split;[|split;[|intros i]]);
  repeat rewrite ZTree.gss;
  repeat rewrite ZTree.gsspec;
  repeat destruct ZTree.elt_eq;
  auto.
  subst. intros _. intuition. apply Zle_trans with (interp l); auto. apply C; auto.
  intros I. specialize (C _ I). intuition.
  intros _. subst. intuition.
  intros I. specialize (C _ I). intuition.
  intros _. subst. intuition.
  intros H1.
  repeat (split;[apply ZTree.gss|]).
  intros i. rewrite ZTree.gsspec. destruct ZTree.elt_eq. subst. intuition.
  intros K. elim (is_empty_correct _ H1 _ K).
Qed.

Definition fint_set : Type := noitpo int_set.

Definition fempty : fint_set := Just (ZTree.empty _).

Definition fs_widen (old new: int_set) : fint_set :=
  if int_set_LE_dec new old
  then Just old
  else
    let j : int_set := union old new in
    if N.leb 10%N (fs_size j) (* FIXME: get rid of this magic num. *)
    then All
    else Just j.

Instance fs_gamma : gamma_op fint_set int := fun x =>
  match x with
  | All => fun _ => True
  | Just s => fun i => proj i ∈ s
  end.

Lemma fempty_gamma i : ¬ fs_gamma fempty i.
Proof.
  simpl. rewrite ZTree.gempty. discriminate.
Qed.

Definition int_set_pl : pre_lattice int_set :=
  {| pl_leb x y := int_set_LE_dec x y
   ; pl_join x y := Just (union x y)
   ; pl_widen x y := fs_widen x y
  |}.

Instance int_set_wl : weak_lattice fint_set :=
  weak_lattice_of_pre_lattice int_set_pl.

Lemma int_set_adom : adom fint_set int int_set_wl fs_gamma.
Proof.
  apply adom_of_pre_lattice.
  split.
+ (* gamma monotone *)
  unfold γ. intros x y; simpl.
  destruct int_set_LE_dec as [H|].
    intros _ a A. now apply H.
  discriminate.
+ (* join sound *)
  unfold γ.
  intros x y. simpl. intros i I.
  unfold union. red. rewrite ZTree.gcombine; auto.
  repeat (destruct ZTree.get as [()|]; auto). intuition.
Qed.

Definition fs_reduce (x: int_set) : fint_set+⊥ :=
  if is_empty x
  then Bot
  else NotBot (Just x).

Definition fs_meet (x y: fint_set) : fint_set+⊥ :=
  match x, y with
  | All, _ => NotBot y
  | _, All => NotBot x
  | Just x', Just y' => fs_reduce (intersection x' y')
  end.

Lemma fs_meet_sound : ∀ x y: fint_set, (γ x) ∩ (γ y) ⊆ γ (fs_meet x y).
Proof.
  intros [|x] [|y]; try now intuition.
  intros a (X & Y). simpl. unfold fs_reduce.
  case_eq (is_empty (intersection x y)).
  intros K. elim (is_empty_correct _ K (proj a)).
  apply intersection_correct; auto.
  intros _. simpl. apply intersection_correct; auto.
Qed.

Lemma fs_meet_glb : ∀ x y: fint_set, γ (fs_meet x y) ⊆ (γ x) ∩ (γ y).
Proof.
  intros [|x] [|y]; try now intuition.
  intros i. simpl. unfold fs_reduce.
  case_eq (is_empty (intersection x y)). intuition.
  intros _. apply intersection_exact.
Qed.

Definition fs_const : int → fint_set := @Just _ ∘ singleton.

Definition fs_booleans : fint_set :=
  Just (union (singleton Int.zero) (singleton Int.one)).

Definition map (f: Z → Z) (s: int_set) : int_set :=
  ZTree.fold (fun m k _ => ZTree.set (f k) tt m) s (ZTree.empty unit).

Lemma map_in f (s: int_set) : ∀ x, x ∈ s → f x ∈ map f s.
Proof.
  unfold map.
  apply P.fold_rec.
  intros m m' a H H0 x.
  rewrite <- H. auto.
  intros x. repeat rewrite ZTree.gempty. intuition.
  intros m a k () H H0 H1 x.
  repeat rewrite ZTree.gsspec.
  repeat destruct ZTree.elt_eq. auto.
  apply False_ind. subst. intuition.
  auto.
  auto.
Qed.

Definition fs_unop (op: int → int) : fint_set → fint_set+⊥ :=
  fun x =>
    match x with
    | All => NotBot x
    | Just x' => NotBot (Just (map (fun i => proj (op (Int.repr i))) x'))
    end.

Definition map2 (f: Z → Z → Z) (l r: int_set) : int_set :=
  ZTree.fold (fun m i _ =>
                ZTree.fold (fun m j _ => ZTree.set (f i j) tt m) r m ) l (ZTree.empty unit).

Lemma map2_in f (l r: int_set) : ∀ x y, x ∈ l → y ∈ r → f x y ∈ map2 f l r.
Proof.
  unfold map2.
  apply P.fold_rec.
  intros m m' a H H0 x y H1 H2. apply H0. rewrite H. auto. auto.
  intros i y K. apply False_ind. rewrite ZTree.gempty in K. discriminate.
  intros m a k () H H0 H1 x y H2 H3.
  rewrite ZTree.gsspec in H2.
  destruct ZTree.elt_eq. subst. clear H2.
  generalize (fun x A => H1 x y A H3). clear H1.
  Focus 2. specialize (H1 x y H2 H3). clear H2 H3.
  eapply P.fold_rec; auto.
  intros m0 a0 k0 () H2 H3 H4.
  rewrite ZTree.gsspec.
  destruct ZTree.elt_eq; auto.
  generalize dependent r.
  intros r.
  apply P.fold_rec.
  intros m0 m' a0 H1 H2 H3 H4. apply H2; auto. rewrite H1; auto.
  intros K. apply False_ind. rewrite ZTree.gempty in K. discriminate.
  intros m0 a0 k0 () H1 H2 H3 H4 H5.
  rewrite ZTree.gsspec in *.
  repeat (destruct ZTree.elt_eq; auto).
  subst. intuition.
Qed.

Definition fs_binop (op: int → int → int) (x: fint_set) (y: fint_set) : fint_set+⊥ :=
  match x, y with
  | All, _
  | _, All => NotBot All
  | Just x', Just y' => NotBot (Just (map2 (fun a b => proj (op (Int.repr a) (Int.repr b))) x' y'))
  end.

Definition int_set_unsigned_range (x: int_set) :=
  match min_max (fun i => i) x with
  | None => Bot
  | Some (l,r) => NotBot {| Interval.min := l; Interval.max := r |}
  end.

Definition int_set_signed_range (x: int_set) :=
  let interp := Int.signed ∘ Int.repr in
  match min_max interp x with
  | None => Bot
  | Some (l,r) => NotBot {| Interval.min := interp l; Interval.max := interp r |}
  end.

Definition fs_range (x: fint_set) :=
  match x with
  | All => fun s => NotBot (match s with Signed => Interval.top | Unsigned => Interval.utop end)
  | Just x' => fun s =>
                 match s with
                 | Signed => int_set_signed_range x'
                 | Unsigned => int_set_unsigned_range x'
                 end
  end.

Definition fs_is_in_itv (l r: int) (x: fint_set) : bool :=
  match x with
  | All => false
  | Just x' => forallb (fun i => negb (Int.lt r (Int.repr i)) && negb (Int.lt (Int.repr i) l)) x'
  end.
