Require Import
  Coqlib
  Maps
  DLib.

Set Implicit Arguments.

Module Type TYPE_EQ.
  Variable s: Type.
  Variable t: Type.
  Variable t_of_s : s -> t.
  Variable s_of_t : t -> s.
  Hypothesis inj : forall x : s, s_of_t (t_of_s x) = x.
  Hypothesis surj: forall x : t, t_of_s (s_of_t x) = x.
  Variable eq: forall (x y: s), {x = y} + {x <> y}.
End TYPE_EQ.

Module TYPE_EQ_PROP (X:TYPE_EQ).
  Lemma injective (a b: X.s) :
    a <> b -> X.t_of_s a <> X.t_of_s b.
  Proof. intros ? ?. pose proof (X.inj a). pose proof (X.inj b). congruence. Qed.
  Corollary injective' (a b: X.s) :
    X.t_of_s a = X.t_of_s b -> a = b.
  Proof. intros H. destruct (X.eq a b) as [u|u]; auto. elim (injective u H). Qed.
  Lemma tinjective (a b: X.t) :
    a <> b -> X.s_of_t a <> X.s_of_t b.
  Proof. intros ? ?. pose proof (X.surj a). pose proof (X.surj b). congruence. Qed.
  Lemma tinjective' (a b: X.t) :
    X.s_of_t a = X.s_of_t b -> a = b.
  Proof. intros ?. pose proof (X.surj a). pose proof (X.surj b). congruence. Qed.
End TYPE_EQ_PROP.

Module Z_EQ_POS : TYPE_EQ
    with Definition s := Z
    with Definition t := positive.
  Definition s := Z.
  Definition t := positive.
  Definition t_of_s (z: s) : t :=
    match z with
      | Z0 => xH
      | Zpos p => xO p
      | Zneg p => xI p
    end.
  Definition s_of_t (p: t) : s :=
    match p with
      | xH => Z0
      | xO x => Zpos x
      | xI x => Zneg x
    end.
  Lemma inj : forall x : s, s_of_t (t_of_s x) = x.
  Proof. now induction x. Qed.
  Lemma surj: forall x : t, t_of_s (s_of_t x) = x.
  Proof. now induction x. Qed.
  Definition eq: forall (x y: s), {x = y} + {x <> y} :=
    Z_eq_dec.
End Z_EQ_POS.

Lemma fold_left_map:
  forall {A B C} (f: A -> B) (g: C -> B -> C) xs a,
    fold_left g (map f xs) a = fold_left (fun a x => g a (f x)) xs a.
Proof. now induction xs; simpl. Qed.

Module BijTree (X:TYPE_EQ) (TTree: TREE with Definition elt := X.t) <: TREE.
  Module P := TYPE_EQ_PROP(X).
  Hint Resolve P.injective P.injective' P.tinjective P.tinjective'.
  Definition elt: Type := X.s.
  Definition elt_eq: forall (a b: elt), {a = b} + {a <> b} := X.eq.
  Definition t: Type -> Type := TTree.t.
  Definition empty: forall (A: Type), t A := TTree.empty.
  Definition get A i g : option A := TTree.get (X.t_of_s i) g.
  Definition set A i v g : t A := TTree.set (X.t_of_s i) v g.
  Definition remove A i g : t A := TTree.remove (X.t_of_s i) g.

  Lemma gempty: forall (A: Type) (i: elt), get i (empty A) = None.
  Proof. intros; apply TTree.gempty. Qed.
  Lemma gss: forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof. intros; apply TTree.gss. Qed.
  Lemma gso: forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof. intros; apply TTree.gso; auto. Qed.
  Lemma gsspec: forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof.
    intros. unfold get, set, elt_eq. rewrite TTree.gsspec.
    destruct X.eq. subst. bif. bif. elim n. auto.
  Qed.
  Lemma gsident: forall (A: Type) (i: elt) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof. intros. now apply TTree.gsident. Qed.
  Lemma grs: forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Proof. intros; apply TTree.grs. Qed.
  Lemma gro: forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof. intros; apply TTree.gro; auto. Qed.
  Lemma grspec: forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. unfold get, remove. rewrite TTree.grspec. bif. bif. elim n. auto. bif.
  Qed.

  Definition beq A cmp (t1 t2: t A) : bool :=
    TTree.beq cmp t1 t2.
  Lemma beq_correct:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
      beq eqA t1 t2 = true <->
      (forall (x: elt),
         match get x t1, get x t2 with
           | None, None => True
           | Some y1, Some y2 => eqA y1 y2 = true
           | _, _ => False
         end).
  Proof.
    intros. rewrite TTree.beq_correct.
    unfold get. split.
    - intros. apply H.
    - intros. specialize (H (X.s_of_t x)).
      rewrite X.surj in H. auto.
  Qed.

  (** Applying a function to all data of a tree. *)
  Definition map A B (f: elt -> A -> B) (g: t A) : t B :=
    TTree.map (fun e => (f (X.s_of_t e))) g.

  Lemma gmap: forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros. unfold get, map. rewrite TTree.gmap.
    now rewrite X.inj.
  Qed.

  (** Same as [map], but the function does not receive the [elt] argument. *)
  Definition map1 A B (f: A -> B) g := TTree.map1 f g.
  Lemma gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).
  Proof.
    unfold get, map1. intros. apply TTree.gmap1.
  Qed.

  (** Filtering data that match a given predicate. * )
  Variable filter1:
    forall (A: Type), (A -> bool) -> t A -> t A.
  Hypothesis gfilter1:
    forall (A: Type) (pred: A -> bool) (i: elt) (m: t A),
    get i (filter1 pred m) =
    match get i m with None => None | Some x => if pred x then Some x else None end.
      *)

  (** Applying a function pairwise to all data of two trees. *)
  Definition combine A B C (f:option A -> option B -> option C) g1 g2 : t C :=
    TTree.combine f g1 g2.
  Lemma gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof.
    intros. unfold get, combine. now apply TTree.gcombine.
  Qed.
  Lemma combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros. unfold combine. now apply TTree.combine_commut.
  Qed.

  (** Enumerating the bindings of a tree. *)
  Definition elements A g : list (elt * A) :=
    List.map (fun q => (X.s_of_t (fst q), snd q))
    (TTree.elements g).
  Lemma elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    unfold get, elements. intros A m i v H.
    pose proof (List.in_map (fun q => (X.s_of_t (fst q), snd q)) (TTree.elements m) _ (TTree.elements_correct H)).
    simpl in *. rewrite X.inj in *.
    auto.
  Qed.
  Lemma elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof.
    unfold elements, get. intros A m i v H.
    apply TTree.elements_complete.
    destruct (list_in_map_inv _ _ _ H) as ((x & y) & X & Y).
    simpl in *. injection X. clear X. intros. subst.
    now rewrite X.surj.
  Qed.
  Lemma elements_keys_norepet:
    forall (A: Type) (m: t A), 
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros A m.
    unfold elements.
    rewrite list_map_compose. simpl.
    rewrite <- list_map_compose.
    apply list_map_norepet.
    apply TTree.elements_keys_norepet.
    intros. now apply P.tinjective.
  Qed.

  (** Folding a function over all bindings of a tree. *)
  Definition fold A B f (g: t A) b : B :=
    TTree.fold (fun x k v => f x (X.s_of_t k) v) g b.
  Lemma fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros.
    unfold fold. rewrite TTree.fold_spec.
    unfold elements.
    generalize dependent v.
    generalize (TTree.elements m). clear m.
    induction l; auto.
    simpl. intuition.
  Qed.

  (** Folding a function over all rhs of bindings of a tree. *)
  Definition fold1 A B f (g: t A) b : B :=
    TTree.fold1 (fun x v => f x v) g b.
  Lemma fold1_spec:
    forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
  Proof.
    intros.
    unfold fold1. rewrite TTree.fold1_spec.
    unfold elements.
    generalize dependent v.
    generalize (TTree.elements m). clear m.
    induction l; auto.
    simpl. intuition.
  Qed.

End BijTree.

Module ZTree <: TREE with Definition elt := Z := BijTree(Z_EQ_POS)(PTree).

Module SumTree (L:TREE) (R:TREE) <: TREE.

  Definition elt := (L.elt + R.elt)%type.
  Definition elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Proof.
    decide equality. apply L.elt_eq. apply R.elt_eq.
  Defined.
  Definition t (A: Type) : Type := (L.t A * R.t A)%type.
  Definition empty A : t A := (L.empty A, R.empty A).
  Definition get A k m : option A :=
    match k with
      | inl x => L.get x (fst m)
      | inr x => R.get x (snd m)
    end.
  Definition set A k v m : t A :=
    match k with
      | inl x => (L.set x v (fst m), snd m)
      | inr x => (fst m, R.set x v (snd m))
    end.
  Definition remove A k m : t A :=
    match k with
      | inl x => (L.remove x (fst m), snd m)
      | inr x => (fst m, R.remove x (snd m))
    end.

  Lemma gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Proof.
    destruct i; simpl. apply L.gempty. apply R.gempty.
  Qed.
  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    destruct m. destruct i; simpl. apply L.gss. apply R.gss.
  Qed.
  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    destruct m. destruct i; destruct j; simpl; intros; auto. apply L.gso. congruence. apply R.gso. congruence.
  Qed.
  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof.
    destruct m. destruct i; destruct j; auto.
    bif; simpl; rewrite L.gsspec; bif.
    bif; simpl; rewrite R.gsspec; bif.
  Qed.
  Lemma gsident:
    forall (A: Type) (i: elt) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    destruct m; destruct i; simpl; intros. rewrite L.gsident; auto. rewrite R.gsident; auto.
  Qed.
   
  Lemma grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Proof.
    destruct m; destruct i; simpl. apply L.grs. apply R.grs.
  Qed.
  Lemma gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    destruct m; destruct i; destruct j; simpl; intros; auto.
    apply L.gro; congruence.
    apply R.gro; congruence.
  Qed.
  Lemma grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    destruct m; destruct i; destruct j; auto.
    bif; simpl; rewrite L.grspec; bif.
    bif; simpl; rewrite R.grspec; bif.
  Qed.

  (** Extensional equality between trees. *)
  Definition beq A (cmp: A -> A -> bool) (m1 m2: t A) : bool :=
    let '(l1, r1) := m1 in
    let '(l2, r2) := m2 in
    L.beq cmp l1 l2 && R.beq cmp r1 r2.
  Lemma beq_correct:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
      beq eqA t1 t2 = true <->
      (forall (x: elt),
         match get x t1, get x t2 with
           | None, None => True
           | Some y1, Some y2 => eqA y1 y2 = true
           | _, _ => False
         end).
  Proof.
    destruct t1; destruct t2; simpl.
    rewrite andb_true_iff, L.beq_correct, R.beq_correct.
    intuition.
    - destruct x. apply H0. apply H1.
    - apply (H (inl _)).
    - apply (H (inr _)).
  Qed.

  (** Applying a function to all data of a tree. *)
  Definition map A B (f: elt -> A -> B) (m: t A) : t B :=
    let '(l, r) := m in
    (L.map (fun k => f (inl _ k)) l,
     R.map (fun k => f (inr _ k)) r).
  Lemma gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    destruct m. destruct i; simpl. now rewrite L.gmap. now rewrite R.gmap.
  Qed.

  Definition map1 A B (f: A -> B) (m: t A) : t B :=
    (L.map1 f (fst m), R.map1 f (snd m)).
  Lemma gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).
  Proof.
    destruct m; destruct i; simpl. apply L.gmap1. apply R.gmap1.
  Qed.

  Definition combine A B C (f: option A -> option B -> option C) (m1: t A) (m2: t B) : t C :=
    let '(l1, r1) := m1 in
    let '(l2, r2) := m2 in
    (L.combine f l1 l2, R.combine f r1 r2).
  Lemma gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof.
    destruct m1; destruct m2; destruct i; simpl. apply L.gcombine; auto. apply R.gcombine; auto.
  Qed.
  Lemma combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    pose proof L.combine_commut.
    pose proof R.combine_commut.
    destruct m1; destruct m2. simpl. f_equal; auto.
  Qed.

  (** Enumerating the bindings of a tree. *)
  Definition elements A (m: t A) : list (elt * A) :=
    (List.map (fun k => (inl _ (fst k), snd k)) (L.elements (fst m)))
      ++
    (List.map (fun k => (inr _ (fst k), snd k)) (R.elements (snd m)))
  .
  Lemma elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros A m i v H.
    apply in_app.
    destruct m as (m & n); destruct i as [i|i];[left|right].
    pose proof (L.elements_correct).
    pose proof (List.in_map (fun k => (inl R.elt (fst k), snd k)) (L.elements m) (i,v)). auto.
    pose proof (R.elements_correct H).
    pose proof (List.in_map (fun k => (inr L.elt (fst k), snd k)) (R.elements n) (i,v)). auto.
  Qed.
  Lemma elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof.
    intros A m i v H. apply in_app in H.
    destruct m as [m n].
    destruct H as [H|H]; destruct (list_in_map_inv _ _ _ H) as ((x & y) & X & Y);
    injection X; intros; subst; clear X; simpl.
    apply L.elements_complete; auto.
    apply R.elements_complete; auto.
  Qed.
  Lemma elements_keys_norepet:
    forall (A: Type) (m: t A), 
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros A (m & n). unfold elements. rewrite List.map_app. apply list_norepet_app. split.
    rewrite list_map_compose. simpl. rewrite <- list_map_compose.
    apply list_map_norepet. apply L.elements_keys_norepet. congruence.
    split.
    rewrite list_map_compose. simpl. rewrite <- list_map_compose.
    apply list_map_norepet. apply R.elements_keys_norepet. congruence.
    repeat rewrite list_map_compose. simpl.
    generalize (L.elements m).
    generalize (R.elements n). clear m n.
    induction l as [|(a & b) l]. intros l x y H Z. elim Z.
    intros m x y X Y.
    destruct (list_in_map_inv _ _ _ X) as ((u & v) & U & V). subst. clear X. simpl.
    destruct (list_in_map_inv _ _ _ Y). intuition subst; discriminate.
  Qed.

  Definition fold A B (f: B -> elt -> A -> B) (m: t A) (v: B) : B :=
    (R.fold (fun b k => f b (inr _ k)) (snd m)
    (L.fold (fun b k => f b (inl _ k)) (fst m) v)).
  Lemma fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros. destruct m as (m & n).
    unfold fold, elements.
    rewrite List.fold_left_app, L.fold_spec, R.fold_spec. simpl.
    now repeat rewrite fold_left_map.
  Qed.

  Definition fold1 A B (f: B -> A -> B) (m: t A) (v: B) : B :=
    (R.fold1 (fun b => f b) (snd m)
    (L.fold1 (fun b => f b) (fst m) v)).
  Lemma fold1_spec:
    forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
  Proof.
    intros. destruct m as (m & n).
    unfold fold1, elements.
    rewrite List.fold_left_app, L.fold1_spec, R.fold1_spec. simpl.
    now repeat rewrite fold_left_map.
  Qed.

End SumTree.
