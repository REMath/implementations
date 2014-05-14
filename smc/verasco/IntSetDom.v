Require Import
  Coqlib Utf8
  TreeAl
  Integers
  LatticeSignatures
  IntervalDomain
  AdomLib
  AbMachineNonrel
  IntSet.

Definition fs_unop_sound (op: int → int) :
  ∀ x : fint_set, lift_unop op (γ x) ⊆ γ (fs_unop op x).
Proof.
  intros [|x]. now simpl.
  intros ? (i & I & ->).
  simpl. 
  rewrite <- (Int.repr_unsigned i). fold (proj i).
  apply (map_in (fun i => proj (op (Int.repr i))) x (proj i) I).
Qed.

Definition fs_binop_sound (op: int → int → int) :
  ∀ x y : fint_set, lift_binop op (γ x) (γ y) ⊆ γ (fs_binop op x y).
Proof.
  intros [|x] [|y]; try now simpl.
  intros ? (i & j & I & J & ->). simpl in *.
  rewrite <- (Int.repr_unsigned i). fold (proj i).
  rewrite <- (Int.repr_unsigned j). fold (proj j).
  apply (map2_in (fun i j => proj (op (Int.repr i) (Int.repr j))) x y _ _ I J).
Qed.

Lemma fs_is_in_itv_sound (l r: int) (x: fint_set) :
  fs_is_in_itv l r x = true →
  ∀ i: int, γ x i → Int.lt r i = false ∧ Int.lt i l = false.
Proof.
  destruct x as [|x']; simpl; intros K.
    apply False_ind. discriminate.
  intros i I.
  generalize (forallb_forall K I).
  rewrite andb_true_iff. repeat rewrite negb_true_iff. rewrite Int.repr_unsigned. easy.
Qed.

Notation todobw1 := (fun x _ => NotBot x).
Notation todobw2 := (fun x y _ => (NotBot x, NotBot y)).

Instance int_set_dom : ab_machine_int fint_set :=
{ as_int_adom := int_set_adom
; meet_int := fs_meet
; size := noitpo_lift fs_size
; concretize x := x
; range_int := fs_range
; const_int := fs_const
; booleans := fs_booleans
; forward_int_unop := fs_unop ∘ eval_int_unop
; forward_int_binop := fs_binop ∘ eval_int_binop
; is_in_itv := fs_is_in_itv
; backward_int_unop op := todobw1
; backward_int_binop op := todobw2
}.
 
Instance int_set_dom_correct : ab_machine_int_correct int_set_dom.
Proof.
  constructor; apply fs_unop_sound || apply fs_binop_sound || (now simpl) || intuition.
+ (* meet *)
  apply fs_meet_sound. auto.
+ (* const *)
  intros; simpl; apply ZTree.gss.
  (* booleans *)
+ simpl. apply union_in_l. unfold singleton. apply ZTree.gss.
+ simpl. apply union_in_r. unfold singleton. apply ZTree.gss.
+ (* range *)
  destruct x. split; simpl. apply Interval.gamma_top. apply Interval.ugamma_top.
  simpl in *. split.
  unfold int_set_signed_range.
  generalize (min_max_spec (Int.signed ∘ Int.repr) i).
  destruct min_max as [(l,r)|].
    intros (L & R & LR).
    2: intros E; elim (is_empty_correct _ E _ H).
    destruct (LR _ H). rewrite Int.repr_unsigned in *.
    split; simpl; auto.
  unfold int_set_unsigned_range.
  generalize (min_max_spec (fun i => i) i).
  destruct min_max as [(l,r)|].
    intros (L & R & LR).
    2: intros E; elim (is_empty_correct _ E _ H).
    exact (LR _ H).
+ (* unop *) apply fs_unop_sound, H.
+ (* binop *) apply fs_binop_sound, H.
+ eapply fs_is_in_itv_sound in H; [destruct H|]; eauto.
+ eapply fs_is_in_itv_sound in H; [destruct H|]; eauto.
+ simpl; intuition.
Qed.
