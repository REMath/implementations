Require Import
  Coqlib Integers
  Utf8 DLib
  LatticeSignatures
  AdomLib
  AbMachineNonrel
  IntervalDomain.

(** Instance: (signed) interval domain. *)
Definition botlift_backop {A} op (x y: A+⊥) :=
  match x, y with
    | NotBot x', NotBot y' => op x' y'
    | _, _ => (@Bot A, @Bot A)
  end.

Definition bb {A B C} (f: A → B → C) (a: A) (b: B) : C+⊥ := NotBot (f a b).

Definition itv_unop (op: int_unary_operation) : Interval.itv → Interval.itv :=
  match op with
  | OpNeg => Interval.neg
  | OpNot => Interval.not
  end.

Definition itv_binop (op: int_binary_operation) : Interval.itv → Interval.itv → Interval.itv :=
  match op with
  | OpAdd => Interval.add
  | OpSub => Interval.sub
  | OpMul => Interval.mult
  | OpDivs => Interval.div
  | OpShl => Interval.shl
  | OpShr => Interval.shr
  | OpShru => Interval.shru
  | OpOr => Interval.or
  | OpAnd => Interval.and
  | OpXor => Interval.xor
  | OpCmp c => fun _ _ => Interval.booleans
  | OpCmpu c => fun _ _ => Interval.booleans
  end.

Function itv_concretize_aux (from: Z) (nb: N)
         (acc: IntSet.int_set) {measure N.to_nat nb} : IntSet.int_set :=
  match nb with
  | N0 => acc
  | Npos p =>
    let nb' := Pos.pred_N p in
    itv_concretize_aux from nb'
    (IntSet.union (IntSet.singleton (Int.repr (from + Zpos p))) acc)
  end.
Proof.
  intros from nb acc p ->. rewrite N.pos_pred_spec, Nnat.N2Nat.inj_pred. zify. intuition.
Defined.

Definition itv_concretize (i: Interval.itv) : IntSet.fint_set :=
  let (m, M) := i in
  match z2n (M - m) with
  | inleft n => Just (itv_concretize_aux m (proj1_sig n) (IntSet.singleton (Int.repr m)))
  | inright GT => Just (IntSet.empty)
  end.

Instance itv_dom : ab_machine_int Interval.itv
  := Build_ab_machine_int
    Interval.signed_itv_adom
    (fun x => Just (N_of_Z (x.(Interval.max) - x.(Interval.min))))
    itv_concretize
    Interval.meet
    Interval.signed
    Interval.booleans
    (fun i s => NotBot (match s with Signed => i | Unsigned => Interval.reduc2unsigned i end))
    (fun op => @NotBot _ ∘ itv_unop op)
    (fun op x => @NotBot _ ∘ itv_binop op x)
    (fun m M x => Interval.is_in_interval (Int.signed m) (Int.signed M) x)
    (fun op =>
       match op with
         | OpNeg => Interval.backward_neg
         | OpNot => Interval.backward_not
       end)
    (fun op =>
       match op with
         | OpAdd => Interval.backward_add
         | OpSub => Interval.backward_sub
         | OpCmp c => Interval.backward_cmp c
         | OpCmpu c => Interval.backward_cmpu c
         | OpAnd | OpOr (* FIXME *)
         | OpShr | OpShru
         | OpXor | OpMul | OpDivs | OpShl => fun x y _ => (NotBot x, NotBot y)
       end).

Section CONCR.
  Import IntSet.
  Local Open Scope int_set_scope.

  Lemma itv_concretize_aux_correct z :
    let round x := proj (Int.repr x) in
    ∀ nb acc,
      round z ∈ acc →
      ∀ q, round q ∈ acc ∨ z < q <= z + Z.of_N nb →
           round q ∈ itv_concretize_aux z nb acc.
  Proof.
    intros round.
    intros nb acc Z.
    apply (itv_concretize_aux_rec z).
  - intros nb0 acc0 _ q [H|[H K]]. assumption. Psatz.lia.
  - intros [|p'] acc' p. inversion 1. inversion_clear 1. simpl.
    rewrite N.pos_pred_spec, N2Z.inj_pred. 2: easy. simpl Z.of_N.
    intros IH q [H|[H K]].
    + apply IH. now left; apply IntSet.union_in_r.
    + apply IH. clear IH.
      destruct (Z_le_dec q (z + (Z.pos p + -1))) as [LE|GT]. right; intuition.
      left. apply IntSet.union_in_l.
      unfold IntSet.singleton.
      assert (q = z + Z.pos p). Psatz.lia.
      subst. apply TreeAl.ZTree.gss.
  Qed.

  Corollary itv_concretize_correct (x: Interval.itv) :
    γ x ⊆ γ (itv_concretize x).
  Proof.
    intros i.
    destruct x as (m, M). simpl.
    destruct z2n as [(n & LE)|GT].
  - intros [A B]. unfold γ. simpl in *.
    rewrite <- (Int.repr_signed i).
    apply (itv_concretize_aux_correct).
    now unfold singleton; rewrite TreeAl.ZTree.gss.
    assert (m < Int.signed i ∨ m = Int.signed i) as Q by Psatz.lia.
    destruct Q as [A' | ->]. right. Psatz.lia.
    now left; unfold singleton; rewrite TreeAl.ZTree.gss.
  - intros [A B]. simpl in *. Psatz.lia.
  (* - unfold γ. simpl. unfold empty. rewrite TreeAl.ZTree.gempty. discriminate. *)
  Qed.

End CONCR.

Instance itv_dom_correct : ab_machine_int_correct itv_dom.
Proof.
  split.
  - intros; apply Interval.meet_correct; intuition.
  - exact itv_concretize_correct.
  - intros i; simpl. apply Interval.signed_correct.
  - apply Interval.bool_correct_zero.
  - apply Interval.bool_correct_one.
  - intros; split; simpl; auto. apply Interval.reduc2unsigned_correct; auto.
  - intros (); simpl.
    simpl. intros x a (j & K & L); subst. apply Interval.neg_correct. auto.
    simpl. intros x a (j & K & L); subst. apply Interval.not_correct. auto.
  - intros (); simpl; try easy.
    intros x y a (j & k & J & K & ->). simpl. apply Interval.add_correct; auto.
    intros x y a (j & k & J & K & ->). simpl. apply Interval.sub_correct; auto.
    intros x y a (j & k & J & K & ->). simpl. apply Interval.mul_correct; auto.
    intros x y a (j & k & J & K & ->). simpl. apply Interval.divs_correct; auto.
    intros x y a (j & k & J & K & ->). simpl. apply Interval.shl_correct; auto.
    intros x y a (j & k & J & K & ->). simpl. apply Interval.shr_correct; auto.
    intros x y a (j & k & J & K & ->). simpl. apply Interval.shru_correct; auto.
    intros x y a (j & k & J & K & ->). simpl. apply Interval.and_correct; auto.
    intros x y a (j & k & J & K & ->). simpl. apply Interval.or_correct; auto.
    intros x y a (j & k & J & K & ->). simpl. apply Interval.xor_correct; auto.
    intros c x y a (j & k & J & K & ->). simpl. destruct Int.cmp.
      apply Interval.bool_correct_one. apply Interval.bool_correct_zero.
    intros c x y a (j & k & J & K & ->). simpl. destruct Int.cmpu.
      apply Interval.bool_correct_one. apply Interval.bool_correct_zero.
  - intros m M x.
    intros K i H. pose proof (Interval.is_in_interval_correct _ _ _ K i H). unfold Int.lt. split; bif; auto; intuition.
  - intros (); simpl.
    intro; apply Interval.backward_neg_correct.
    intro; apply Interval.backward_not_correct.
  - intros (); try now simpl; intuition.
    intro; apply Interval.backward_add_correct.
    intro; apply Interval.backward_sub_correct.
    repeat intro. simpl. apply Interval.backward_cmp_correct; auto.
    repeat intro. simpl. apply Interval.backward_cmpu_correct; auto.
Qed.

(** Instance: (unsigned) interval domain. *)
Module UInterval.

  Import Interval.
  Instance ugamma_op : gamma_op itv int := ugamma.

  Definition const (i: int) : itv :=
    ITV (Int.unsigned i) (Int.unsigned i).

  Definition neg (x: itv) : itv :=
    if zeq 0 (max x)
    then x
    else if zle (min x) 0
         then utop
         else ITV (Int.modulus - max x) (Int.modulus - min x).

  Definition repr (x: itv) : itv :=
    if x ⊑ utop then x else utop.

  Definition add (x y: itv) : itv :=
    let m := min x + min y in
    let M := max x + max y in
    if zle m Int.max_unsigned
    then if zle M Int.max_unsigned
         then ITV m M
         else utop
    else ITV (m - Int.modulus) (M - Int.modulus).

  Definition not (x: itv) : itv :=
    add (neg x) (ITV Int.max_unsigned Int.max_unsigned).

  Definition sub (x y: itv) : itv :=
    repr (ITV (min x - max y) (max x - min y)).

  Definition mult (x y:itv) : itv :=
    let b1 := x.(min) * y.(min) in
    let b2 := x.(min) * y.(max) in
    let b3 := x.(max) * y.(min) in
    let b4 := x.(max) * y.(max) in
      repr (ITV 
               (Zmin (Zmin b1 b4) (Zmin b3 b2))
               (Zmax (Zmax b1 b4) (Zmax b3 b2))).

  (* TODO *)
  Definition todo (x y: itv) : itv := utop.

  Definition back_id1 (x y: itv) : itv+⊥ := NotBot x.
  Definition back_id2 (x y z: itv) : itv+⊥ * itv+⊥ := (NotBot x, NotBot y).

  Definition backward_ltu (i1 i2:itv) : itv+⊥ * itv+⊥ :=
    (botbind (meet i1) (reduce 0 ((max i2)-1)),
     botbind (meet i2) (reduce ((min i1)+1) Int.max_unsigned)).

  Definition backward_ne (x y:itv) : itv+⊥ * itv+⊥ :=
    let '(x', y') := backward_ltu x y in
    let '(y'', x'') := backward_ltu y x in
      (x' ⊔ x'', y' ⊔ y'').

  Definition backward_leu (i1 i2:itv) : itv+⊥ * itv+⊥ :=
    (botbind (meet i1) (reduce 0 (max i2)),
     botbind (meet i2) (reduce (min i1) Int.max_unsigned)).

  Definition backward_cmpu (c:comparison) (ab1 ab2 res:itv) : itv+⊥ * itv+⊥ :=
    match is_singleton res with
      | None => (NotBot ab1,NotBot ab2)
      | Some i =>
        if Int.eq i Int.one then
          match c with
            | Ceq => let ab := ab1 ⊓ ab2 in (ab,ab)
            | Cne => backward_ne ab1 ab2
            | Clt => backward_ltu ab1 ab2
            | Cle => backward_leu ab1 ab2
            | Cgt => swap (backward_ltu ab2 ab1)
            | Cge => swap (backward_leu ab2 ab1)
          end
        else if Int.eq i Int.zero then
               match c with
                 | Ceq => backward_ne ab1 ab2
                 | Cne => let ab := ab1 ⊓ ab2 in (ab,ab)
                 | Cge => backward_ltu ab1 ab2
                 | Cgt => backward_leu ab1 ab2
                 | Cle => swap (backward_ltu ab2 ab1)
                 | Clt => swap (backward_leu ab2 ab1)
               end
             else (NotBot ab1,NotBot ab2)
    end.

Definition itvu_unop (op: int_unary_operation) : itv → itv :=
  match op with
  | OpNeg => neg
  | OpNot => not
  end.

Definition itvu_binop (op: int_binary_operation) : Interval.itv → Interval.itv → Interval.itv :=
  match op with
  | OpAdd => add
  | OpSub => sub
  | OpMul => mult
  | OpDivs => todo
  | OpShl => todo
  | _ => todo
  end.

 Instance itvu_num : ab_machine_int itv := Build_ab_machine_int
   unsigned_itv_adom
   (fun x => Just (N_of_Z (x.(max) - x.(min))))
   (fun _ => All) (* FIXME *)
   meet
   const
   booleans
   (fun i s => NotBot (match s with Signed => reduc2signed i | Unsigned => i end))
   (fun op => @NotBot _ ∘ itvu_unop op)
   (fun op x => @NotBot _ ∘ itvu_binop op x)
   (fun _ _ _ => false)
   (fun _ => back_id1)
   (fun op =>
      match op with
      | OpCmpu c => backward_cmpu c
      | _ => back_id2
      end).

 Lemma neg_correct: ∀ x i,
   ugamma x i →
   ugamma (neg x) (Int.neg i).
 Proof.
   pose proof Int.modulus_pos as P.
   intros (a&B) u H.
   unfold ugamma, min, max in H.
   unfold neg, Int.neg.
   bif.
     unfold ugamma, min, max in *; subst.
     pose proof (Int.unsigned_range u).
     assert (Int.unsigned u = 0) as K2 by intuition.
     rewrite K2 in *. intuition.
   bif.
     apply (ugamma_top (Int.repr (- Int.unsigned u))).
   unfold ugamma, min, max in *.
   rewrite Int.unsigned_repr_eq.
   rewrite Z_mod_nz_opp_full.
   rewrite Z.mod_small. omega.
   apply Int.unsigned_range.
   rewrite Z.mod_small. omega.
   apply Int.unsigned_range.
 Qed.

 Lemma reduce_correct (m M: Z) (i:int) :
   m <= Int.unsigned i <= M →
   lift_gamma Interval.ugamma (reduce m M) i.
 Proof.
   unfold reduce. destruct zle. 2: intuition. auto.
 Qed.

   Lemma add_correct x y i j:
     ugamma x i →
     ugamma y j →
     ugamma (add x y) (Int.add i j).
   Proof.
     unfold ugamma, add.
     pose proof (Int.unsigned_range i).
     pose proof (Int.unsigned_range j).
     repeat bif; simpl min; simpl max.
     > intros. rewrite Int.add_unsigned, Int.unsigned_repr; omega.
     > intros. apply Int.unsigned_range_2.
     > intros. rewrite Int.add_unsigned.
       replace (Int.repr (Int.unsigned i + Int.unsigned j)) with 
               (Int.repr (Int.unsigned i + Int.unsigned j + -1 * Int.modulus)).
       rewrite Int.unsigned_repr. omega. unfold Int.max_unsigned in *. omega.
       apply repr_mod_prop.
   Qed.

   Lemma backward_ltu_correct x y i j :
     ugamma x i →
     ugamma y j →
     Int.unsigned i < Int.unsigned j →
     let '(u,v) := backward_ltu x y in
     lift_gamma ugamma u i ∧ lift_gamma ugamma v j.
   Proof.
     intros I J K.
     unfold backward_ltu.
     split; (eapply botbind_spec; [intros; apply meet_correctu; eauto|]);
                          apply reduce_correct; intuition.
     apply Int.unsigned_range. apply Zle_trans with (Int.unsigned j - 1). intuition. destruct J. intuition.
     apply Zle_trans with (Int.unsigned i + 1). destruct I. intuition. intuition.
     unfold Int.max_unsigned. generalize (Int.unsigned_range j). intuition.
   Qed.

   Lemma backward_ne_correct x y i j :
     ugamma x i →
     ugamma y j →
     Int.unsigned i ≠ Int.unsigned j →
     let '(u,v) := backward_ne x y in
     lift_gamma ugamma u i ∧ lift_gamma ugamma v j.
   Proof.
     Hint Resolve (lift_bot itvu_adom).
     intros I J K. repeat red.
     destruct (Ztrichotomy (Int.unsigned i) (Int.unsigned j)) as [H|[H|H]]. 2: contradiction.
     split; apply join_sound; auto; left; eapply backward_ltu_correct; eauto.
     split; apply join_sound; auto; right; eapply backward_ltu_correct; eauto; intuition.
   Qed.

   Lemma backward_leu_correct x y i j :
     ugamma x i →
     ugamma y j →
     Int.unsigned i <= Int.unsigned j →
     let '(u,v) := backward_leu x y in
     lift_gamma ugamma u i ∧ lift_gamma ugamma v j.
   Proof.
     intros I J K.
     split; (eapply botbind_spec; [intros; apply meet_correctu; eauto|]); apply reduce_correct; intuition.
     apply Int.unsigned_range. apply Zle_trans with (Int.unsigned j). intuition. destruct J. intuition.
     apply Zle_trans with (Int.unsigned i). destruct I. intuition. intuition.
     unfold Int.max_unsigned. generalize (Int.unsigned_range j). intuition.
   Qed.

 Instance itvu_num_correct : ab_machine_int_correct itvu_num.
 Proof.
   split.
   - (* meet *) apply meet_correctu.
   - (* concretize *) easy.
   - (* const *) intros i. split; simpl; apply Zle_refl.
   - (* booleans *)
     simpl. split; simpl; intuition.
   - simpl. split; simpl; intuition.
   - (* range *)
     split; simpl. apply reduc2signed_correct; auto. auto.
   - intros ().
     (* neg *)
     simpl. intros a j (i & H & ->). now apply neg_correct.
     (* not *)
     simpl. intros a j (i & H & ->).
     rewrite Int.not_neg. unfold not. apply add_correct. apply neg_correct. auto.
     vm_compute. split; discriminate.
   - intros (); try now intros; apply ugamma_top.
     (* add *)
     intros x y i (u & v & A); simpl in *. intuition. subst. now apply add_correct.
     (* sub *)
     intros x y i (u & v & A & B & ->).
     destruct A as [A A']. destruct B as [B B'].
     simpl; unfold sub, repr, Int.sub. simpl.
     destruct zle. destruct zle.
     unfold γ, ugamma. simpl. unfold γ. simpl min; simpl max.
     rewrite Int.unsigned_repr; omega.
     apply ugamma_top.
     apply ugamma_top.
     (* mul *)
     simpl; unfold γ, ugamma.
     intros [a b] [c d] ? (i & j & A & B & ->); simpl in *.
     unfold mult, repr; simpl.
     destruct zle as [C|]. 2: apply ugamma_top.
     destruct zle as [D|]. 2: apply ugamma_top.
     unfold Int.mul.
     assert (HZ:=Mult_interval_correct_min_max _ _ _ _ _ _ A B).
     split; simpl; rewrite Int.unsigned_repr; Psatz.nia.
  - (* is_in_itv *)
    simpl. intuition.
  - (* back id *)
    intros ? ? ? ? H _; exact H.
  - intros (); try (intros ? ? ? ? ? H K _; exact (conj H K)).
    intros ? ? ? ? ? ? H K _; exact (conj H K).
    (* back cmp *)
    Opaque meet.
    simpl. unfold backward_cmpu.
    intros c x y (rl,rr) i j I J R. unfold is_singleton. simpl in I,J,R.
    destruct zeq. 2: simpl; intuition.
    subst.
    generalize (Int.eq_spec (of_bool (Int.cmpu c i j)) Int.one).
    destruct Int.eq; intros C.
    (* true *)
    autorw'.
    assert (rr = 1) by (destruct rr as [|p|p]; vm_compute in R; try destruct p; intuition). subst.
    clear R. repeat red.
    destruct c; simpl in C.
    (* eq *)
    generalize (Int.eq_spec i j). destruct Int.eq. intros ->.
    split; simpl; apply meet_correctu; intuition.
    discriminate.
    (* ne *)
    generalize (Int.eq_spec i j). destruct Int.eq. intros ->. discriminate. intros.
    apply backward_ne_correct; auto. apply unsigned_inj; auto.
    (* ltu *)
    unfold Int.ltu in C. destruct zlt. 2: discriminate.
    eapply backward_ltu_correct; auto.
    unfold Int.ltu in C. destruct zlt. discriminate.
    eapply backward_leu_correct; auto. intuition.
    unfold Int.ltu in C. destruct zlt. 2: discriminate.
    repeat red; apply and_comm. split; eapply backward_ltu_correct; eauto.
    unfold Int.ltu in C. destruct zlt. discriminate.
    repeat red; apply and_comm. eapply backward_leu_correct; auto. intuition.
    (* false *)
    assert (rr = 0). unfold of_bool in R. destruct Int.cmpu. elim C; reflexivity.
    destruct rr; vm_compute in R; intuition.
    subst. clear R. repeat red.
    destruct c; simpl in C.
    generalize (Int.eq_spec i j). destruct Int.eq. intros ->. elim C; reflexivity.
    intros. apply backward_ne_correct; auto. apply unsigned_inj; auto.
    generalize (Int.eq_spec i j). destruct Int.eq. intros ->.
    simpl; split; apply meet_correctu; intuition.
    elim C. reflexivity.
    unfold Int.ltu in C. destruct zlt. elim C; reflexivity.
    repeat red. apply and_comm. apply backward_leu_correct; intuition.
    unfold Int.ltu in C. destruct zlt. 2: elim C; reflexivity.
    repeat red. apply and_comm. apply backward_ltu_correct; intuition.
    unfold Int.ltu in C. destruct zlt. elim C; reflexivity.
    apply backward_leu_correct; intuition.
    unfold Int.ltu in C. destruct zlt. 2: elim C; reflexivity.
    apply backward_ltu_correct; intuition.
Qed.

End UInterval.

(** Instance: reduction for signed/unsigned intervals. *)
Import Interval.
Instance itv_red : reduction itv itv :=
{| ρ := botbind2 (fun s u =>
     let s' := reduc2signed u in
     let u' := reduc2unsigned s in
     match s ⊓ s', u ⊓ u' with
       | Bot, _ | _, Bot => Bot
       | NotBot a, NotBot b => NotBot (a,b)
     end)
|}.

Lemma itv_red_correct : reduction_correct signed_itv_adom unsigned_itv_adom.
Proof.
  Hint Resolve reduc2unsigned_correct reduc2signed_correct.
  intros [|a] [|b]; try now simpl.
  unfold γ. simpl. unfold γ.
  intros i (A & B).
  unfold ρ, itv_red, botbind2, botbind.
  pose proof (meet_correct a (reduc2signed b)) as X.
  pose proof (@meet_correctu b (reduc2unsigned a)) as Y.
  case_eq (a ⊓ reduc2signed b);[|intros ab];
  intros Ha; rewrite Ha in X. eapply X; eauto. now apply reduc2signed_correct.
  case_eq (b ⊓ reduc2unsigned a);[|intros ba];
  intros Hb; rewrite Hb in Y. eapply Y; eauto.
  intuition. apply X; auto.
  now apply reduc2signed_correct.
Qed.

(*
Instance unit_red : reduction unit unit :=
{| ρ := botbind2 (fun _ _ => NotBot (tt, tt)) |}.

Instance unit_red_correct : reduction_correct unit_adom (@unit_adom Floats.float).
intros [|a] [|b]; try now simpl.
Qed.
*)

Instance intervals : ab_machine_int _  := 
  @reduced_product_int _ _ itv_dom UInterval.itvu_num itv_red.
Instance intervals_correct : ab_machine_int_correct intervals :=
  reduced_product_int_correct itv_dom_correct UInterval.itvu_num_correct itv_red_correct.
