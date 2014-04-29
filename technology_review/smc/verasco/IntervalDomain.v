(** Abstract domain of intervals of machine integers. *)

Require Import Coqlib Utf8 ToString.
Require Import Psatz.
Require Import Integers.
Require Import LatticeSignatures AdomLib.
Require Import DLib.
Require Import PrintPos.
Require Recdef.
Import String.

Section SIGNEDNESS.
Local Unset Elimination Schemes.
Inductive signedness : Type :=
  | Signed: signedness
  | Unsigned: signedness.
End SIGNEDNESS.

Module Interval.

  Record itv : Type := ITV { min: Z; max: Z }.
  Definition t := itv.

  Instance toString : ToString t :=
    { to_string i := ("[" ++ string_of_z i.(min) ++ "; " ++ string_of_z i.(max) ++ "]")%string }.

  Definition order (i1 i2: itv) : bool :=
    match i1, i2 with
      | (ITV min1 max1), (ITV min2 max2) =>
        zle min2 min1 && zle max1 max2
    end.

  Definition join (i1 i2: itv) : itv :=
    match i1, i2 with
      | (ITV min1 max1), (ITV min2 max2) =>
        (ITV (Zmin min1 min2) (Zmax max1 max2))
    end.

  Definition widen_classic (i1 i2: itv) : itv :=
    match i1, i2 with
      | (ITV min1 max1), (ITV min2 max2) =>
        ITV 
        (if zle min1 min2 then min1 else Int.min_signed)
	(if zle max2 max1 then max1 else Int.max_signed)
    end.

  Fixpoint next_pow2_pos (p:positive) :=
    match p with
    | xH => xH
    | xI p
    | xO p => xI (next_pow2_pos p)
    end.

  Definition previous_pow2_pos p := 
    let p' := next_pow2_pos p in
     match p' with
       | xI p => p
       |  _ => p' (* assert false *)
     end.

  Definition next_threshold (z:Z) := 
    match z with
      | Z0 => Z0
      | Zpos xH => Zpos xH
      | Zneg xH => Zneg xH
      | Zpos p => Zpos (next_pow2_pos p)
      | Zneg p => Zneg (previous_pow2_pos p)
    end.

  Definition previous_threshold (z:Z) :=
    match z with
      | Z0 => Z0
      | Zpos xH => Zpos xH
      | Zneg xH => Zneg xH
      | Zpos p => Zpos (previous_pow2_pos p)
      | Zneg p => Zneg (next_pow2_pos p)
    end.

  Definition widen (i1 i2: itv) : itv :=
    match i1, i2 with
      | (ITV min1 max1), (ITV min2 max2) =>
        ITV 
        (if zle min1 min2 then min1
          else previous_threshold min2)
	(if zle max2 max1 then max1
          else next_threshold max2)
    end.

  Parameter next_smaller : Z -> Z.
  Parameter next_larger : Z -> Z.
  
  Definition widen_heuristic (i1 i2: itv) : itv :=
    match i1, i2 with
      | (ITV min1 max1), (ITV min2 max2) =>
        ITV 
        (if zle min1 min2 then min1
          else next_smaller min2)
	(if zle max2 max1 then max1
          else next_larger max2)
    end.

(*
  let itv x =
    let min = Camlcoq.camlint64_of_z x.min in
    let max = Camlcoq.camlint64_of_z x.max in
      Printf.sprintf "[%Ld; %Ld]" min max

  let widen i1 i2 =
    let res = widen i1 i2 in
      Printf.printf "WIDENING(%s, %s) --> %s\n"
	(itv i1) (itv i2) (itv res);
      res
*)

  Definition top : itv := (ITV Int.min_signed Int.max_signed).
  Definition utop : itv := (ITV 0 Int.max_unsigned).

  Instance gamma : gamma_op itv int := fun i v =>
    min i <= Int.signed v <= max i.

  Lemma gamma_top : forall v,
    gamma top v.
  Proof.
    unfold gamma.
    apply Int.signed_range.
  Qed.

  Lemma gamma_monotone : forall ab1 ab2,
    order ab1 ab2 = true -> forall v, gamma ab1 v -> gamma ab2 v.
  Proof.
    destruct ab1 as [min1 max1].
    destruct ab2 as [min2 max2]; simpl in *.
    unfold gamma; simpl in *; auto.
    rewrite andb_true_iff in *; repeat rewrite zle_true_iff in *; intros; omega.
  Qed.

  Lemma join_correct : forall (i1 i2:itv) i,
    gamma i1 i \/ gamma i2 i ->
    gamma (join i1 i2) i.
  Proof.
    unfold join.
    unfold gamma.
    destruct i1; simpl.
    destruct i2; simpl.
    simpl; intros.
    lia.
  Qed.

  Instance signed_itv_wl : weak_lattice itv :=
  { leb := order;
    top := top;
    join := join;
    widen := widen_heuristic
  }.
  Lemma signed_itv_adom : adom itv int _ gamma.
  Proof.
    split.
    exact gamma_monotone.
    exact gamma_top.
    exact join_correct.
  Qed.

  Definition itvbot := itv+⊥.

  Definition reduce (min max : Z) : itvbot :=
    if zle min max then NotBot (ITV min max) else Bot.

  Definition meet (i1: itv) (i2:itv) : itvbot :=
    match i1, i2 with
      | (ITV min1 max1), (ITV min2 max2) =>
        reduce (Zmax min1 min2) (Zmin max1 max2)
    end.
  Notation "x ⊓ y" := (meet x y) (at level 40).

  Definition repr (i:itv) : itv :=
    if leb i top then i else top.

  Definition signed (n:int) : itv := 
    let z := Int.signed n in 
      (ITV z z).

  Definition neg (i:itv) : itv := 
    match i with
      | (ITV min max) => 
        repr (ITV (-max) (-min))
    end.

  Definition mult (i1 i2:itv) : itv :=
    let min1 := min i1 in
    let min2 := min i2 in
    let max1 := max i1 in
    let max2 := max i2 in
    let b1 := min1 * min2 in
    let b2 := min1 * max2 in
    let b3 := max1 * min2 in
    let b4 := max1 * max2 in
      repr (ITV 
               (Zmin (Zmin b1 b4) (Zmin b3 b2))
               (Zmax (Zmax b1 b4) (Zmax b3 b2))).

  Definition add (i1 i2:itv) : itv :=
    repr (ITV ((min i1)+(min i2)) ((max i1)+(max i2))).

  Definition sub (i1 i2:itv) : itv :=
    repr (ITV ((min i1)-(max i2)) ((max i1)-(min i2))).

  Definition not (i:itv) : itv :=
    add (neg i) (signed Int.mone).

  Definition contains (x:int) (i:itv) : bool :=
    let (min,max) := i in 
      let x := Int.signed x in
      zle min x && zle x max.

  Definition is_singleton (v:itv) : option int :=
    let (min,max) := v in
      if zeq min max then Some (Int.repr min) else None.

  Definition is_bool (v:itv) : option bool :=
    let (min,max) := v in
      if zeq min max then
        let x := Int.repr min in
          if Int.eq x Int.zero then Some false
          else if Int.eq x Int.one then Some true
            else None
        else None.

  Definition booleans :=
    join (signed Int.zero) (signed Int.one).

  Definition div (v1 v2:itv) : itv :=
    match is_singleton v2 with
      | Some i2 => 
        let (a,b) := v1 in
        let i2 := Int.signed i2 in
        if zlt 0 i2 then ITV (Z.quot a i2) (Z.quot b i2) else top
      | None => top
    end.

  Definition shl (v1 v2:itv) : itv :=
    match is_singleton v2 with
      | Some i2 => mult v1 (signed (Int.shl Int.one i2))
      | None => top
    end.

  Definition backward_eq (i1 i2:itv) : itvbot * itvbot :=
    (meet i1 i2, meet i1 i2).

  Definition backward_lt (i1 i2:itv) : itvbot * itvbot :=
        (botbind (meet i1) (reduce Int.min_signed ((max i2)-1)),
          botbind (meet i2) (reduce ((min i1)+1) Int.max_signed))
    .

  Definition backward_ne (i1 i2:itv) : itvbot * itvbot :=
    let (i1',i2') := backward_lt i1 i2 in
      let (i2'',i1'') := backward_lt i2 i1 in
        (i1' ⊔ i1'',i2' ⊔ i2'').

  Definition backward_le (i1 i2:itv) : itvbot * itvbot :=
    (botbind (meet i1) (reduce Int.min_signed (max i2)),
      botbind (meet i2) (reduce (min i1) Int.max_signed))
    .

  Definition is_in_interval (a b : Z) (ab:itv) : bool :=
    ab ⊑ (ITV a b).

  Definition cast_int16u : Interval.t-> bool := is_in_interval 0 65535.

  Definition backward_leu (i1 i2:itv) : itvbot * itvbot :=
    if cast_int16u i1 && cast_int16u i2
      then backward_le i1 i2
      else (NotBot i1, NotBot i2).

  Definition backward_ltu (i1 i2:itv) : itvbot * itvbot := 
    if cast_int16u i1 && cast_int16u i2
      then backward_lt i1 i2
      else (NotBot i1, NotBot i2).

  Lemma meet_correct: forall (ab1:itv) (ab2:itv) v,
    γ ab1 v -> γ ab2 v -> γ (meet ab1 ab2) v.
  Proof.
    unfold meet.
    destruct ab1; simpl.
    destruct ab2; simpl.
    assert (TT:Int.min_signed <= Int.max_signed) by discriminate.
    unfold γ, gamma. simpl.
    apply Zmax_case_strong; apply Zmin_case_strong;  unfold reduce; simpl; repeat (destruct zle; simpl);
      intros; auto; try lia;
    split; intuition.
  Qed.

  Definition meet' (ab1 ab2:itvbot) : itvbot :=
    botbind2 meet ab1 ab2.

  Lemma meet'_correct: forall (ab1 ab2:itvbot) v,
    γ ab1 v -> γ ab2 v -> γ (meet' ab1 ab2) v.
  Proof.
    intros. eapply botbind2_spec; eauto.
    intros. apply meet_correct; auto.
  Qed.

  Lemma neg_correct : forall ab i,
    γ ab i ->
    γ (neg ab) (Int.neg i).
  Proof.
    destruct ab; simpl; auto; intros.
    unfold gamma; simpl.
    destruct i; simpl in *.
    unfold repr; simpl.
    case_eq (zle Int.min_signed (- max0) && zle (- min0) Int.max_signed); auto.
    repeat rewrite andb_true_iff; repeat rewrite zle_true_iff; intros [T1 T2].
    simpl.
    unfold Int.neg; rewrite <- neg_signed_unsigned.
    unfold γ, gamma in *; simpl in *.
    rewrite Int.signed_repr; lia.
    intros;     apply Int.signed_range.
  Qed.

  Lemma signed_correct: forall i, γ (signed i) i.
  Proof.
    unfold signed; simpl; intros; unfold γ, gamma; simpl; lia.
  Qed.

  Lemma bool_correct_zero : γ booleans Int.zero.
  Proof.
    unfold booleans.
    apply (join_correct (signed Int.zero) (signed Int.one)); simpl.
    left; unfold gamma, signed; simpl.
    split; reflexivity.
  Qed.

  Lemma bool_correct_one : γ booleans Int.one.
  Proof.
    unfold booleans.
    apply (join_correct (signed Int.zero) (signed Int.one)); simpl.
    right; unfold gamma, signed; simpl.
    split; reflexivity.
  Qed.

  Lemma is_in_interval_correct : forall a b ab,
    is_in_interval a b ab = true -> 
    forall i, γ ab i -> a <= Int.signed i <= b.
  Proof.
    simpl; unfold γ, gamma.
    unfold is_in_interval; simpl; intros.
    destruct ab; simpl in *.
    repeat rewrite andb_true_iff in *; repeat rewrite zle_true_iff in *; destruct H. lia.
  Qed.

  Lemma add_correct : forall ab1 ab2 i1 i2,
    γ ab1 i1 -> γ ab2 i2 ->
    γ (add ab1 ab2) (Int.add i1 i2).
  Proof.
    unfold γ, gamma, add, repr; simpl.
    destruct ab1; destruct ab2; simpl; intros; auto.
    case_eq (zle Int.min_signed (min0 + min1)
      && zle (max0 + max1) Int.max_signed); simpl; auto.
    repeat rewrite andb_true_iff; repeat rewrite zle_true_iff; intros [T1 T2].
    unfold Int.add.
    rewrite <- add_signed_unsigned.
    rewrite Int.signed_repr; try lia.
    intros; apply Int.signed_range.
  Qed.

  Lemma not_correct : forall ab i,
    γ ab i -> γ (not ab) (Int.not i).
  Proof.
    intros; unfold not.
    rewrite Int.not_neg.
    apply add_correct.
    apply neg_correct; auto.
    apply signed_correct.
  Qed.

  Lemma sub_correct : forall ab1 ab2 i1 i2,
    γ ab1 i1 -> γ ab2 i2 ->
    γ (sub ab1 ab2) (Int.sub i1 i2).
  Proof.
    simpl; unfold γ, gamma.
    destruct ab1; destruct ab2; simpl; intros; auto.
    unfold sub, repr; simpl.
    case_eq (zle Int.min_signed (min0 - max1)
      && zle (max0 - min1) Int.max_signed); simpl; auto.
    repeat rewrite andb_true_iff; repeat rewrite zle_true_iff; intros [T1 T2].
    unfold Int.sub.
    rewrite <- sub_signed_unsigned.
    rewrite Int.signed_repr; try omega.
    intros; apply Int.signed_range.
  Qed.

  Lemma mul_correct : forall ab1 ab2 i1 i2,
    γ ab1 i1 -> γ ab2 i2 ->
    γ (mult ab1 ab2) (Int.mul i1 i2).
  Proof.
    simpl; unfold γ, gamma.
    destruct ab1; destruct ab2; simpl; intros; auto.
    unfold mult, repr; simpl.
    case_eq (zle Int.min_signed
           (Zmin (Zmin (min0 * min1) (max0 * max1))
              (Zmin (max0 * min1) (min0 * max1))) &&
         zle
           (Zmax (Zmax (min0 * min1) (max0 * max1))
              (Zmax (max0 * min1) (min0 * max1))) Int.max_signed); simpl; auto.
    repeat rewrite andb_true_iff; repeat rewrite zle_true_iff; intros [T1 T2].
    unfold Int.mul.
    rewrite <- mult_signed_unsigned.
    assert (HZ:=Mult_interval_correct_min_max _ _ _ _ _ _ H H0).
    rewrite Int.signed_repr; try omega.
    intros; apply Int.signed_range.
  Qed.

  Lemma is_singleton_correct : forall i n n',
    γ i n -> is_singleton i = Some n' -> n'=n.
  Proof.
    unfold is_singleton; intros.
    destruct i.
    destruct zeq; inv H0.
    revert H.
    simpl; unfold γ, Interval.gamma; simpl; intros.
    replace max0 with (Int.signed n) by omega.
    rewrite Int.repr_signed; auto.
  Qed.

  Definition of_bool (b: bool): int :=
    if b then Int.one else Int.zero.

  Lemma is_bool_correct : forall i n b,
    γ i n -> is_bool i = Some b -> n = of_bool b.
  Proof.
    unfold is_bool; intros.
    destruct i.
    destruct zeq; inv H0.
    revert H2; generalize (Int.eq_spec (Int.repr max0) Int.zero); destruct Int.eq; intros.
    > inv H2.
      revert H.
      simpl; unfold γ, Interval.gamma; simpl; intros.
      replace max0 with (Int.signed n) in H0 by omega.
      rewrite Int.repr_signed in H0; auto.
    > revert H2; generalize (Int.eq_spec (Int.repr max0) Int.one); destruct Int.eq; intros.
      > inv H2.
        revert H.
        simpl; unfold γ, Interval.gamma; simpl; intros.
        replace max0 with (Int.signed n) in H1 by omega.
        rewrite Int.repr_signed in H1; auto.
      > congruence.
  Qed.

  Definition is_a_boolean (i:itv) : bool :=
    is_in_interval 0 1 i.

  Lemma is_a_boolean_correct: forall i n,
    γ i n ->
    is_a_boolean i = true ->
    n = Int.zero \/ n = Int.one.
  Proof.
    unfold is_a_boolean; intros.
    exploit is_in_interval_correct; eauto.
    intros.
    assert (Int.signed n = 0 \/ Int.signed n = 1) by omega.
    destruct H2; generalize (Int.repr_signed n); rewrite H2; compute; auto.
  Qed.

  Lemma is_a_boolean_correct_extra: forall i n,
    γ i n ->
    is_a_boolean i = true ->
    0 <= min i /\  max i <= 1.
  Proof.
    unfold is_a_boolean, is_in_interval; simpl; unfold order; intros.
    destruct i.
    rewrite andb_true_iff in H0; simpl.
    repeat rewrite zle_true_iff in H0.
    auto.
  Qed.

  Lemma is_a_boolean_correct_zero: forall i n,
    γ i n ->
    is_a_boolean i = true ->
    (max i) = 0 ->
    n = Int.zero.
  Proof.
    intros; exploit is_a_boolean_correct_extra; eauto.
    destruct 1.
    revert H; simpl; unfold gamma; simpl; destruct 1.
    assert (Int.signed n = 0) by omega.
    generalize (Int.repr_signed n); rewrite H5; compute; auto.
  Qed.

  Lemma is_a_boolean_correct_one: forall i n,
    γ i n ->
    is_a_boolean i = true ->
    (min i) = 1 ->
    n = Int.one.
  Proof.
    intros; exploit is_a_boolean_correct_extra; eauto.
    destruct 1.
    revert H; simpl; unfold gamma; simpl; destruct 1.
    assert (Int.signed n = 1) by omega.
    generalize (Int.repr_signed n); rewrite H5; compute; auto.
  Qed.

  Definition bool_op (f:int->int->int) (i1 i2:itv) : itv :=
    match is_singleton i1, is_singleton i2 with
      | Some i1, Some i2 => signed (f i1 i2)
      | _ , _ =>
        if is_a_boolean i1 && is_a_boolean i2 then booleans else top
    end.

  Definition IsBool (n:int) : Prop :=
    n = Int.zero \/ n = Int.one.

  Lemma IsBool_booleans: forall n,
    IsBool n -> γ booleans n.
  Proof.
    destruct 1; subst.
    apply bool_correct_zero.
    apply bool_correct_one.
  Qed.

  Lemma bool_op_correct : forall f,
    (forall x y, IsBool x -> IsBool y -> IsBool (f x y)) ->
    forall ab1 ab2 i1 i2,
      γ ab1 i1 -> γ ab2 i2 ->
      γ (bool_op f ab1 ab2) (f i1 i2).
  Proof.
    simpl; unfold bool_op; intros.
    case_eq (is_singleton ab1); intros.
    case_eq (is_singleton ab2); intros.
    exploit is_singleton_correct; eauto; clear H3.
    exploit (is_singleton_correct ab1); eauto; clear H2.
    intros; subst; apply signed_correct.
    case_eq (is_a_boolean ab1). 2: intros; apply gamma_top.
    case_eq (is_a_boolean ab2). 2: intros; apply gamma_top.
    simpl; intros; apply IsBool_booleans; apply H;
      unfold IsBool; eapply is_a_boolean_correct; eauto.
    case_eq (is_a_boolean ab1). 2: intros; apply gamma_top.
    case_eq (is_a_boolean ab2). 2: intros; apply gamma_top.
    simpl; intros; apply IsBool_booleans; apply H;
      unfold IsBool; eapply is_a_boolean_correct; eauto.
  Qed.

  Definition and : itv -> itv -> itv := bool_op Int.and.
  Definition or : itv -> itv -> itv := bool_op Int.or.
  Definition xor : itv -> itv -> itv := bool_op Int.xor.

  Lemma and_correct : forall ab1 ab2 i1 i2,
    γ ab1 i1 -> γ ab2 i2 ->
    γ (and ab1 ab2) (Int.and i1 i2).
  Proof.
    unfold and; apply bool_op_correct.
    unfold IsBool; destruct 1; destruct 1; subst; vm_compute; auto.
  Qed.

  Lemma or_correct : forall ab1 ab2 i1 i2,
    γ ab1 i1 -> γ ab2 i2 ->
    γ (or ab1 ab2) (Int.or i1 i2).
  Proof.
    unfold or; apply bool_op_correct.
    unfold IsBool; destruct 1; destruct 1; subst; vm_compute; auto.
  Qed.

  Lemma xor_correct : forall ab1 ab2 i1 i2,
    γ ab1 i1 -> γ ab2 i2 ->
    γ (xor ab1 ab2) (Int.xor i1 i2).
  Proof.
    unfold xor; apply bool_op_correct.
    unfold IsBool; destruct 1; destruct 1; subst; vm_compute; auto.
  Qed.

  Lemma shl_correct : forall ab1 ab2 i1 i2,
    γ ab1 i1 -> γ ab2 i2 ->
    γ (shl ab1 ab2) (Int.shl i1 i2).
  Proof.
    simpl; unfold gamma, shl; intros. 
    case_eq (is_singleton ab2); intros; auto.
    eapply is_singleton_correct in H1; simpl; eauto.
    subst; rewrite (Int.shl_mul i1 i2).
    apply mul_correct; simpl; auto.
    apply signed_correct.
    apply gamma_top.
  Qed.

  Lemma divs_correct : forall ab1 ab2 i1 i2,
    γ ab1 i1 -> γ ab2 i2 ->
    γ (div ab1 ab2) (Int.divs i1 i2).
  Proof.
    Hint Resolve Z_div_le Int.modulus_pos.
    pose proof zdiv_lt as V.
    assert (∀ a b, a >= 0 -> b > 0 -> a / b <= a) as U.
      intros. pose proof (Z_div_lt a b).
      elim_div. nia.
    simpl; unfold γ, gamma, div, Int.divs. intros ab1 ab2 i1 i2 H1 H2.
    case_eq (is_singleton ab2); auto. intros i H.
    eapply is_singleton_correct in H; simpl; eauto.
    destruct ab1 as (a,b); destruct zlt as [Z|Z]; subst; simpl in *.
    2: apply gamma_top.
    2: intros; apply gamma_top.
    repeat (rewrite Int.Zquot_Zdiv;[|intuition]).
    set (A := Int.signed i1). fold A in H1.
    set (B := Int.signed i2). fold B in H2, Z.
    replace (a + B - 1) with (a - 1 + 1 * B) by ring.
    rewrite Z_div_plus. 2: intuition.
    replace (A + B - 1) with (A - 1 + 1 * B) by ring.
    rewrite Z_div_plus. 2: intuition.
    replace (b + B - 1) with (b - 1 + 1 * B) by ring.
    rewrite Z_div_plus. 2: intuition.

    rewrite Int.signed_repr.
    repeat (destruct zlt; try omega); try (intuition; omega); split; try now intuition.
    cut ((A-1)/B < b /B). intuition.
    apply Zlt_le_trans with (0/B). 2: intuition.
    apply V; lia.
    cut ((a-1)/B < A / B). lia.
    apply V; lia.

    pose proof (Int.signed_range i1).
    destruct zlt; split.
    3: apply Zle_trans with 0;[discriminate| apply Z_div_pos; intuition].
    3: apply Zle_trans with (Int.max_signed / B) ;[|apply U]; intuition; discriminate.

    apply Zle_trans with (A). intuition.
    cut (A-1 <= (A-1)/B). lia.
    apply zdiv_mono; lia.
    
    apply Zle_trans with (0 / B + 1). intuition. discriminate.
  Qed.

  Definition shr_l (x: itv) (y: Z) : itv :=
    {| min := Z.shiftr x.(min) y
     ; max := Z.shiftr x.(max) y
    |}.

  Lemma shr_l_correct x y i :
    0 <= y < Int.modulus ->
    γ x i ->
    γ (shr_l x y) (Int.shr i (Int.repr y)).
  Proof.
    intros H (A, B).
    unfold shr_l, Int.shr.
    rewrite Int.unsigned_repr.
    2: unfold Int.max_unsigned; intuition.
    simpl; unfold γ, gamma; simpl.
    cut (2 ^ y > 0). intros.
    repeat (rewrite Z.shiftr_div_pow2;[|intuition]).
    rewrite Int.signed_repr.
    DLib.elim_div.
    nia.
    pose proof (Int.signed_range i).
    DLib.elim_div.
    compute_this Int.max_signed.
    compute_this Int.min_signed.
    nia.
    destruct H as [H _]; clear -H.
    destruct y as [|y|y]. easy.
    apply pow2_pos. intuition.
    intuition.
  Qed.

  Definition shr (x y: itv) : itv :=
    match is_singleton y with
    | Some l => shr_l x (Int.unsigned l)
    | None => top
    end.

  Lemma shr_correct x y i j :
    gamma x i -> gamma y j ->
    γ (shr x y) (Int.shr i j).
  Proof.
    intros X Y.
    unfold shr.
    generalize (is_singleton_correct y).
    destruct is_singleton as [l|].
    + intros K; specialize (K _ _ Y eq_refl). subst.
      generalize (shr_l_correct x (Int.unsigned j) _ (Int.unsigned_range _) X).
      generalize (Int.repr_unsigned j).
      generalize (Int.unsigned_range j).
      destruct Int.unsigned.
      - simpl. intros _ -> A; apply A.
      - simpl. intros _ -> A; apply A.
      - intuition.
    + intros _; apply gamma_top.
  Qed.

  (* ⊤ >>u y *)
  Definition shru_top (y: Z) : itv :=
    {| min := 0
     ; max := Z.shiftr (2 ^ 32 - 1) y
    |}.

  Lemma shru_top_correct i j :
    Int.unsigned j ≠ 0 →
    γ (shru_top (Int.unsigned j)) (Int.shru i j).
  Proof.
    intros H.
    unfold shru_top, Int.shru.
    assert (Int.unsigned j > 0) as K.
    { generalize (Int.unsigned_range j).
      destruct (Int.unsigned j); intuition.
    }
    assert (Z.shiftr (Int.unsigned i) (Int.unsigned j) <= Int.max_signed).
    { rewrite Z.shiftr_div_pow2. 2: intuition.
      generalize (Int.unsigned_range i).
      compute_this Int.max_unsigned;
      compute_this Int.max_signed;
      compute_this Int.modulus.
      set (z := 2 ^ Int.unsigned j).
      assert (z >= 2).
      { subst z. destruct (Int.unsigned j) as [|p|].
        intuition.
        simpl. clear -p.
        unfold Z.pow_pos.
        induction p using Pos.peano_ind.
        easy.
        rewrite Pos.iter_succ. intuition.
        lia.
      }
      elim_div. nia.
    }
    unfold γ. red. unfold gamma.
    rewrite Int.signed_repr.
    unfold min, max.
    split.
    apply Z.shiftr_nonneg, Int.unsigned_range.
    repeat (rewrite Z.shiftr_div_pow2;[|intuition]).
    apply Z_div_le. apply pow2_pos. easy.
    generalize (Int.unsigned_range i).
    simpl. smart_omega.
    split. etransitivity.
    2: apply Z.shiftr_nonneg, Int.unsigned_range.
    easy.
    easy.
  Qed.

  Definition shru (x y: itv) : itv :=
    match is_singleton y with
    | Some l =>
      let y' := Int.unsigned l in
      if Z_zerop y'
      then x
      else if znegb x.(min)
           then shru_top y'
           else shr_l x y'
    | None => top
    end.

  Lemma shru_correct x y i j :
    gamma x i -> gamma y j ->
    γ (shru x y) (Int.shru i j).
  Proof.
    destruct x as [xl xu].
    intros [X X'] Y.
    unfold shru, Int.shru. simpl in *.
    generalize (is_singleton_correct y).
    destruct is_singleton as [l|].
    + intros K; specialize (K _ _ Y eq_refl). subst.
      destruct Z_zerop as [->|K].
      * rewrite Z.shiftr_0_r.
        rewrite Int.repr_unsigned.
        split; easy.
      * destruct znegb.
        - now apply shru_top_correct.
        - assert (Int.unsigned i = Int.signed i) as L.
          revert X. generalize (Int.unsigned_range i).
          unfold Int.signed. destruct zlt; intuition.
          rewrite L.
          fold (Int.shr i j).
          rewrite <- (Int.repr_unsigned j) at 2.
          apply shr_l_correct.
          apply Int.unsigned_range.
          split; auto.
    + intros _; apply gamma_top.
  Qed.

  Lemma contains_correct : forall x ab,
    if contains x ab then γ ab x else ~ γ ab x.
  Proof.
    simpl; unfold γ, gamma, contains.
    destruct ab; simpl in *.
    case_eq_bool_in_goal.
    repeat rewrite andb_true_iff in *; repeat rewrite zle_true_iff in *; try omega.
    intros T; exploit zle_and_case; eauto.
    destruct 1; omega.
  Qed.

  Lemma gamma_backward_eq: forall ab1 ab2 ab1' ab2' i1 i2,
    backward_eq ab1 ab2 = (ab1',ab2') ->
    γ ab1 i1 ->
    γ ab2 i2 ->
    Int.eq i1 i2 = true ->
    γ ab1' i1 /\ γ ab2' i2.
  Proof.
    Opaque meet.
    simpl; unfold gamma, backward_eq; simpl; intros.
    destruct ab1; simpl in *;
      destruct ab2; simpl in *.
    generalize (Int.eq_spec i1 i2); rewrite H2; intros; subst.
    unfold backward_eq in H; inv H.
    split; apply meet_correct; simpl; auto.
  Qed.
  Transparent meet.

  Definition remove (it:itv) (i:int) : itvbot :=
    let (min,max) := it in
      let i := Int.signed i in
      if zeq i min then 
        botbind (meet it) (reduce (min+1) Int.max_signed)
        else if zeq i max then
          botbind (meet it) (reduce Int.min_signed (max-1))
          else NotBot it.

  Lemma remove_correct : forall ab i0 i,
    γ ab i -> Int.eq i i0 = false -> γ (remove ab i0) i.
  Proof.
    unfold γ.
    unfold remove; intros.
    destruct ab.
    destruct zeq.
    eapply botbind_spec.
    > intros. apply meet_correct; eauto.
      simpl in *; unfold γ, gamma, reduce in *; simpl in *.
      assert (Int.signed i <> Int.signed i0).
        generalize (Int.eq_spec i i0); rewrite H0.
        apply DLib.signed_inj.
      destruct zle; simpl; generalize (Int.signed_range i); unfold γ; simpl; try omega.
    > destruct zeq.
      eapply botbind_spec.
      > intros. apply meet_correct; eauto.
        simpl in *; unfold gamma, reduce in *; simpl in *.
        assert (Int.signed i <> Int.signed i0).
          generalize (Int.eq_spec i i0); rewrite H0.
          apply DLib.signed_inj.
        destruct (zle Int.min_signed (max0 -1)); simpl; generalize (Int.signed_range i). unfold γ. simpl. unfold γ. simpl. lia. lia.
    >  auto.
  Qed.

 Definition backward_neg (iin:itv) (out:itv) : itvbot := 
   meet iin (neg out).

  Lemma backward_neg_correct : forall ab1 ab2 i,
    γ ab1 i ->
    γ ab2 (Int.neg i) ->
    γ (backward_neg ab1 ab2) i.
  Proof.
    unfold backward_neg; intros.
    apply meet_correct; auto.
    rewrite <- (Int.neg_involutive i).
    simpl.
    apply neg_correct; auto.
  Qed.

 Definition backward_not (iin:itv) (out:itv) : itvbot := 
   meet iin (not out).

  Lemma backward_not_correct : forall ab1 ab2 i,
    γ ab1 i ->
    γ ab2 (Int.not i) ->
    γ (backward_not ab1 ab2) i.
  Proof.
    unfold backward_not; intros.
    apply meet_correct; auto.
    rewrite <- (Int.not_involutive i).
    simpl.
    apply not_correct; auto.
  Qed.


Lemma max_signed_unsigned: Int.max_unsigned = 2*Int.max_signed + 1.
Proof.
  unfold Int.max_signed, Int.max_unsigned.
  generalize Int.half_modulus_modulus; intros HH1.
  omega.
Qed.

Definition backward_add (ab1 ab2 res:itv) : itvbot * itvbot :=
  (meet ab1 (sub res ab2), 
    meet ab2 (sub res ab1)).

Lemma add_sub: forall i1 i2:int,
  (Int.sub (Int.add i1 i2) i2) = i1.
Proof.
  intros.
  rewrite Int.add_commut.
  rewrite Int.sub_add_l.
  rewrite Int.sub_idem.
  rewrite Int.add_zero_l; auto.
Qed.

Lemma backward_add_correct : forall ab1 ab2 res i1 i2,
  γ ab1 i1 ->
  γ ab2 i2 ->
  γ res (Int.add i1 i2) ->
  γ (fst (backward_add ab1 ab2 res)) i1 /\
  γ (snd (backward_add ab1 ab2 res)) i2.
Proof.
    unfold backward_not; intros.
    unfold backward_add; split; apply meet_correct; auto.
    > rewrite <- (add_sub i1 i2).
      simpl; apply sub_correct; auto.
    > rewrite <- (add_sub i2 i1).
      simpl; apply sub_correct; auto.
      rewrite Int.add_commut; auto.
Qed.

Definition backward_sub (ab1 ab2 res:itv) : itvbot * itvbot :=
  (meet ab1 (add res ab2), 
    meet ab2 (sub ab1 res)).

Lemma add_sub2: forall i1 i2:int,
  (Int.add (Int.sub i1 i2) i2) = i1.
Proof.
  intros.
  rewrite Int.sub_add_opp.
  rewrite Int.add_assoc.
  rewrite (Int.add_commut (Int.neg i2)).
  rewrite Int.add_neg_zero.
  rewrite Int.add_zero; auto.
Qed.

Lemma add_sub3: forall i1 i2:int,
  (Int.sub i1 (Int.sub i1 i2)) = i2.
Proof.
  intros.
  repeat rewrite Int.sub_add_opp.
  rewrite Int.neg_add_distr.
  rewrite Int.neg_involutive.
  rewrite <- Int.add_assoc.
  rewrite Int.add_neg_zero.
  rewrite Int.add_zero_l; auto.
Qed.

Lemma backward_sub_correct : forall ab1 ab2 res i1 i2,
  γ ab1 i1 ->
  γ ab2 i2 ->
  γ res (Int.sub i1 i2) ->
  γ (fst (backward_sub ab1 ab2 res)) i1 /\
  γ (snd (backward_sub ab1 ab2 res)) i2.
Proof.
    unfold backward_not; intros.
    unfold backward_sub; split; apply meet_correct; auto.
    > rewrite <- (add_sub2 i1 i2).
      simpl; apply add_correct; auto.
    > rewrite <- (add_sub3 i1 i2).
      simpl; apply sub_correct; auto.
Qed.

Definition backward_and_list (ab1 ab2 res:itv) : list (itvbot * itvbot) :=
  if is_a_boolean ab1 && is_a_boolean ab2 then (* useless test *)
    match is_singleton res with
      | None => (NotBot ab1,NotBot ab2) :: nil
      | Some i =>
        if Int.eq i Int.one then
          (meet ab1 (signed Int.one),
            meet ab2 (signed Int.one)) ::nil
          else if Int.eq i Int.zero then
            (NotBot ab1,meet ab2 (signed Int.zero)) ::
            (meet ab1 (signed Int.zero), NotBot ab2) :: nil
            else (NotBot ab1,NotBot ab2) :: nil
    end
    else (NotBot ab1,NotBot ab2) :: nil.


Lemma backward_and_list_correct : forall ab1 ab2 res i1 i2,
  γ ab1 i1 ->
  γ ab2 i2 ->
  γ res (Int.and i1 i2) ->
  exists ab, In ab (backward_and_list ab1 ab2 res) /\
    γ (fst ab) i1 /\
    γ (snd ab) i2.
Proof.
    unfold backward_and_list; intros.
    case_eq_bool_in_goal.
    > rewrite andb_true_iff; destruct 1.
      exploit (is_a_boolean_correct ab1); eauto; clear H2.
      exploit (is_a_boolean_correct ab2); eauto; clear H3.
      case_eq (is_singleton res); intros.
      > exploit is_singleton_correct; eauto; clear H2.
        intros; subst.
        generalize (Int.eq_spec (Int.and i1 i2) Int.one); destruct Int.eq; intros.
        > destruct H3; destruct H4; subst; vm_compute in H2; inv H2.
          econstructor; split; [left; eauto|split]; apply meet_correct; auto;
            simpl; apply signed_correct.
        > generalize (Int.eq_spec (Int.and i1 i2) Int.zero); destruct Int.eq; intros.
          > destruct H3.
            > econstructor; split; [left; eauto|idtac].
              split; auto; apply meet_correct; auto.
              subst; simpl; apply signed_correct.
            > destruct H4; subst; vm_compute in H5; inv H5.
              econstructor; split; [right; left; eauto|idtac].
              split; auto; apply meet_correct; auto.
              subst; simpl; apply signed_correct.
          > econstructor; split; [left;eauto|auto].
        > econstructor; split; [left;eauto|auto].
      > econstructor; split; [left;eauto|auto].
Qed.

Definition backward_or_list (ab1 ab2 res:itv) : list (itvbot * itvbot) :=
  if is_a_boolean ab1 && is_a_boolean ab2 then
    match is_singleton res with
      | None => (NotBot ab1,NotBot ab2) :: nil
      | Some i =>
        if Int.eq i Int.zero then
          (meet ab1 (signed Int.zero),
            meet ab2 (signed Int.zero)) ::nil
          else if Int.eq i Int.one then
            (NotBot ab1, meet ab2 (signed Int.one)) ::
            (meet ab1 (signed Int.one), NotBot ab2) :: nil
            else (NotBot ab1,NotBot ab2) :: nil
    end
    else (NotBot ab1,NotBot ab2) :: nil.

Lemma backward_or_list_correct : forall ab1 ab2 res i1 i2,
  γ ab1 i1 ->
  γ ab2 i2 ->
  γ res (Int.or i1 i2) ->
  exists ab, In ab (backward_or_list ab1 ab2 res) /\
    γ (fst ab) i1 /\
    γ (snd ab) i2.
Proof.
    unfold backward_or_list; intros.
    case_eq_bool_in_goal.
    > rewrite andb_true_iff; destruct 1.
      exploit (is_a_boolean_correct ab1); eauto; clear H2.
      exploit (is_a_boolean_correct ab2); eauto; clear H3.
      case_eq (is_singleton res); intros.
      > exploit is_singleton_correct; eauto; clear H2.
        intros; subst.
        generalize (Int.eq_spec (Int.or i1 i2) Int.zero); destruct Int.eq; intros.
        > destruct H3; destruct H4; subst; vm_compute in H2; inv H2.
          econstructor; split; [left; eauto|split]; apply meet_correct; auto;
            simpl; apply signed_correct.
        > generalize (Int.eq_spec (Int.or i1 i2) Int.one); destruct Int.eq; intros.
          > destruct H3.
            destruct H4; subst; vm_compute in H5; inv H5.
            > econstructor; split; [right; left; eauto|idtac].
              split; auto; apply meet_correct; auto.
              subst; simpl; apply signed_correct.
            > econstructor; split; [left; eauto|idtac].
              split; auto; apply meet_correct; auto.
              subst; simpl; apply signed_correct.
          > econstructor; split; [left;eauto|auto].    
        > econstructor; split; [left;eauto|auto].    
      > econstructor; split; [left;eauto|auto].    
Qed.

  Lemma gamma_backward_lt: forall ab1 ab2 ab1' ab2' i1 i2,
    backward_lt ab1 ab2 = (ab1',ab2') ->
    γ ab1 i1 ->
    γ ab2 i2 ->
    Int.lt i1 i2 = true ->
    γ ab1' i1 /\ γ ab2' i2.
  Proof.
    simpl; unfold γ, gamma, backward_lt; simpl; intros.
    destruct ab1; destruct ab2; simpl in *.
    assert (I1:=Int.signed_range i1).
    assert (I2:=Int.signed_range i2).
    unfold Int.lt in H2; destruct zlt. 2: congruence.
    unfold reduce in *.
    assert (M:=max_signed_unsigned).
    repeat destruct zle; simpl in *; inv H; simpl; try (split; omega);  
    unfold reduce in *; repeat destruct zle; simpl in *;
    unfold γ; simpl; try (split; lia).
  Qed.

  Lemma gamma_backward_ne: forall ab1 ab2 ab1' ab2' i1 i2,
    backward_ne ab1 ab2 = (ab1',ab2') ->
    γ ab1 i1 ->
    γ ab2 i2 ->
    negb (Int.eq i1 i2) = true ->
    γ ab1' i1 /\ γ ab2' i2.
  Proof.
    unfold backward_ne; intros.
    case_eq (backward_lt ab1 ab2); intros i1' i2' G1; rewrite G1 in *.
    case_eq (backward_lt ab2 ab1); intros i1'' i2'' G2; rewrite G2 in *.
    inv H.
    assert (H2':Int.eq i1 i2=false).
      destruct (Int.eq i1 i2); inv H2; auto.
    generalize (Int.eq_spec i1 i2); rewrite H2'; intros; subst.
    assert (Int.signed i1 <> Int.signed i2). 
      apply Int.eq_false in H.
      unfold Int.eq in H.
      destruct zeq; try congruence.
      red; intro; elim n.
      unfold Int.signed in *.
      generalize Int.half_modulus_modulus; intros HH1.
      generalize (Int.unsigned_range i1); intros R1. 
      generalize (Int.unsigned_range i2); intros R2.
      destruct zlt; destruct zlt; try omega.
    assert (Int.signed i1 < Int.signed i2 \/ Int.signed i2 < Int.signed i1) by omega.
    destruct H4.
    exploit (gamma_backward_lt ab1 ab2 i1' i2'); eauto.
    unfold Int.lt; destruct zlt; auto.
    destruct 1 as [HG1 HG2].
    destruct i1'; try (elim HG1; fail).
    destruct i2'; try (elim HG2; fail).
    split.
    > destruct i2''; auto.
      generalize (join_correct x x1); simpl; intros J1.
      apply J1; intuition.
    > destruct i1''; auto.  
      generalize (join_correct x0 x1); simpl; intros J2.
      apply J2; intuition.

    exploit (gamma_backward_lt ab2 ab1 i1'' i2''); eauto.
    unfold Int.lt; destruct zlt; auto.
    destruct 1 as [HG1 HG2].
    destruct i1''; try (elim HG1; fail).
    destruct i2''; try (elim HG2; fail).
    split.
    > destruct i1'; auto.
      generalize (join_correct x1 x0); simpl; intros J1.
      apply J1; intuition.
    > destruct i2'; auto.  
      generalize (join_correct x1 x); simpl; intros J2.
      apply J2; intuition.
  Qed.

  Lemma gamma_backward_le: forall ab1 ab2 ab1' ab2' i1 i2,
    backward_le ab1 ab2 = (ab1',ab2') ->
    γ ab1 i1 ->
    γ ab2 i2 ->
    negb (Int.lt i2 i1) = true ->
    γ ab1' i1 /\ γ ab2' i2.
  Proof.
    simpl; unfold γ, gamma, backward_le; simpl; intros.
    destruct ab1; simpl in *; try (intuition; fail);
      destruct ab2; simpl in *; try (intuition; fail).
    assert (I1:=Int.signed_range i1).
    assert (I2:=Int.signed_range i2).
    unfold Int.lt in H2; destruct zlt; simpl in H2. congruence.
    unfold reduce in *.
    repeat destruct zle; simpl in *; inv H; simpl; try lia.
    unfold reduce in *;
    repeat destruct zle; simpl; unfold γ; simpl in *; lia.
  Qed.

  Lemma cast_int16u_correct: forall ab i,
    cast_int16u ab = true ->
    γ ab i ->
    Int.signed i = Int.unsigned i.
  Proof.
    unfold cast_int16u; destruct ab ;simpl; intros.
    assert (I1:=Int.intrange i).
    assert (HI:=is_in_interval_correct _ _ _ H _ H0); clear H.
    unfold Int.signed, Int.unsigned in *.
    destruct zlt; try omega.
  Qed.

  Lemma gamma_backward_leu: forall ab1 ab2 ab1' ab2' i1 i2,
    backward_leu ab1 ab2 = (ab1',ab2') ->
    γ ab1 i1 ->
    γ ab2 i2 ->
    negb (Int.ltu i2 i1) = true ->
    γ ab1' i1 /\ γ ab2' i2.
  Proof.
    unfold backward_leu; simpl; intros.
    case_eq (cast_int16u ab1); intros; rewrite H3 in H; simpl in *.
    case_eq (cast_int16u ab2); intros; rewrite H4 in H; simpl in *.
    assert (negb (Int.lt i2 i1) = true).
    unfold Int.ltu in H2; destruct zlt; simpl in H2; try congruence.
    unfold Int.lt; destruct zlt; simpl; try congruence.    
    rewrite (cast_int16u_correct ab1 i1) in l; auto.
    rewrite (cast_int16u_correct ab2 i2) in l; auto.
    exploit gamma_backward_le; eauto.
    simpl; intros; inv H; split; auto.
    simpl; intros; inv H; split; auto.
  Qed.

  Lemma gamma_backward_ltu: forall ab1 ab2 ab1' ab2' i1 i2,
    backward_ltu ab1 ab2 = (ab1',ab2') ->
    γ ab1 i1 ->
    γ ab2 i2 ->
    Int.ltu i1 i2 = true ->
    γ ab1' i1 /\ γ ab2' i2.
  Proof.
    unfold backward_ltu; simpl; intros.
    case_eq (cast_int16u ab1); intros; rewrite H3 in H; simpl in *.
    case_eq (cast_int16u ab2); intros; rewrite H4 in H; simpl in *.
    assert (Int.lt i1 i2 = true).
    unfold Int.ltu in H2; destruct zlt; simpl in H2; try congruence.
    unfold Int.lt; destruct zlt; simpl; try congruence.    
    rewrite (cast_int16u_correct ab1 i1) in g; auto.
    rewrite (cast_int16u_correct ab2 i2) in g; auto.
    exploit gamma_backward_lt; eauto.
    simpl; intros; inv H; split; auto.
    simpl; intros; inv H; split; auto.
  Qed.


Definition swap {A} (xy:A*A) : A*A :=
  let (x,y) := xy in (y,x).

Definition backward_cmp (c:comparison) (ab1 ab2 res:itv) : itvbot * itvbot :=
  match is_singleton res with
    | None => (NotBot ab1,NotBot ab2) 
    | Some i =>
      if Int.eq i Int.one then
        match c with
          | Ceq => let ab := meet ab1 ab2 in (ab,ab)
          | Cne => backward_ne ab1 ab2 
          | Clt => backward_lt ab1 ab2
          | Cle => backward_le ab1 ab2
          | Cgt => swap (backward_lt ab2 ab1)
          | Cge => swap (backward_le ab2 ab1)
        end
        else if Int.eq i Int.zero then
        match c with
          | Ceq => backward_ne ab1 ab2 
          | Cne => let ab := meet ab1 ab2 in (ab,ab)
          | Cge => backward_lt ab1 ab2
          | Cgt => backward_le ab1 ab2
          | Cle => swap (backward_lt ab2 ab1)
          | Clt => swap (backward_le ab2 ab1)
        end
        else (NotBot ab1,NotBot ab2) 
    end.

Lemma pair_eq : forall A B (x:A*B), x = (fst x, snd x).
Proof.
  destruct x; auto.
Qed.
Hint Resolve pair_eq.

Lemma swap_inv {A} (x:A*A) (u v: A) : swap x = (u,v) -> x = (v,u).
Proof. destruct x; simpl; congruence. Qed.

Opaque meet.
Lemma backward_cmp_correct : forall c ab1 ab2 res i1 i2,
  γ ab1 i1 ->
  γ ab2 i2 ->
  γ res (of_bool (Int.cmp c i1 i2)) ->
  let '(u,v) := backward_cmp c ab1 ab2 res in
  γ u i1 /\ γ v i2.
Proof.
    unfold backward_cmp; intros.
    case_eq (is_singleton res); intros; auto.
    exploit is_singleton_correct; eauto; clear H2.
    intros; subst.
    generalize (Int.eq_spec (of_bool (Int.cmp c i1 i2)) Int.one); destruct Int.eq; intros.
    > revert H2; case_eq (Int.cmp c i1 i2); try (unfold of_bool; intros _ T; inv T; fail).
      intros T _.
      destruct c; simpl in T.
      > generalize (Int.eq_spec i1 i2); rewrite T; intros; subst.
        split; apply meet_correct; auto.
      > pairs. intros; eapply gamma_backward_ne; eauto.
      > pairs. intros; eapply gamma_backward_lt; eauto.
      > pairs; intros; eapply gamma_backward_le; eauto.
      > pairs. intros Q. apply swap_inv in Q.
        exploit (gamma_backward_lt ab2 ab1); eauto.
        intuition.
      > pairs. intros Q. apply swap_inv in Q.
        exploit (gamma_backward_le ab2 ab1); eauto.
        intuition.
    > revert H2; case_eq (Int.cmp c i1 i2).
      intros _ T; elim T; compute; auto.
      intros T _.
      pairs.
      rewrite Int.eq_true.
      destruct c; simpl in T.
      > intros; eapply gamma_backward_ne; eauto.
        rewrite T; auto.
      > generalize (Int.eq_spec i1 i2); destruct Int.eq; inv T; intros; subst.
        inj. split; eapply meet_correct; auto.
      > intros Q. apply swap_inv in Q.
        exploit (gamma_backward_le ab2 ab1); eauto.
        rewrite T; auto.
        intuition.
      > intros Q. apply swap_inv in Q.
        exploit (gamma_backward_lt ab2 ab1); eauto.
        destruct Int.lt; inv T; auto.
        intuition.
      > intros. eapply gamma_backward_le; eauto.
        rewrite T; auto.
      > intros. eapply gamma_backward_lt; eauto.
        destruct Int.lt; inv T; auto.
Qed.

Definition backward_cmpu (c:comparison) (ab1 ab2 res:itv) : itvbot * itvbot :=
  match is_singleton res with
    | None => (NotBot ab1,NotBot ab2) 
    | Some i =>
      if Int.eq i Int.one then
        match c with
          | Ceq => let ab := meet ab1 ab2 in (ab,ab)
          | Cne => backward_ne ab1 ab2 
          | Clt => backward_ltu ab1 ab2
          | Cle => backward_leu ab1 ab2
          | Cgt => swap (backward_ltu ab2 ab1)
          | Cge => swap (backward_leu ab2 ab1)
        end
        else if Int.eq i Int.zero then
        match c with
          | Ceq => backward_ne ab1 ab2 
          | Cne => let ab := meet ab1 ab2 in (ab,ab)
          | Cge => backward_ltu ab1 ab2
          | Cgt => backward_leu ab1 ab2
          | Cle => swap (backward_ltu ab2 ab1)
          | Clt => swap (backward_leu ab2 ab1)
        end
        else (NotBot ab1,NotBot ab2) 
    end.

Lemma backward_cmpu_correct : forall c ab1 ab2 res i1 i2,
  γ ab1 i1 ->
  γ ab2 i2 ->
  γ res (of_bool (Int.cmpu c i1 i2)) ->
  let '(u,v) := backward_cmpu c ab1 ab2 res in
  γ u i1 /\ γ v i2.
Proof.
    unfold backward_cmpu; intros.
    case_eq (is_singleton res); intros; auto.
    exploit is_singleton_correct; eauto; clear H2.
    intros; subst.
    generalize (Int.eq_spec (of_bool (Int.cmpu c i1 i2)) Int.one); destruct Int.eq; intros.
    > revert H2; case_eq (Int.cmpu c i1 i2); try (unfold of_bool; intros _ T; inv T; fail).
      intros T _.
      destruct c; simpl in T.
      > generalize (Int.eq_spec i1 i2); rewrite T; intros; subst.
        split; apply meet_correct; auto.
      > pairs. intros; eapply gamma_backward_ne; eauto.
      > pairs. intros; eapply gamma_backward_ltu; eauto.
      > pairs. intros; eapply gamma_backward_leu; eauto.
      > pairs. intros Q. apply swap_inv in Q.
        exploit (gamma_backward_ltu ab2 ab1); eauto.
        intuition.
      > pairs. intros Q. apply swap_inv in Q.
        exploit (gamma_backward_leu ab2 ab1); eauto.
        intuition.
    > revert H2; case_eq (Int.cmpu c i1 i2).
      intros _ T; elim T; compute; auto.
      intros T _.
      rewrite Int.eq_true.
      destruct c; simpl in T.
      > pairs. intros; eapply gamma_backward_ne; eauto.
        rewrite T; auto.
      > generalize (Int.eq_spec i1 i2); destruct Int.eq; inv T; intros; subst.
        split; apply meet_correct; auto.
      > pairs. intros Q. apply swap_inv in Q.
        exploit (gamma_backward_leu ab2 ab1); eauto.
        rewrite T; auto.
        intuition.
      > pairs. intros Q. apply swap_inv in Q.
        exploit (gamma_backward_ltu ab2 ab1); eauto.
        destruct Int.ltu; inv T; auto.
        intuition.
      > pairs. intros; eapply gamma_backward_leu; eauto.
        rewrite T; auto.
      > pairs. intros; eapply gamma_backward_ltu; eauto.
        destruct Int.ltu; inv T; auto.
Qed.

  Hint Resolve gamma_top signed_correct.

  Definition ugamma (i:itv) (v:int) : Prop :=
    min i <= Int.unsigned v <= max i.

  Definition reduc2signed (i:itv) : itv :=
    match i with
      | ITV m M =>
        if zlt M Int.half_modulus
        then i
        else if zle Int.half_modulus m
             then ITV (m - Int.modulus) (M - Int.modulus)
             else ⊤
    end.
  Definition reduc2unsigned (i: itv) : itv :=
    match i with
      | ITV m M =>
        if zle 0 m
        then i
        else if zlt M 0
             then ITV (m + Int.modulus) (M + Int.modulus)
             else utop
    end.
  Lemma reduc2unsigned_correct: forall i v,
    gamma i v ->
    ugamma (reduc2unsigned i) v.
  Proof.
    intros (m & M) v (A & B). simpl in *.
    pose proof (Int.signed_range v).
    pose proof (Int.unsigned_range v).
    unfold ugamma, Int.signed in *.
    repeat destruct zlt; repeat destruct zle; simpl; intuition;
    unfold Int.max_unsigned; intuition.
  Qed.
  Lemma reduc2signed_correct: forall i v,
    ugamma i v ->
    gamma (reduc2signed i) v.
  Proof.
    intros (m & M) v (A & B). simpl in *. unfold gamma, Int.signed.
    pose proof (Int.min_signed_neg).
    pose proof (Int.unsigned_range v).
    repeat destruct zlt; repeat destruct zle; simpl; intuition.
    unfold Int.max_signed. intuition.
    unfold Int.min_signed, Int.half_modulus in *.
    assert (-(Int.modulus / 2) + Int.modulus <= Int.unsigned v); intuition.
    apply Zle_trans with (Int.modulus / 2); intuition.
    apply Zle_trans with 0. intuition.
    unfold Int.max_signed, Int.half_modulus in *. simpl. intuition.
  Qed.

Lemma ugamma_top: ∀ x, ugamma utop x.
Proof.
  intros x. pose proof (Int.unsigned_range x). split; intuition.
  simpl. unfold Int.max_unsigned. intuition.
Qed.

Lemma join_correctu : ∀ a b, ugamma a ∪ ugamma b ⊆ ugamma (a ⊔ b).
Proof.
  intros (a & A) (b & B) x [H|H]; simpl; apply Zmin_case_strong; apply Zmax_case_strong; auto;
  destruct H as (H & L); unfold ugamma; simpl in *;
  intuition.
Qed.

Instance itvu_wl : weak_lattice itv :=
  { leb := order
  ; top := utop
  ; join := join
  ; widen := widen
  }.

Lemma itvu_adom : adom itv int itvu_wl ugamma.
Proof.
  split.
  unfold γ, ugamma.
  intros (a1,b1) (a2,b2) H a K. simpl in *.
  rewrite andb_true_iff in H; repeat rewrite zle_true_iff in H.
  intuition.
  exact ugamma_top.
  exact join_correctu.
Qed.
Definition unsigned_itv_adom := itvu_adom.

Local Notation Γ := ugamma.

Transparent meet.
Lemma meet_correctu : forall x y,
  Γ x ∩ Γ y ⊆ match x ⊓ y with Bot => ∅ | NotBot z => Γ z end.
Proof.
  Hint Resolve Zmax_lub Zmin_glb.
  intros (x & X) (y & Y) i.
  unfold ugamma; simpl.
  intros [H0 H1].
  destruct H0, H1. simpl in *.
  unfold reduce. bif.
  simpl. intuition.
  assert (Zmax x y <= Int.unsigned i) by intuition.
  assert (Int.unsigned i <= Zmin X Y) by intuition.
  intuition.
Qed.
Opaque meet.

End Interval.

Definition ints_in_range (r: signedness-> Interval.itv+⊥) : int -> Prop :=
    lift_gamma Interval.gamma (r Signed)
  ∩ lift_gamma Interval.ugamma (r Unsigned).
