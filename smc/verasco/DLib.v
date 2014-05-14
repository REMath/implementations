(** Utility definitions by David. *)

Require Import Utf8.
Require Import Coqlib.
Require Import compcert.Maps.

(* For readability of proof scripts *)
Tactic Notation ">" tactic(t) := t.
Tactic Notation "by" tactic(t) := t; fail "this goal should be proved at this point".

Ltac destruct_bool_in_goal :=
  match goal with [ |- context[if ?x then _ else _]] => destruct x end.
Ltac destruct_option_in_goal :=
  match goal with [ |- context[match ?x with Some _ => _ | None => _ end]] => destruct x end.
Ltac case_eq_bool_in_goal :=
  match goal with [ |- context[if ?x then _ else _]] => case_eq x end.
Ltac case_eq_option_in_goal :=
  match goal with [ |- context[match ?x with Some _ => _ | None => _ end]] => case_eq x end.
Ltac destruct_bool :=
  match goal with 
    [ _ : context[if ?x then _ else _] |- _] => destruct x 
  | [ |- context[if ?x then _ else _]] => destruct x 
  end.
Ltac destruct_option :=
  match goal with
    [ _ : context[match ?x with Some _ => _ | None => _ end] |- _] => destruct x
  | [ |- context[match ?x with Some _ => _ | None => _ end]] => destruct x
  end.

Ltac simpl_option :=
  match goal with
    [ id : Some _ = Some _ |- _ ] => inv id
  | [ id : None = Some _ |- _ ] => inv id
  | [ id : Some _ = None |- _ ] => inv id
  end.

Ltac invh f :=
    match goal with
      [ id: f |- _ ] => inv id
    | [ id: f _ |- _ ] => inv id
    | [ id: f _ _ |- _ ] => inv id
    | [ id: f _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    end.

Ltac bif :=
  match goal with |- context[if ?a then _ else _] => destruct a end; try congruence.

Ltac bif' :=
  match goal with |- context[if ?a then _ else _] => destruct a eqn: ? end; try congruence.

Ltac pairs :=
  repeat
  match goal with
    | |- context[let '(_,_) := ?x in _] =>
      case_eq x; intros ? ?
  end.

Ltac autorw :=
  match goal with
    | [H: _ = _ |- _] => rewrite H in *
  end.

Ltac autorw' := repeat (progress (autorw; subst)).

Ltac inj :=
  repeat
  match goal with
    | [H : ?f _ = ?f _ |- _] => injection H; intros ?; subst; clear H
    | [H : ?f _ _ = ?f _ _ |- _] => injection H; intros ? ?; subst; clear H
  end.
Definition ptree_forall {A:Type} (m:PTree.t A) (f:positive->A->bool) : bool :=
  PTree.fold (fun b0 p a => b0 && f p a) m true.

Lemma ptree_forall_correct1 : forall A (f:positive->A->bool) m,
  ptree_forall m f = true ->
  forall n ins, m!n = Some ins -> f n ins = true.
Proof.
  intros A f m; unfold ptree_forall.
  apply PTree_Properties.fold_rec
    with (P:=fun m b => b = true -> forall n ins, m!n = Some ins -> f n ins = true); intros.
  apply H0; auto.
  rewrite H; auto.
  rewrite PTree.gempty in H0; congruence.
  rewrite PTree.gsspec in H3; destruct peq.
  inv H3.
  elim andb_prop with (1:=H2); auto.
  elim andb_prop with (1:=H2); auto.
Qed.

Lemma ptree_forall_correct2 : forall A (f:positive->A->bool) m,
  (forall n ins, m!n = Some ins -> f n ins = true) ->
  ptree_forall m f = true.
Proof.
  intros A f m; unfold ptree_forall.
  apply PTree_Properties.fold_rec
    with (P:=fun m b => (forall n ins, m!n = Some ins -> f n ins = true) -> b = true ); intros; auto.
  apply H0; auto.
  intros n ins; rewrite H; auto.
  rewrite H1; simpl.
  apply H2.
  rewrite PTree.gss; auto.
  intros; apply H2.
  rewrite PTree.gsspec; destruct peq; auto; congruence.
Qed.

Lemma ptree_forall_correct : forall A (f:positive->A->bool) m,
  ptree_forall m f = true <->
  (forall n ins, m!n = Some ins -> f n ins = true).
Proof.
  split; eauto using ptree_forall_correct1, ptree_forall_correct2.
Qed.


Require Import ZArith.
Require Psatz.

Open Scope Z_scope.

Ltac elim_div :=
  unfold Zdiv, Zmod;
  repeat 
    match goal with
      |  H : context[ Zdiv_eucl ?X ?Y ] |-  _ =>   
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
      |  |-  context[ Zdiv_eucl ?X ?Y ] =>   
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
    end; unfold Remainder.

Definition znegb (x: Z) : { x < 0 } + { x >= 0 }.
  refine (match x with Zneg _ => left _ | _ => right _ end);
  clear x;
  abstract Psatz.lia.
Proof.
Defined.

Definition z2n (z: Z) : { n : N | Z.of_N n = z } + {z < 0} :=
  match z with
  | Zpos p => inleft (exist _ (Npos p) eq_refl)
  | Z0 => inleft (exist _ N0 eq_refl)
  | _ => inright eq_refl
  end.

Lemma Zmult_bounds1 : forall x1 x2 y1 y2 : Z, 
  0 <= x1 <= x2 -> 
  0 <= y1 <= y2 -> 
  x1 * y1 <= x2 * y2.
Proof.
intros; apply Zmult_le_compat; omega.
Qed.

Lemma Zmult_opp : forall x y : Z, x*y=(-x)*(-y).
Proof.
  intros; ring.
Qed.

Lemma Zmult_bounds2 : forall x1 x2 y1 y2 : Z, 
   x1 <= x2 <= 0-> 
   y1 <= y2 <= 0 -> 
   x2 * y2 <= x1 * y1.
Proof.
intuition.
rewrite (Zmult_opp x2); rewrite (Zmult_opp x1).
apply Zmult_bounds1; omega.
Qed.

Lemma Zmult_interval_right_right : forall a b c d x y,
  a <= x <= b -> 
  c <= y <= d ->
  0 <= a -> 0 <= c ->
  a*c <= x*y <= b*d.
Proof.
  intuition.
  apply Zmult_bounds1; split; try omega.
  apply Zmult_bounds1; split; try omega.
Qed.

Lemma Zmult_ineq1 : forall a b c d,
  c*(-d) <= a*(-b) -> a*b <= c*d.
Proof.
  intuition.
  replace (c*d) with (-(c*-d)).
  replace (a*b) with (-(a*-b)).
  omega.
  ring.
  ring.
Qed. 

Lemma Zmult_ineq2 : forall a b c d,
  (-c)*d <= (-a)*b -> a*b <= c*d.
Proof.
  intuition.
  replace (c*d) with (-(-c*d)).
  replace (a*b) with (-(-a*b)).
  omega.
  ring.
  ring.
Qed. 

Lemma Zmult_split : forall a b c d,
  a*b <= 0 -> 0 <= c*d -> a*b <= c*d.
Proof.
  intros; apply Zle_trans with 0; auto.
Qed.
Hint Resolve Zmult_split Zmult_ineq1.

Lemma sign_rule1 : forall x y : Z,
  x >= 0 -> y <= 0 -> x * y <= 0.
Proof.
  intros.
  replace 0 with (x*0)%Z; auto with zarith.
Qed.
Lemma sign_rule2 : forall x y : Z,
  x >= 0 -> y >= 0 -> 0 <= x * y.
Proof.
  intros.
  replace 0 with (x*0)%Z; auto with zarith.
Qed.
Lemma sign_rule3 : forall x y : Z,
  x <= 0 -> y <= 0 -> 0 <= x * y.
Proof.
  intros.
  rewrite (Zmult_opp x).
  apply sign_rule2; omega.
Qed.
Lemma sign_rule4 : forall x y : Z,
  x <= 0 -> y >= 0 -> x * y <= 0.
Proof.
  intros.
  rewrite Zmult_comm.
  apply sign_rule1; auto.
Qed.
Hint Resolve sign_rule1 sign_rule2 sign_rule3 sign_rule4 : sign.

Lemma Zpos_or_not : forall x : Z, {x>=0}+{x<0}.
Proof.
  intros x; destruct (Z_le_dec 0 x); auto.
  left; omega.
  right; omega.
Qed.

Lemma Zpos_strict_or_not : forall x : Z, {x>0}+{x<=0}.
Proof.
  intros x; destruct (Z_lt_dec 0 x).
  left; omega.
  right; omega.
Qed.

Hint Resolve Zmult_bounds1 Zmult_ineq1.

Lemma Zmult_interval_right_mid : forall a b c d x y,
  a <= x <= b -> 
  c <= y <= d ->
  0 <= a -> c < 0 -> 0 <= d ->
  b*c <= x*y <= b*d.
Proof.
  intuition;
  (assert (b>=0); [omega|idtac]);
  (assert (x>=0); [omega|idtac]);
  destruct (Zpos_or_not y); auto with sign zarith.
Qed.

Hint Resolve Zmult_bounds2 Zmult_ineq2.

Lemma Zmult_interval_left_mid : forall a b c d x y,
  a <= x <= b -> 
  c <= y <= d ->
  b < 0 -> c < 0 -> 0 <= d ->
  a*d <= x*y <= a*c.
Proof.
  intuition;
  (assert (a<0); [omega|idtac]);
  (assert (x<0); [omega|idtac]);
  destruct (Zpos_or_not y); auto with sign zarith.
Qed.
  
Lemma Zmult_interval_right_left : forall a b c d x y,
  a <= x <= b -> 
  c <= y <= d ->
  0 <= a -> d < 0  ->
  b*c <= x*y <= a*d.
Proof.
  intuition; auto with zarith.
Qed.

Lemma Zmult_interval_left_left : forall a b c d x y,
  a <= x <= b -> 
  c <= y <= d ->
  b < 0 -> d < 0  ->
  b*d <= x*y <= a*c.
Proof.
  intuition; auto with zarith.
Qed.

Lemma Z_max_le_r : forall x y : Z, y <= (Zmax x y).
Proof.
  intros; apply Zmax2.
Qed.

Lemma Z_max_le_l : forall x y : Z, x <= (Zmax x y).
Proof.
  intros; apply Zmax1.
Qed.

Hint Resolve Zle_min_l Zle_min_r Z_max_le_l Z_max_le_r.

Lemma ineq_trans : forall a b c d e : Z,
 a <= b -> c <= d ->
 b <= e <= c ->
 a <= e <= d.
Proof.
  intuition; omega.
Qed.

Lemma Z_min4_le_1 : forall x y z t: Z, Zmin (Zmin x y) (Zmin z t) <= x.
Proof.
  intros.
  apply Zle_trans with (Zmin x y); auto.
Qed.

Lemma Z_min4_le_2 : forall x y z t: Z, Zmin (Zmin x y) (Zmin z t) <= y.
Proof.
  intros.
  apply Zle_trans with (Zmin x y); auto.
Qed.

Lemma Z_min4_le_3 : forall x y z t: Z, Zmin (Zmin x y) (Zmin z t) <= z.
Proof.
  intros.
  apply Zle_trans with (Zmin z t); auto.
Qed.

Lemma Z_min4_le_4 : forall x y z t: Z, Zmin (Zmin x y) (Zmin z t) <= t.
Proof.
  intros.
  apply Zle_trans with (Zmin z t); auto.
Qed.

Lemma Z_max4_le_1 : forall x y z t: Z, x <= Zmax (Zmax x y) (Zmax z t).
Proof.
  intros.
  apply Zle_trans with (Zmax x y); auto.
Qed.

Lemma Z_max4_le_2 : forall x y z t: Z, y <= Zmax (Zmax x y) (Zmax z t).
Proof.
  intros.
  apply Zle_trans with (Zmax x y); auto.
Qed.

Lemma Z_max4_le_3 : forall x y z t: Z, z <= Zmax (Zmax x y) (Zmax z t).
Proof.
  intros.
  apply Zle_trans with (Zmax z t); auto.
Qed.

Lemma Z_max4_le_4 : forall x y z t: Z, t <= Zmax (Zmax x y) (Zmax z t).
Proof.
  intros.
  apply Zle_trans with (Zmax z t); auto.
Qed.

Hint Resolve Z_max4_le_1 Z_max4_le_2 Z_max4_le_3 Z_max4_le_4
             Z_min4_le_1 Z_min4_le_2 Z_min4_le_3 Z_min4_le_4.

Require Import compcert.Integers.
(* Compcert integers *)

Ltac compute_this val :=
  let x := fresh in set val as x in *; vm_compute in x; subst x.

Ltac smart_omega :=
  compute_this Int.modulus; compute_this Int.half_modulus;
  compute_this Int.max_unsigned;
  compute_this Int.min_signed; compute_this Int.max_signed;
  omega.

  Lemma repr_mod_prop: forall x y,
    Int.repr (x + y * Int.modulus) = Int.repr x.
  Proof.
    intros.
    apply Int.eqm_repr_eq, Int.eqm_unsigned_repr_r.
    exists y. ring.
  Qed.

  Lemma Z_of_nat_gt: forall n, (n > 0)%nat -> Z_of_nat n > 0.
  Proof.
    intros.
    apply (inj_gt n 0).
    auto.
  Qed.

  Lemma sign_ext_same : forall n m i,
    (m > 0)%nat ->
    Int.wordsize = ((S n)+m)%nat ->
    -(two_power_nat n) <= Int.signed i <= (two_power_nat n) -1 ->
    Int.sign_ext (Z_of_nat (S n)) i = i.
  Proof.
    intros.
    apply Int.same_bits_eq.
    intros.
    rewrite Int.bits_sign_ext; try now simpl; auto.
    destruct zlt. auto.
    rewrite <- (Int.repr_signed i), !Int.testbit_repr by (zify; omega).
    destruct (zlt (Int.signed i) 0).
    rewrite !Int.Ztestbit_above_neg with (n:=n); try (zify; omega). reflexivity.
    rewrite !Int.Ztestbit_above with (n:=n); try (zify; omega). reflexivity.
  Qed.

  Lemma zero_ext_same : forall n m i,
    (m > 0)%nat ->
    Int.wordsize = (n+m)%nat ->
    0 <= Int.signed i <= (two_power_nat n) -1 ->
    Int.zero_ext (Z_of_nat n) i = i.
  Proof.
    intros.
    apply Int.same_bits_eq.
    intros.
    rewrite Int.bits_zero_ext; try now simpl; auto.
    destruct zlt. auto.
    rewrite <- (Int.repr_signed i), !Int.testbit_repr by (zify; omega).
    rewrite !Int.Ztestbit_above with (n:=n); try (zify; omega). reflexivity.
  Qed.

  Lemma two_power_nat_div2 : forall n,
    two_power_nat (S n) / 2 = two_power_nat n.
  Proof.
    unfold two_power_nat; intros; simpl.
    unfold shift_nat; simpl.
    generalize (iter_nat n positive xO 1%positive); intros.
    apply Zdiv_unique with 0; try omega.
    rewrite Zmult_comm; auto.
  Qed.

  Lemma pow2_pos n : n > 0 → 2 ^ n > 0.
  Proof.
    destruct n as [|n|]. intuition.
    intros _.
    simpl. unfold Z.pow_pos.
    induction n using Pos.peano_ind. easy.
    rewrite Pos.iter_succ.
    intuition.
    inversion 1.
  Qed.

  Lemma neg_signed_unsigned : forall x,
    Int.repr (- (Int.signed x)) = Int.repr (- (Int.unsigned x)).
  Proof.
    intros.
    unfold Int.signed; destruct zlt; auto.
    replace (- (Int.unsigned x - Int.modulus)) with
      ( - Int.unsigned x + (1) * Int.modulus) by ring.
    apply repr_mod_prop.
  Qed.

  Lemma zle_and_case: forall x y z t,
    zle x y && zle z t = false -> x > y \/ z > t. 
  Proof.
    intros x1 x2 x3 x4.
    destruct zle; simpl.
    destruct zle; simpl; try congruence.
    omega.
    omega.
  Qed.

  Lemma add_signed_unsigned : forall x y,
    Int.repr (Int.signed x + Int.signed y) = Int.repr (Int.unsigned x + Int.unsigned y).
  Proof.
    intros.
    unfold Int.signed; do 2 destruct zlt; try reflexivity.
    replace (Int.unsigned x + (Int.unsigned y - Int.modulus)) with
      ((Int.unsigned x + Int.unsigned y) + (- 1) * Int.modulus) by ring.
    apply repr_mod_prop.
    replace ((Int.unsigned x - Int.modulus) + Int.unsigned y) with
      ((Int.unsigned x + Int.unsigned y) + (-1) * Int.modulus) by ring.
    apply repr_mod_prop.
    replace ((Int.unsigned x - Int.modulus) + (Int.unsigned y - Int.modulus)) with
      ((Int.unsigned x + Int.unsigned y) + (- 2) * Int.modulus) by ring.
    apply repr_mod_prop.
  Qed.

  Lemma sub_signed_unsigned : forall x y,
    Int.repr (Int.signed x - Int.signed y) = Int.repr (Int.unsigned x - Int.unsigned y).
  Proof.
    intros.
    unfold Int.signed; do 2 destruct zlt; try reflexivity.
    replace (Int.unsigned x - (Int.unsigned y - Int.modulus)) with
      ((Int.unsigned x - Int.unsigned y) + (1) * Int.modulus) by ring.
    apply repr_mod_prop.
    replace ((Int.unsigned x - Int.modulus) - Int.unsigned y) with
      ((Int.unsigned x - Int.unsigned y) + (-1) * Int.modulus) by ring.
    apply repr_mod_prop.
    replace ((Int.unsigned x - Int.modulus) - (Int.unsigned y - Int.modulus)) with
      ((Int.unsigned x - Int.unsigned y)) by ring.
    auto.
  Qed.

  Lemma mult_signed_unsigned : forall x y,
    Int.repr (Int.signed x * Int.signed y) = Int.repr (Int.unsigned x * Int.unsigned y).
  Proof.
    intros.
    unfold Int.signed; do 2 destruct zlt; try reflexivity.
    replace (Int.unsigned x * (Int.unsigned y - Int.modulus)) with
      ((Int.unsigned x * Int.unsigned y) + (- Int.unsigned x) * Int.modulus) by ring.
    apply repr_mod_prop.
    replace ((Int.unsigned x - Int.modulus) * Int.unsigned y) with
      ((Int.unsigned x * Int.unsigned y) + (- Int.unsigned y) * Int.modulus) by ring.
    apply repr_mod_prop.
    replace ((Int.unsigned x - Int.modulus)* (Int.unsigned y - Int.modulus)) with
      ((Int.unsigned x * Int.unsigned y) + (- Int.unsigned x - Int.unsigned y + Int.modulus) * Int.modulus) by ring.
    apply repr_mod_prop.
  Qed.

  Lemma zle_true_iff : forall x y: Z,
    proj_sumbool (zle x y) = true <-> x <= y.
  Proof.
    intros; destruct zle; simpl; split; auto; congruence.
  Qed.

Lemma unsigned_inj i j : i ≠ j → Int.unsigned i ≠ Int.unsigned j.
Proof. 
  intro. contradict H.
  rewrite <- Int.repr_unsigned with i.
  rewrite <- Int.repr_unsigned with j.
  congruence.
Qed.

Lemma signed_inj i j : i ≠ j → Int.signed i ≠ Int.signed j.
Proof.
  intro. contradict H.
  rewrite <- Int.repr_signed with i.
  rewrite <- Int.repr_signed with j.
  congruence.
Qed.

Lemma signed_le_unsigned x :
  Int.signed x <= Int.unsigned x.
Proof.
  unfold Int.signed. bif; auto; intuition.
  pose proof (Int.modulus_pos). intuition.
Qed.

Lemma signed_pos_unsigned {x} :
  0 <= Int.signed x → Int.signed x = Int.unsigned x.
Proof.
  unfold Int.signed. bif.
  intros H. apply False_ind. unfold Int.half_modulus in *.
  pose proof (Int.unsigned_range x). intuition.
Qed.

Lemma mod_sub : ∀ x M, M > 0 →
                       M <= x < M + M - 1 →
                       x mod M = x - M.
Proof.
  intros q M ? ?. rewrite Zmod_eq; auto.
  replace (q / M) with (((q-M) + 1 * M) / M).
  2: f_equal; ring.
  rewrite Z_div_plus; auto.
  rewrite Zdiv_small; intuition.
Qed.

Lemma z_lt_neg_gt x y : - x < - y -> y < x.
Proof. destruct x; destruct y; intuition. Qed.

Lemma z_le_neg_ge x y : - x <= - y -> y <= x.
Proof. destruct x; destruct y; intuition. Qed.

Lemma zdiv_lt : ∀ x y z, z > 0 -> x < 0 <= y -> x / z < y / z.
Proof.
  (* with Psatz
  intros.
  unfold Zdiv.
  elim_div.
  assert (z0 = 0 \/ z0 < 0 \/ z0 > 0) by lia.
  psatz Z.
  *)
  intros x y z H [X Y].
  apply Zlt_le_trans with 0. 2: intuition auto using Z_div_pos.
  apply z_lt_neg_gt. simpl.
  case (zeq (x mod z) 0); intros M.
  pose proof (Z_div_mod_eq x _ H) as U. rewrite M in U.
  set (q := x / z). fold q in U. clear M.
  destruct q. rewrite U in X. omega.
  simpl. assert (x>0). subst.
  destruct z; intuition. intuition.
  simpl. zify. intuition.
  cut (0 <= - (x / z) - 1). intuition.
  rewrite <- Z_div_nz_opp_full; auto. apply Z_div_pos; intuition.
Qed.

Lemma zdiv_mono : ∀ x z : Z, x < -1 → z > 0 → x <= x / z.
Proof.
  (* psatz
  intros. elim_div. psatz Z.
  *)
  intros x z X Z.
  apply z_le_neg_ge.
  case (zeq (x mod z) 0); intros m.
  rewrite <- Z_div_zero_opp_full; auto.
  case (zlt z 2); intros.
    assert (z = 1). omega. subst. intuition.
  cut (-x/z < -x). intuition.
  apply Z_div_lt; intuition.
  cut (-(x/z)-1 < -x). intuition.
  rewrite <- Z_div_nz_opp_full; auto.
  apply Z_div_lt; intuition.
  destruct z as [|z|]; intuition. 2: discriminate.
  destruct z; intuition; zify; try omega.
Qed.

  Lemma ltlt i j :
    Int.min_signed <= i <= Int.max_signed ->
    Int.lt (Int.repr i) j = false ->
    Int.signed j <= i.
  Proof.
    unfold Int.lt. destruct zlt. congruence. intros.
    rewrite Int.signed_repr in *; intuition.
  Qed.

  Lemma ltlt' i j :
    Int.min_signed <= i <= Int.max_signed ->
    Int.lt j (Int.repr i) = false ->
    i <= Int.signed j.
  Proof.
    unfold Int.lt. destruct zlt. congruence. intros.
    rewrite Int.signed_repr in *; intuition.
  Qed.

Require Import Errors.
Require Import String.
Open Scope error_monad_scope.

Definition get_opt {A} (a:option A) (msg:string) : res A :=
  match a with
    | None => Error (MSG msg::nil)
    | Some a => OK a
  end.

Definition ptree_forall_error {A} (f: positive -> A -> res unit) (m: PTree.t A) : res unit :=
  PTree.fold
    (fun (res: res unit) (i: positive) (x: A) => 
      do _ <- res;
      f i x)
    m (OK tt).

Lemma ptree_forall_error_correct:
  forall (A: Type) (f: positive -> A -> res unit) (m: PTree.t A),
    ptree_forall_error f m = OK tt ->
    forall i x, m!i = Some x -> f i x = OK tt.
Proof.
  unfold ptree_forall_error; intros.
  set (f' := fun (r: res unit) (i: positive) (x: A) => do _ <- r; f i x).
  set (P := fun (m: PTree.t A) (r: res unit) =>
              r = OK tt -> m!i = Some x -> f i x = OK tt).
  assert (P m (OK tt)).
  rewrite <- H. fold f'. apply PTree_Properties.fold_rec.
  unfold P; intros. rewrite <- H1 in H4. auto. 
  red; intros. rewrite PTree.gempty in H2. discriminate.
  unfold P; intros. unfold f' in H4. 
  destruct a; inv H4.
  rewrite PTree.gsspec in H5. destruct (peq i k). 
  inv H5. auto.
  destruct u; auto.
  rewrite H3; auto. 
  red in H1. auto. 
Qed.

Definition ptree_mem {A} n (m:PTree.t A) : bool :=
  match PTree.get n m with
    | None => false
    | Some _ => true
  end.

Lemma fold_left_cons_map_app {A B:Type} (f: A -> B) :
  forall (l: list A) (k: list B),
  fold_left (fun acc a => f a :: acc) l k = rev (map f l) ++ k.
Proof.
  refine (rev_ind _ _ _). reflexivity.
  intros. rewrite fold_left_app, map_app, rev_app_distr. simpl. congruence.
Qed.

Lemma flat_map_app {A B: Type} (f: A -> list B) :
  forall l m,
    flat_map f (l ++ m) = flat_map f l ++ flat_map f m.
Proof. induction l. reflexivity. simpl. intros. rewrite <- app_assoc. congruence. Qed.

Lemma aux {A B C:Type} (f: A -> B -> C) :
  forall (l: list A) (m: list B) (k: list C),
  fold_left (fun acc a => rev (map (f a) m) ++ acc) l k =
  rev (flat_map (fun a => map (f a) m) l) ++ k.
Proof.
  refine (rev_ind _ _ _). reflexivity.
  intros a l IH.
  intros m k.
  rewrite fold_left_app, flat_map_app, rev_app_distr, IH.
  simpl. rewrite app_assoc. f_equal.
  now rewrite app_nil_r.
Qed.

Lemma aux' {A B C D: Type} (f: A -> B -> C -> D) :
  forall (l: list A) (m: list B) (n: list C) (k: list D),
  fold_left (fun acc a => rev (flat_map (fun b => map (f a b) n) m) ++ acc) l k =
  rev (flat_map (fun a => flat_map (fun b => map (f a b) n) m) l) ++ k.
Proof.
  refine (rev_ind _ _ _). reflexivity.
  intros x l H m n k.
  rewrite fold_left_app. simpl.
  rewrite H, app_assoc, flat_map_app, rev_app_distr. f_equal.
  simpl. rewrite app_nil_r. auto.
Qed.

Lemma minus_4_lt (p: positive) :
  (Z.to_nat (Zpos p - 4) < Z.to_nat (Zpos p))%nat.
Proof.
  rewrite Z2Nat.inj_pos.
  set (q := Z.pos p - 4).
  assert (q < 0 ∨ q >= 0) as [H|H] by Psatz.lia.
  destruct q. Psatz.lia. Psatz.lia. rewrite Z2Nat.inj_neg. apply Pos2Nat.is_pos.
  case_eq q. intuition. intros p' P. rewrite Z2Nat.inj_pos. subst. Psatz.lia.
  intros p' P. rewrite P in H. Psatz.lia.
Qed.

Lemma case_Zmin : forall (P:Z->Type) x y,
 (x<=y -> P x) -> (y<=x -> P y )-> P (Zmin x y).
Proof.
  unfold Zmin, Zle; intros P x y.
  generalize (Zcompare_antisym x y).
  destruct (x ?= y); intros.
  apply X; discriminate.
  apply X; discriminate.
  apply X0.
  rewrite <- H; discriminate.
Qed.

Lemma case_Zmax : forall (P:Z->Type) x y,
 (y<=x -> P x) -> (x<=y -> P y )-> P (Zmax x y).
Proof.
  unfold Zmax, Zle; intros.
  case_eq (x ?= y); intros.
  apply X; rewrite <- Zcompare_antisym.
  rewrite H; discriminate.
  apply X0; rewrite H; discriminate.
  apply X; rewrite <- Zcompare_antisym.
  rewrite H; discriminate.
Qed.

Lemma Zmult_interval_mid_mid : forall a b c d x y,
  a <= x <= b -> 
  c <= y <= d ->
  a < 0 -> 0 <= b -> c < 0 -> 0 <= d ->
  Zmin (b*c) (a*d) <= x*y <= Zmax (a*c) (b*d).
Proof.
  intuition.
  apply case_Zmin; intros.
  destruct (Zpos_or_not y).
  destruct (Zpos_or_not x).
  apply Zmult_split; auto with zarith sign.
  apply Zle_trans with (a*d); auto.
  apply Zmult_ineq2; apply Zmult_bounds1; intuition.
  destruct (Zpos_or_not x).
  apply Zmult_ineq1; apply Zmult_bounds1; intuition.
  apply Zmult_split; auto with zarith sign.
  destruct (Zpos_or_not y); destruct (Zpos_or_not x).
  apply Zmult_split; auto with zarith sign.
  apply Zmult_ineq2; apply Zmult_bounds1; intuition.
  apply Zle_trans with (b*c); auto.
  apply Zmult_ineq1; apply Zmult_bounds1; intuition.
  apply Zmult_split; auto with zarith sign.
  apply case_Zmax; intros.
  destruct (Zpos_or_not y); destruct (Zpos_or_not x).
  apply Zle_trans with (b*d); auto.
  apply Zmult_bounds1; intuition.
  apply Zmult_split; auto with zarith sign.
  apply Zmult_split; auto with zarith sign.
  apply Zmult_ineq2; apply Zmult_ineq1; intuition.
  destruct (Zpos_or_not y); destruct (Zpos_or_not x).
  apply Zmult_bounds1; intuition.
  apply Zmult_split; auto with zarith sign.
  apply Zmult_split; auto with zarith sign.
  apply Zle_trans with (a*c); auto.
  apply Zmult_ineq2; apply Zmult_ineq1; intuition.
Qed.

Lemma Mult_interval_correct_min_max : forall a b c d x y : Z,
  a <= x <= b ->
  c <= y <= d ->
  Zmin (Zmin (a*c) (b*d)) (Zmin (b*c) (a*d)) <= x * y 
      <= Zmax (Zmax (a*c) (b*d)) (Zmax (b*c) (a*d)).
Proof.
  intros.
  destruct (Zpos_or_not a).
  destruct (Zpos_or_not c).
  apply ineq_trans with (a*c) (b*d); auto.
  apply Zmult_interval_right_right; auto with zarith.  
  destruct (Zpos_or_not d).
  apply ineq_trans with (b*c) (b*d); auto.
  apply Zmult_interval_right_mid with a; auto with zarith.
  apply ineq_trans with (b*c) (a*d); auto.
  apply Zmult_interval_right_left; auto with zarith.  
  destruct (Zpos_or_not b); destruct (Zpos_or_not c).
  apply ineq_trans with (a*d) (b*d); auto.
  rewrite (Zmult_comm a d); rewrite (Zmult_comm x y); rewrite (Zmult_comm b d).
  apply Zmult_interval_right_mid with c; auto with zarith.  
  destruct (Zpos_or_not d).
  apply ineq_trans with (Zmin (b*c) (a*d)) (Zmax (a*c) (b*d)); auto.
  apply Zmult_interval_mid_mid; auto with zarith.
  apply ineq_trans with (b*c) (a*c); auto.
  rewrite (Zmult_comm a c); rewrite (Zmult_comm x y); rewrite (Zmult_comm b c).
  apply Zmult_interval_left_mid with d; auto with zarith.  
  apply ineq_trans with (a*d) (b*c); auto.
  rewrite (Zmult_comm b c); rewrite (Zmult_comm x y); rewrite (Zmult_comm a d).
  apply Zmult_interval_right_left; auto with zarith.  
  destruct (Zpos_or_not d).
  apply ineq_trans with (a*d) (a*c); auto.
  apply Zmult_interval_left_mid with b; auto with zarith.  
  apply ineq_trans with (b*d) (a*c); auto.
  apply Zmult_interval_left_left; auto with zarith.  
Qed.
