Require Import Znumtheory.
Require Import ZArith.
Require Import Setoid.
Require Import Ring.
Require Import Omega.

Local Open Scope Z_scope.

Definition Z_zerop (z:Z) : { z = 0 } + { z <> 0 }.
  refine (match z with
            | Z0 => left _ _
            | _ => right _ _
          end); abstract congruence.
Defined.

Lemma div_0_is_0 : forall {a}, (0|a) -> a = 0.
Proof.
  intros a [q Hq].
  rewrite Hq.
  ring.
Qed.

Lemma plus_div_2 : forall z, ( z + z ) / 2 = z.
Proof.
intros.
assert (z + z = z * 2) as H;[|rewrite H].
auto with zarith.
apply Z_div_mult.
intuition.
Qed.

Section Congruence.

Definition congrS n x y := { q : Z | y = x + q * n }.
Definition congr n x y : Prop :=
  exists q, y = x + q * n.

Lemma congr_refl : forall n x, congr n x x.
Proof. intros n x; exists 0; auto with zarith. Qed.

Lemma congr_sym : forall n x y, congr n x y -> congr n y x.
Proof.
  intros n x y [q Hq]. exists (-q); rewrite Hq.
  ring.
Qed.

Lemma congr_trans n : transitive _ (congr n).
Proof.
  intros x y z [q Hq] [r Hr].
  exists (q + r).
  rewrite Hr; rewrite Hq.
  rewrite Zmult_plus_distr_l.
  rewrite Zplus_assoc.
  reflexivity.
Qed.

Lemma congr_0_eq : forall x y, congr 0 x y -> x = y.
Proof.
  intros x y [q Hq]; rewrite Hq.
  simpl.
  auto with zarith.
Qed.

Lemma congr_1 : forall x y, congr 1 x y.
Proof.
  intros x y; exists (y - x). simpl.
  omega.
Qed.

Lemma congr_divide : forall n m x y,
  congr n x y -> (m | n) ->
    congr m x y.
Proof.
  intros n m x y [kn Hn] [km Hm].
  exists (kn * km).
  rewrite Hn; rewrite Hm.
  auto with zarith.
Qed.

Lemma congr_plus_compat_l : forall n x y m,
  congr n x y ->
  congr n (x + m) (y + m).
Proof.
  intros n x y m [q Hq].
  exists q.
  rewrite Hq.
  ring.
Qed.

Lemma congr_minus_compat_l : forall n x y m,
  congr n x y ->
  congr n (x - m) (y - m).
Proof.
  intros n x y m [q Hq].
  exists q.
  rewrite Hq.
  ring.
Qed.

Lemma congr_minus_compat n x y z t :
  congr n x y ->
  congr n z t ->
  congr n (x - z) (y - t).
Proof.
  intros [a ->] [b ->].
  exists (a - b). ring.
Qed.

Lemma congr_neg_compat n x y :
  congr n x y ->
  congr n (-x) (-y).
Proof.
  intros [q ->].
  exists (-q). ring.
Qed.

Lemma congr_plus_compat : forall n x y z t,
  congr n x y -> congr n z t ->
  congr n (x + z) (y + t).
Proof.
  intros n x y z t [a Ha] [b Hb].
  exists (a + b).
  rewrite Ha. rewrite Hb.
  ring.
Qed.

Lemma congr_diff : forall a b,
  congr (a - b) a b.
Proof.
  intros a b.
  destruct (Z_eq_dec a b).
  subst; apply congr_refl.
  exists (-1); auto with zarith.
Qed.

Lemma congr_mod_compat : forall n x, n > 0 ->
  congr n x (x mod n).
Proof.
intros n x H.
rewrite (Zmod_eq _ _ H).
exists (- (x / n)).
unfold Zminus.
rewrite Zopp_mult_distr_l.
reflexivity.
Qed.

Lemma congr_eqm : forall n x y, n > 0 ->
  congr n x y -> eqm n x y.
Proof.
  intros n x y POS (q & ->).
  symmetry. apply Z_mod_plus. auto.
Qed.

Lemma eqm_congr : forall n x y, n > 0 ->
  eqm n x y -> congr n x y.
Proof.
  intros n x y POS EQM. unfold eqm in *.
  exists (y / n - x / n).
  replace (x + (y / n  - x / n) * n) with (y / n * n + (x - x / n * n)) by ring.
  assert (n <> 0) by intuition.
  rewrite <- Zmod_eq_full; auto.
  rewrite EQM.
  rewrite Zmod_eq_full; auto.
  ring.
Qed.

Lemma congr_mult_l_compat :
  forall n p x y,
    congr n x y ->
    congr (p * n) (p * x) (p * y).
Proof.
  intros n p x y (q & ->). exists q. ring.
Qed.

Lemma congr_opp n x y :
  congr n x y ->
  congr n (-x) (-y).
Proof.
  intros (q & H).
  exists (-q). subst. ring.
Qed.

Definition congr_dec n x y :
  {congr n x y} + {~congr n x y}.
refine (
    match Z_zerop n with
    | left NZ =>
      match Z.eq_dec x y with
      | left EQ => left (ex_intro _ 0 _)
      | right NE => right _
      end
    | right NNZ =>
      match Z_zerop ((y - x) mod n) with
      | left H => left (ex_intro _ ((y - x) / n) _)
      | right H => right _
      end
    end).
Proof.
  abstract intuition.
  abstract (exact (fun K => NE (congr_0_eq x y (eq_ind n (fun u => congr u x y) K 0 NZ)))).
  abstract (rewrite Zmult_comm, <- (Z_div_exact_full_2 _ _ NNZ H); auto with zarith).
  abstract (
  intros (q,->); apply H;
  unfold Zminus;
  rewrite Zplus_comm, Zplus_assoc, Zplus_opp_l, Zplus_0_l;
  apply Zdivide_mod;
  exists q; reflexivity).
Defined.

Definition congrS_dec {n} {x} {y} (H :congr n x y) : congrS n x y.
  refine (match Z_zerop n with
            | left H =>
              if Z_eq_dec x y
              then exist _ 0 _
              else False_rec _ _ 
            | right H => exist _ ((y - x) / n) _
          end).
Proof.
  subst. ring.
  subst. pose proof (congr_0_eq x y). intuition.
  destruct H as [q Hq].
  rewrite Hq.
  assert (x + q * n - x = q * n) as K. ring.
  rewrite K.
  rewrite Z_div_mult_full.
  ring.
  assumption.
Defined.

End Congruence.

Hint Resolve congr_refl congr_trans congr_sym congr_0_eq congr_1 : congr.

Notation "x ≡ y [ n ]" := (congr n x y) (at level 80).

Section ggT.

Variables a b : Z.
Hypothesis a_pos : 0 <= a.
Hypothesis b_pos : 0 <= b.

Inductive Eucl : Set :=
| Eucl_intro : forall (u v d:Z) (Hbez:u * a + v * b = d)
    (Hpos: 0 <= d)
    (Hgcd: Zis_gcd a b d), Eucl.

  (** The recursive part of Euclid's algorithm uses well-founded
      recursion of non-negative integers. It maintains 6 integers
      [u1,u2,u3,v1,v2,v3] such that the following invariant holds:
      [u1*a+u2*b=u3] and [v1*a+v2*b=v3] and [gcd(u2,v3)=gcd(a,b)].
      *)

  Lemma eucl_rec :
    forall (v3:Z) (Hv3: 0 <= v3)
      (u3 : Z),
      0 <= u3 ->
      forall u1 u2 v1 v2:Z,
	u1 * a + u2 * b = u3 ->
	v1 * a + v2 * b = v3 ->
	(forall d:Z, Zis_gcd u3 v3 d -> Zis_gcd a b d) -> Eucl.
  Proof.
    intros v3 Hv3; generalize Hv3; pattern v3 in |- *.
    apply Zlt_0_rec.
    clear v3 Hv3; intros.
    elim (Z_zerop x); intro.
    apply Eucl_intro with (u := u1) (v := u2) (d := u3).
    assumption.
    assumption.
    apply H4.
    rewrite a0; auto with zarith.
    set (q := u3 / x) in *.
    assert (Hq : 0 <= u3 - q * x < x).
    replace (u3 - q * x) with (u3 mod x).
    apply Z_mod_lt; omega.
    assert (xpos : x > 0). omega.
    generalize (Z_div_mod_eq u3 x xpos).
    unfold q in |- *.
    intro eq; pattern u3 at 2 in |- *; rewrite eq; ring.
    apply (H (u3 - q * x) Hq (proj1 Hq) x H0 v1 v2 (u1 - q * v1) (u2 - q * v2)).
    tauto.
    replace ((u1 - q * v1) * a + (u2 - q * v2) * b) with
      (u1 * a + u2 * b - q * (v1 * a + v2 * b)).
    rewrite H2; rewrite H3; trivial.
    ring.
    intros; apply H4.
    apply Zis_gcd_for_euclid with q; assumption.
    assumption.
  Defined.

  (** We get Euclid's algorithm by applying [euclid_rec] on
      [1,0,a,0,1,b] when [b>=0] and [1,0,a,0,-1,-b] when [b<0]. *)

  Lemma eucl : Eucl.
  Proof.
    apply eucl_rec with
      (u1 := 1) (u2 := 0) (u3 := a)
      (v1 := 0) (v2 := 1) (v3 := b).
    apply b_pos.
    apply a_pos.
    ring.
    ring.
    intros; assumption.
  Defined.

Definition ggT := match eucl with
Eucl_intro _ _ g _ _ _ => g
end.

Lemma ggT_pos : 0 <= ggT.
Proof.
  unfold ggT; destruct eucl.
  assumption.
Qed.

Lemma ggT_is_Zgcd : ggT = Zgcd a b.
Proof.
  unfold ggT; destruct eucl.
  destruct (Zis_gcd_unique a b d (Zgcd a b)) as [H|H].
        assumption.
      apply Zgcd_is_gcd.
    assumption.
  rewrite H in Hpos.
  pose proof (Zgcd_is_pos a b) as K.
  assert (Zgcd a b <= 0) as U.
    auto with zarith.
  rewrite (Zle_antisym _ _ U K) in *.
  auto.
Qed.

End ggT.

Section on_gcd.

Variables a b : Z.

Lemma Zgcd_divides_l : (Zgcd a b | a).
Proof.
  destruct (Zgcd_is_gcd a b).
  assumption.
Qed.

Lemma Zgcd_divides_r : (Zgcd a b | b).
Proof.
  destruct (Zgcd_is_gcd a b).
  assumption.
Qed.

Lemma Zis_gcd_0_inv_l : Zis_gcd a b 0 -> a = 0.
Proof.
  intros H; induction H as [[q Hq] _ _].
  intuition.
Qed.

Lemma Zis_gcd_0_inv_r : Zis_gcd a b 0 -> b = 0.
Proof.
  intros H; induction H as [_ [q Hq] _].
  intuition.
Qed.

End on_gcd.

Section RemEqn.

Variables a b ma mb : Z.
Hypothesis Hma : 0 <= ma.
Hypothesis Hmb : 0 <= mb.

Definition rem_eqn_spec n := congr ma a n /\ congr mb b n.

Lemma rem_eqn_nes n : rem_eqn_spec n ->
  congr (Zgcd ma mb) a b.
Proof.
  intros [[qa Ha] [qb Hb]].
  edestruct Z.gcd_divide_l with ma mb as [ma' Hma'].
  edestruct Z.gcd_divide_r with ma mb as [mb' Hmb'].
  exists (qa * ma' - qb * mb').
  rewrite Hma' in Ha.
  rewrite Hmb' in Hb.
  rewrite Zmult_minus_distr_r.
  unfold Zminus.
  rewrite Zplus_assoc.
  rewrite Zmult_assoc in Ha.
  rewrite <- Ha.
  rewrite Hb.
  ring.
Qed.

Definition rem_eqn_particular : congr (Zgcd ma mb) a b ->
  { n : Z | rem_eqn_spec n}.
Proof.
  intros H; destruct (congrS_dec H) as [q Hq].
  destruct (eucl ma mb Hma Hmb).
  rewrite (Zis_gcd_gcd _ _ _ Hpos Hgcd) in *.
  exists (ma * u * q + a).
  split.
    exists (u * q); ring.
  exists (- v * q).
  rewrite Hq.
  rewrite <- Hbez.
  ring.
Defined.

Lemma rem_eqn_other_solution' :
 forall (H : congr (Zgcd ma mb) a b),
 let (n, _) := rem_eqn_particular H in
 forall k, rem_eqn_spec (n + k * Z.lcm ma mb).
Proof.
  intros H;
  destruct (rem_eqn_particular H) as [n [Ha Hb]].
  intros k; split.
    rewrite <- (Zplus_0_r a).
    apply congr_plus_compat.
      assumption.
    destruct (Z.divide_lcm_l ma mb) as [l Hl].
    rewrite Hl.
    exists (k * l); ring.
  rewrite <- (Zplus_0_r b).
  apply congr_plus_compat.
    assumption.
  destruct (Z.divide_lcm_r ma mb) as [l Hl].
  rewrite Hl.
  exists (k * l); ring.
Qed.

Lemma rem_eqn_other_solution :
 forall {n} k, rem_eqn_spec (n + k * Z.lcm ma mb) ->
 rem_eqn_spec n.
Proof.
  destruct (Z.divide_lcm_l ma mb) as [ma' Hma'];
  destruct (Z.divide_lcm_r ma mb) as [mb' Hmb'].
  intros n k [Hna Hnb].
  split.
    destruct Hna as [q Hq].
    exists (q - k * ma').
    ring_simplify.
    rewrite <- Hq.
    rewrite Hma'.
    ring.
  destruct Hnb as [q Hq].
  exists (q - k * mb').
  ring_simplify.
  rewrite <- Hq.
  rewrite Hmb'.
  ring.
Qed.

Lemma rem_eqn_other_solution_congr :
 forall {n m}, n ≡ m [Z.lcm ma mb] ->
 rem_eqn_spec m ->
 rem_eqn_spec n.
Proof.
  intros n m [q Hq].
  rewrite Hq.
  apply rem_eqn_other_solution.
Qed.

Lemma rem_eqn_all_solutions' :
  forall N (Hsol: rem_eqn_spec N),
  let H := rem_eqn_nes N Hsol in
  let (n, _) := rem_eqn_particular H in
    N ≡ n [Z.lcm ma mb].
Proof.
  intros N Hsol H;
  destruct (rem_eqn_particular H) as [n [[ra Ha] [rb Hb]]].
  destruct Hsol as [Hsa Hsb].
  assert ((ma|n-N) /\ (mb|n-N)) as Hdiv. split.
    destruct Hsa as [q Hq].
    rewrite Hq; rewrite Ha.
    exists (ra - q); ring.
    destruct Hsb as [q Hq].
    rewrite Hq; rewrite Hb.
    exists (rb - q); ring.
  apply Z.lcm_divide_iff in Hdiv.
  destruct Hdiv as [q Hq].
  exists q; rewrite <- Hq; ring.
Qed.

Lemma rem_eqn_all_solutions :
  forall N n, rem_eqn_spec N -> rem_eqn_spec n ->
    N ≡ n [Z.lcm ma mb].
Proof.
  intros N n HN Hn.
  pose (rem_eqn_nes N HN) as H.
  destruct (rem_eqn_particular H) as [x [[ra Ha] [rb Hb]]].
  destruct HN as [HNa HNb].
  destruct Hn as [Hna Hnb].
  assert ((ma|x-N) /\ (mb|x-N)) as HdivN. split.
    destruct HNa as [q Hq].
    rewrite Hq; rewrite Ha.
    exists (ra - q); ring.
    destruct HNb as [q Hq].
    rewrite Hq; rewrite Hb.
    exists (rb - q); ring.
  assert ((ma|n-x) /\ (mb|n-x)) as Hdivn. split.
    destruct Hna as [q Hq].
    rewrite Hq; rewrite Ha.
    exists (q - ra); ring.
    destruct Hnb as [q Hq].
    rewrite Hq; rewrite Hb.
    exists (q - rb); ring.
  apply Z.lcm_divide_iff in HdivN.
  apply Z.lcm_divide_iff in Hdivn.
  destruct HdivN as [q Hq].
  destruct Hdivn as [r Hr].
  exists (q + r).
  rewrite Zmult_plus_distr_l.
  rewrite <- Hq; rewrite <- Hr.
  ring.
Qed.

Lemma rem_eqn_0_l : forall {n},
   ma = 0 -> rem_eqn_spec n -> n = a.
Proof.
  intros n Hmaz [Hna Hnb].
  destruct Hna as [q Hq].
  rewrite Hq; rewrite Hmaz.
  intuition.
Qed.

Definition smallest_larger_than (m: Z) (P : Z -> Prop) (n: Z) : Prop :=
  P n /\ m <= n /\ forall q, P q -> m <= q -> n <= q.

Lemma smallest_larger_than_unique m P n n' :
  smallest_larger_than m P n ->
  smallest_larger_than m P n' ->
  n = n'.
Proof.
  intros (A & B & C) (D & E & F).
  apply Zle_antisym; auto.
Qed.

Definition largest_smaller_than (m: Z) (P : Z -> Prop) (n: Z) : Prop :=
  P n /\ n <= m /\ forall q, P q -> q <= m -> q <= n.

Lemma largest_smaller_than_unique m P n n' :
  largest_smaller_than m P n ->
  largest_smaller_than m P n' ->
  n = n'.
Proof.
  intros (A & B & C) (D & E & F).
  apply Zle_antisym; auto.
Qed.

Lemma smallest_solution_larger_than' A :
  Z.lcm ma mb > 0 ->
  forall q n,
    rem_eqn_spec q ->
    rem_eqn_spec (A + (n - A) mod Z.lcm ma mb) ->
    A <= q ->
    A + (n - A) mod Z.lcm ma mb <= q.
Proof.
  set (s := Z.lcm ma mb). intros Hs q n Q L AQ.
  pose proof (rem_eqn_all_solutions _ q L Q) as (x & ->).
  assert (A + (n - A) mod s < A + s).
    apply Zplus_le_lt_compat.
      apply Zle_refl.
    apply Z_mod_lt; auto.
  destruct (Z_le_gt_dec 0 x).
    rewrite <- (Zplus_0_r ) at 1. subst s.
    apply Zplus_le_compat;
    auto with zarith.
  absurd (A + (n - A) mod s + x * Z.lcm ma mb < A). intuition.
  apply Zle_lt_trans with (A + (n - A) mod s - s);
    [apply Zplus_le_compat|];
  auto with zarith.
  rewrite Zopp_eq_mult_neg_1.
  rewrite Zmult_comm.
  apply Zmult_le_compat_l; intuition.
Qed.

Lemma smallest_solution_larger_than H A :
  Z.lcm ma mb > 0 ->
  smallest_larger_than A rem_eqn_spec (A + (proj1_sig (rem_eqn_particular H) - A) mod Z.lcm ma mb).
Proof.
  set (s := Z.lcm ma mb).
  intros Hs.
  destruct rem_eqn_particular as (n & N). simpl.
  assert (rem_eqn_spec (A + (n - A) mod s)) as HA.
  eapply (@rem_eqn_other_solution_congr); eauto.
  set (r := (n-A) mod s).
  set (p := (n - A) / s).
  assert (r = (n - A) - s * p) as Hr.
    rewrite (Z_div_mod_eq_full (n - A) s).
    unfold r, p; ring.
  intuition.
  rewrite Hr.
  exists p. subst s. ring.
  split. apply HA.
  split. rewrite <- (Zplus_0_r A) at 1. apply Zplus_le_compat. auto with zarith.
  apply Z_mod_lt; auto.
  intros. subst s. apply smallest_solution_larger_than'; auto.
Qed.

Lemma largest_solution_smaller_than H B :
  Z.lcm ma mb > 0 ->
  largest_smaller_than B rem_eqn_spec (B - (B - proj1_sig (rem_eqn_particular H)) mod Z.lcm ma mb).
Proof.
  set (s := Z.lcm ma mb).
  intros Hs.
  destruct rem_eqn_particular as (n & N). simpl.
  assert (rem_eqn_spec (B - (B - n) mod s)) as HB.
  eapply (@rem_eqn_other_solution_congr); eauto.
  set (r := (B - n) mod s).
  set (p := (B - n) / s).
  assert (r = (B - n) - s * p) as Hr.
    rewrite (Z_div_mod_eq_full (B - n) s).
    unfold r, p; ring.
  intuition.
  rewrite Hr.
  exists (-p). subst s. ring.
  split. apply HB.
  split. rewrite <- (Zplus_0_r B) at 3. apply Zplus_le_compat. auto with zarith.
  pose proof (Z_mod_lt (B-n) s Hs). intuition.
  intros q Q QB.
  pose proof (rem_eqn_all_solutions _ q HB Q) as (x & ->).
  assert (B - s < B - (B - n) mod s).
    apply Zplus_le_lt_compat.
      apply Zle_refl.
      pose proof (Z_mod_lt (B-n) _ Hs). intuition.
  destruct (Z_lt_ge_dec 0 x).
  absurd (B < B - (B - n) mod s + x * Z.lcm ma mb). intuition.
  apply Zlt_le_trans with (B - (B - n) mod s + s); auto with zarith.
  unfold Zminus. apply Zplus_le_compat; auto with zarith.
    rewrite <- Zmult_1_l at 1.
  apply Zmult_le_compat_r; intuition. apply Z.lcm_nonneg; apply lcm_pos.
  rewrite <- (Zplus_0_r ).
  apply Zplus_le_compat.
    auto with zarith.
  rewrite <- (Zmult_0_l s). auto with zarith.
Qed.

End RemEqn.

Require Import Utf8.
Require Psatz.

Lemma le_congr i j s :
  i < j →
  i ≡ j [Zpos s] →
  i <= j - Zpos s.
Proof.
  clear.
  intros LT (q,->).
  assert (q < 0 ∨ q = 0 ∨ q > 0) by Psatz.lia.
  Psatz.nia.
Qed.

Definition Nabs_diff (x y: Z) := N_of_Z (Zmax (x - y) (y - x)).
Lemma Nabs_diff_case x y :
  x <= y ∧ Nabs_diff x y = N_of_Z (y - x) ∨
  y <= x ∧ Nabs_diff x y = N_of_Z (x - y).
Proof.
  unfold Nabs_diff. apply Zmax_case_strong; intuition.
Qed.

Definition Zdivides_dec (a b: Z) : { (a | b) } + { ¬ (a | b) }.
  refine (let q : Z := b / a in
          let r : Z := b - q * a in
          match Z_zerop r with
            | left H => left _
            | right H => right _
          end).
Proof.
  exists q. subst r q. omega.
  subst r q. intros (q & K). elim H. rewrite K. clear K.
  destruct (Z_zerop a). now subst; rewrite Zmult_comm.
  replace (q * a / a) with q. ring.
  rewrite Z_div_mult_full; intuition.
Defined.

Local Coercion Z_of_N : N >-> Z.
Definition Ndivides_dec (a b: N) : { (a | b) } + { ¬ (a | b) }.
  refine (let q : N := N.div b a in
          match N.eq_dec b (q * a) with
          | left H => left _
          | right H => right _
          end).
Proof.
  abstract (exists q; subst q; zify; Psatz.lia).
  abstract (
  subst q; intros (q & K); elim H; zify; rewrite N2Z.inj_div in *;
  rewrite K; clear K;
  destruct a as [|a];
  [repeat (rewrite Zmult_comm; simpl); reflexivity|
  rewrite Z_div_mult_full; intuition; easy]).
Defined.

Remark Ngcd_is_Zgcd (x y: N) : (N.gcd x y:Z) = Zgcd x y.
Proof. destruct x, y; reflexivity. Qed.

Remark Nlcm_is_Zlcm (x y: N) : (N.lcm x y:Z) = Z.lcm x y.
Proof.
  unfold N.lcm, Z.lcm. 
  rewrite <- Ngcd_is_Zgcd, <- N2Z.inj_div, <- N2Z.inj_mul.
  zify. omega.
Qed.

Lemma N_of_pos (x: Z) : 0 <= x → (N_of_Z x : Z) = x.
Proof. destruct x; auto. simpl. Psatz.lia. Qed.

