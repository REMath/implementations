(*---------------------------------------------------------------------------
    Various helpers for halving, double and powers of 2
  ---------------------------------------------------------------------------*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype div.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma half_ltn_double m n : m < n.*2 -> m./2 < n.
Proof. move => H. 
rewrite -ltn_double. rewrite -(odd_double_half m) in H. 
rewrite -(ltn_add2l (odd m)). 
by apply ltn_addl. 
Qed. 

Lemma half_double_subn1 a : ((a.*2).-1)./2 = a.-1.
Proof. case a. done. move => a'. simpl; apply uphalf_double. Qed.

Lemma uphalf_double_subn1 a : uphalf ((a.*2).-1) = a.
Proof. case a. done. move => a'. simpl; by rewrite half_double. Qed.

Lemma half_subn1 : forall a b, (b - a.+1)./2 = (uphalf (b - a)).-1.
Proof. induction a.
+ case => //. move => b. by rewrite subn1. 
+ move => b. specialize (IHa (b.-1)). 
rewrite -subn1 in IHa. by rewrite -!subnDA !add1n in IHa. 
Qed. 

(* Strictly speaking we don't need the precondition *)
Lemma half_sub a : forall b, a <= b.*2 -> (b.*2 - a)./2 = b - uphalf a.
Proof. 
induction a => b H.
+ by rewrite !subn0 doubleK. 
+ rewrite half_subn1. rewrite uphalf_half. rewrite IHa. 
  rewrite odd_sub. rewrite odd_double/=. rewrite -subn1. 
  rewrite uphalf_half. 
case ODD: (odd a). 
  by rewrite add1n subn1. 
  by rewrite !add0n/= -subnDA addn1.
apply (ltnW H). apply (ltnW H).  
Qed. 

Lemma odd_oddsubn1 : forall n, n > 0 -> odd n.-1 = ~~odd n. 
Proof. induction n => //. destruct n => //. simpl. by case (odd n). Qed. 

Lemma odd_power2 n : odd (2^(n.+1)) = false.
Proof. by rewrite expnS mul2n odd_double. Qed.

Lemma odd_power2subn1 n : odd ((2^(n.+1)).-1) = true.
Proof. induction n => //.
rewrite expnS mul2n odd_oddsubn1. 
by rewrite odd_double. 
rewrite -mul2n -expnS. apply expn_gt0.  
Qed. 

Lemma leq_subn a b : 0 < b -> a < b -> a <= b.-1. 
Proof. by case b. Qed. 

Lemma pow2_gt1 n : 1 < 2^n.+1.
Proof. rewrite expnS. 
suff: 2*1 <= 2*2^n => //.  
rewrite leq_mul2l/=.  
apply expn_gt0. 
Qed. 

Lemma nat_lt0_succ m : (0 < m) = true -> exists m', m = m'+1. 
Proof. destruct m => //. move => _. exists m. by rewrite addn1. 
Qed. 

Lemma pow2_sub_ltn n x : (2^n)-(x.+1) < 2^n. 
Proof. have H := expn_gt0 2 n. simpl in H. 
destruct (nat_lt0_succ H) as [m' HH]. rewrite HH. 
rewrite addn1 subSS. by rewrite ltnS leq_subr. 
Qed. 

Lemma modn_sub : forall N x y, 0 < N -> x < N -> y < N -> N <= x+y -> 
   (x + y) %% N + N = x+y.
Proof. 
move => N x y B H1 H2 H3.
assert (H4:= divn_eq (x+y) N). 
rewrite {2}H4.
rewrite addnC. 
assert (LT:(x + y) %/ N < 2). 
rewrite ltn_divLR. rewrite mul2n -addnn. 
rewrite -(ltn_add2r y) in H1. 
apply (ltn_trans H1). 
by rewrite ltn_add2l. 
done. 
assert (GT:0 < (x + y) %/ N). 
by rewrite divn_gt0. rewrite ltnS in LT. 
assert (1 <= (x+y) %/ N <= 1). by rewrite GT LT. 
rewrite -eqn_leq in H. rewrite -(eqP H). 
by rewrite mul1n. 
Qed.

