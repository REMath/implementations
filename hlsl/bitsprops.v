(*===========================================================================
  Properties of bit vectors
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple fintype div zmodp ssralg.
Require Import ZArith.
Require Import tuplehelp bitsrep nathelp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma trivialBits (p q: BITS 0) : p = q. 
Proof. by rewrite (tuple0 p) (tuple0 q). Qed.


(*---------------------------------------------------------------------------
    Properties of conversion to and from natural numbers.
  ---------------------------------------------------------------------------*)
Lemma toNatCons n b (p:BITS n) : toNat (consB b p) = b + (toNat p).*2.
Proof. done. Qed.

Lemma toNatNil (p:BITS 0) : toNat p = 0. 
Proof. by rewrite (tuple0 p). Qed.

(* toNat is left-inverse to fromNat *)
Lemma toNatK n : cancel (@toNat n) (@fromNat n). 
Proof. induction n; first (move => p; apply trivialBits). 
+ case/tupleP => b x. rewrite toNatCons /= half_bit_double IHn odd_add odd_double. by case b.  
Qed. 

(* Hence toNat is injective *)
Definition toNat_inj n := can_inj (@toNatK n).

(* toNat result is bounded *)
Lemma toNatBounded n : forall (p: BITS n), toNat p < 2^n. 
Proof. induction n. move => p. by rewrite toNatNil. 
case/tupleP => [b p]. 
rewrite expnS mul2n toNatCons.
case b.
+ rewrite ltn_Sdouble. apply IHn.
+ rewrite ltn_double. apply IHn. 
Qed. 

Lemma toNat_fromNatBounded n : forall m, m < 2^n -> toNat (fromNat (n:=n) m) = m. 
Proof. induction n. 
+ rewrite expn0. by case. 
+ rewrite expnS. move => m.  specialize (IHn m./2). 
  move => LT. 
  assert (m./2 < 2^n). 
  rewrite -ltn_double. rewrite -(odd_double_half m) mul2n in LT. 
  rewrite -(ltn_add2l (odd m)). 
  by apply ltn_addl. 
  specialize (IHn H). 
  rewrite /toNat-/toNat/=. 
  rewrite /toNat/= in IHn. rewrite IHn. 
  by rewrite odd_double_half. 
Qed. 

Lemma fromNatHalf n : forall m, cons_tuple (odd m) (fromNat (n:=n) (m./2)) = fromNat m.
Proof. done. Qed.
 

Lemma fromNat_wrap n : forall m, fromNat (n:=n) m = fromNat (n:=n) (m + 2^n). 
Proof. induction n => //.
rewrite expnS. 
move => m. 
case ODD: (odd m); rewrite /=ODD odd_add odd_mul/=ODD/= half_add ODD/=.
specialize (IHn m./2). by rewrite odd_mul/= add0n mul2n doubleK IHn. 
specialize (IHn m./2). by rewrite add0n mul2n doubleK IHn. 
Qed. 

Lemma fromNat_wrapMany n c : forall m, fromNat (n:=n) m = fromNat (n:=n) (m + c * 2^n). 
Proof. induction c => m. by rewrite mul0n addn0. 
rewrite mulSn (addnC (2^n)) addnA fromNat_wrap. rewrite IHc.
by rewrite -addnA (addnC (2^n)) addnA. 
Qed. 

Lemma toNat_mod n p: @toNat n p = toNat p %% 2^n. 
Proof. rewrite modn_small => //. apply toNatBounded. Qed.

Lemma toNat_fromNat n m : @toNat n #m = m %% 2^n. 
Proof. have H:= divn_eq m (2^n). rewrite {1}H. 
have HH:= @fromNat_wrapMany n (m %/ 2^n) (m %% 2^n). rewrite addnC in HH. rewrite -HH. 
rewrite toNat_fromNatBounded. done. apply ltn_pmod. apply expn_gt0. Qed. 

Lemma fromNat_succn n : forall b c, @fromNat n b = #c -> @fromNat n (b.+1) = #(c.+1). 
Proof. induction n => //. 
move => b c EQ. rewrite /fromNat-/fromNat. rewrite /fromNat-/fromNat in EQ.
destruct (splitTuple EQ) as [EQ1 EQ2]. simpl in EQ1. simpl in EQ2. 
specialize (IHn _ _ EQ2). rewrite/= !uphalf_half /=EQ1.
case ODD: (odd c). + by rewrite !add1n IHn. + by rewrite !add0n EQ2. 
Qed. 

Lemma fromNat_addn n : forall a b c, @fromNat n b = #c -> @fromNat n (a+b) = #(a+c). 
Proof. induction a => //.
move => b c EQ. rewrite -addn1 -!addnA !add1n. apply IHa. by apply fromNat_succn. 
Qed. 

Lemma toZp_fromNat n m : toZp (fromNat (n:=n.+1) m) = (m%:R)%R.
Proof. apply val_inj. 
rewrite /toZp toNat_fromNat Zp_nat. rewrite /=Zp_cast; last apply pow2_gt1. 
by rewrite modn_mod. 
Qed. 

Lemma toNat_droplsb n (p: BITS n.+1) : toNat (droplsb p) = (toNat p)./2.
Proof. case/tupleP: p => [b p]. rewrite /droplsb/splitlsb beheadCons theadCons.  
rewrite toNatCons. simpl. by rewrite half_bit_double. 
Qed.

(*---------------------------------------------------------------------------
    Properties of conversion to and from 'Z_(2^n)
  ---------------------------------------------------------------------------*)

(* This only holds for n.+1 because 'Z_1 actually has two elements - it's 
   definitionally the same as 'Z_2 in order to force a ring structure. See zmodp
   for more details *)
Lemma fromZpK n : cancel (@fromZp n.+1) (@toZp n.+1). 
Proof. 
  move => x. rewrite /toZp/fromZp. rewrite  toNat_fromNat modn_small. apply valZpK.
  destruct x. simpl. rewrite Zp_cast in i => //.
  apply pow2_gt1.
Qed. 
 
Lemma toZpK n : cancel (@toZp n) (@fromZp n).  
Proof. case E: (n == 0). 
+ rewrite /cancel. rewrite (eqP E). move => x. apply trivialBits. 
+ move => x. rewrite /fromZp/toZp/=.  
  rewrite Zp_cast. by rewrite (modn_small (toNatBounded _)) toNatK. 
  apply negbT in E. destruct n => //. apply pow2_gt1. 
Qed. 

Lemma toZp_inj n : injective (@toZp n). 
Proof. apply (can_inj (@toZpK _)). Qed.

Lemma fromZp_inj n : injective (@fromZp n.+1).
Proof. apply (can_inj (@fromZpK _)). Qed. 

Lemma toZp_eq n (x y: BITS n) : (x == y) = (toZp x == toZp y). 
Proof. destruct n. by rewrite (tuple0 x) (tuple0 y).
case E: (toZp x == toZp y).
rewrite (toZp_inj (eqP E)). by rewrite eq_refl. 
apply (contraFF (b:=false)) => // => H. 
rewrite (eqP H) (eq_refl) in E. done. 
Qed. 

(*---------------------------------------------------------------------------
    Properties of bit get and set
  ---------------------------------------------------------------------------*)

Lemma setBitThenGetSame n : forall (p: BITS n) i b, i<n -> getBit (setBit p i b) i = b.
Proof.
induction n => //.  
case/tupleP => [b' p]. move => i b LT.
destruct i => //.
simpl. rewrite theadCons beheadCons. assert (LT' : i < n) by done.
rewrite /getBit/=. apply IHn; done. 
Qed. 

Lemma setBitThenGetDistinct n : 
  forall (p: BITS n) i i' b, i<n -> i'<n -> i<>i' -> getBit (setBit p i b) i' = getBit p i'.
Proof.
induction n => //. 
case/tupleP => [b' p]. move => i i' b LT LT' NEQ.
destruct i. 
(* i = 0 *) simpl. rewrite beheadCons. destruct i' => //. 
(* i <> 0 *) 
destruct i' => //.
rewrite /= theadCons beheadCons /getBit/=.
assert (lt : i < n) by done. 
assert (lt' : i' < n) by done. 
assert (neq' : i <> i') by  intuition. 
specialize (IHn p _ _ b lt lt' neq'). apply IHn. 
Qed. 

(*---------------------------------------------------------------------------
    Properties of all zeroes and all ones
  ---------------------------------------------------------------------------*)
Lemma fromNat0 n : #0 = zero n.
Proof. induction n; first apply trivialBits.
+ rewrite /zero /copy. rewrite /zero /copy in IHn. simpl. by rewrite IHn nseqCons. 
Qed. 

Lemma toNat_zero n : toNat (zero n) = 0. 
Proof. induction n => //. rewrite /toNat/=. rewrite /toNat in IHn. by rewrite IHn. Qed.

Corollary toNat_fromNat0 n : @toNat n #0 = 0.
Proof. by rewrite fromNat0 toNat_zero. Qed.

Lemma msb_zero n : msb (zero n) = false.
Proof. by induction n. Qed.

Lemma toNat_ones_succ n : (toNat (ones n)).+1 = 2^n. 
Proof. induction n => //. 
rewrite /toNat/=. rewrite /toNat/= in IHn. 
by rewrite expnS mul2n addnC addn1 -doubleS IHn. 
Qed. 

Corollary toNat_ones n : toNat (ones n) = (2^n).-1.
Proof. by rewrite -toNat_ones_succ succnK. Qed.

Lemma msb_ones n : msb (ones n.+1) = true.
Proof. by induction n. Qed. 

Lemma toZp_zero n : toZp (zero n) = 0%R. 
Proof. rewrite /toZp toNat_zero. by apply val_inj. Qed.

Lemma toZpAux_zero m n : toZpAux (m:=m) (zero n) = 0%R.
Proof. rewrite /toZpAux toNat_zero. by apply val_inj. Qed. 

Lemma toZp_ones n : toZp (ones n.+1) = (-1)%R. 
Proof. rewrite /toZp toNat_ones. apply val_inj. 
rewrite /= Zp_cast; last apply pow2_gt1. 
rewrite -subn1. replace (1 %% 2^n.+1) with 1 => //. 
by rewrite modn_small; last apply pow2_gt1. 
Qed.


(*---------------------------------------------------------------------------
    Properties of joinmsb and splitmsb
  ---------------------------------------------------------------------------*)

Lemma toNat_joinmsb n : forall c (p: BITS n), toNat (joinmsb (c, p)) = c * 2^n + toNat p.
Proof. induction n. 
+ move => c p. by rewrite /joinmsb (tuple0 p) expn0 muln1. 
+ move => c. case/tupleP => [b p]. 
  rewrite /joinmsb-/joinmsb /splitlsb theadCons beheadCons !toNatCons expnS IHn. 
  by rewrite double_add addnCA -mul2n mulnCA. 
Qed. 

Lemma toNat_joinmsb0 n (p: BITS n) : toNat (joinmsb0 p) = toNat p.
Proof. by rewrite toNat_joinmsb. Qed. 

Lemma splitmsb_fromNat n : 
  forall m, splitmsb (n:=n) #m = (odd (m %/ 2^n), #m). 
Proof. induction n => m. 
+ by rewrite /dropmsb/=beheadCons!theadCons expn0 divn1. 
+ rewrite expnS. simpl.   
  rewrite /joinlsb !beheadCons!theadCons fromNatHalf. specialize (IHn m./2). rewrite IHn. 
  by rewrite -divn2 divn_divl. 
Qed. 

Corollary dropmsb_fromNat n m : dropmsb (n:=n) #m = #m. 
Proof. by rewrite /dropmsb splitmsb_fromNat. Qed. 

Corollary toNat_dropmsb n (p: BITS n.+1) : toNat (dropmsb p) = toNat p %% 2^n.
Proof. rewrite -{1}(toNatK p). rewrite dropmsb_fromNat. by rewrite toNat_fromNat. Qed.

Lemma toZp_joinmsb0 n (p: BITS n) : toZp (joinmsb0 p) = toZpAux p. 
Proof. apply val_inj. 
rewrite /toZp/toZpAux/= Zp_cast; last apply pow2_gt1. 
by rewrite toNat_joinmsb0.
Qed. 

Lemma toZp_dropmsb n (p: BITS n.+2) : toZp (dropmsb p) = toZpAux (m:=n.+1) p. 
Proof. apply val_inj. 
rewrite /toZp/toZpAux/= Zp_cast; last apply pow2_gt1.
rewrite toNat_dropmsb. 
by rewrite modn_mod. 
Qed. 

Lemma splitmsbK n : cancel (@splitmsb n) (@joinmsb n).
Proof. induction n.
+ case/tupleP => [b p]. by rewrite (tuple0 p).  
+ case/tupleP => [b p]. rewrite /= beheadCons theadCons. specialize (IHn p). 
case E: (splitmsb p) => [b' p']. 
rewrite beheadCons theadCons. 
rewrite E in IHn. by rewrite IHn. 
Qed. 

Lemma joinmsbK n : cancel (@joinmsb n) (@splitmsb n).
Proof. induction n. 
+ move => [b p]. by rewrite !(tuple0 p) /= theadCons beheadCons.  
+ move => [c p]. case/tupleP: p => [b p]. 
  by rewrite /= !theadCons !beheadCons IHn. 
Qed. 

Corollary dropmsb_joinmsb n b (p:BITS n) : dropmsb (joinmsb (b, p)) = p.
Proof. by rewrite /dropmsb joinmsbK. Qed.

Lemma splitlsbK n : cancel (@splitlsb n) (@joinlsb n). 
Proof. case/tupleP => [b p]. by rewrite /splitlsb beheadCons theadCons. Qed.

Lemma joinlsbK n : cancel (@joinlsb n) (@splitlsb n). 
Proof. move => [p b]. by rewrite /joinlsb /splitlsb beheadCons theadCons. Qed.

Lemma toNat_joinlsb n (p:BITS n) b : toNat (joinlsb (p, b)) = b + (toNat p).*2.
Proof. done. Qed. 

(*---------------------------------------------------------------------------
    Properties of concatenation and splitting of bit strings
  ---------------------------------------------------------------------------*)
Lemma high_catB n2 n1 (p:BITS n1) (q:BITS n2) : high n1 (p ## q) = p. 
Proof. induction n2.
- rewrite /high (tuple0 q). by apply catNil. 
- case/tupleP: q => x q. rewrite /catB catCons /= beheadCons. apply IHn2. 
Qed. 

Lemma low_catB n2 n1 (p:BITS n1) (q:BITS n2) : low n2 (p ## q) = q. 
Proof. induction n2; first apply trivialBits. 
case/tupleP: q => x q. rewrite /catB catCons /= beheadCons. by rewrite IHn2. 
Qed. 

Lemma split2eta : forall n2 n1 p, let (p1,p2) := split2 n1 n2 p in p = p1 ## p2.  
Proof. unfold split2. induction n2. 
- move =>n1 p. by rewrite /catB catNil. 
- move => n1. case/tupleP => x p. rewrite /= (IHn2 n1 p). 
rewrite beheadCons theadCons high_catB low_catB. by rewrite /catB catCons. Qed.  

Lemma split2app n2 n1 p1 p2 : split2 n1 n2 (p1 ## p2) = (p1,p2).
Proof. by rewrite /split2 high_catB low_catB. Qed.

Lemma split3app n3 n2 n1 p1 p2 p3 : split3 n1 n2 n3 (p1 ## p2 ## p3) = (p1,p2,p3).
Proof. by rewrite /split3 !split2app. Qed. 

Lemma split4app n4 n3 n2 n1 p1 p2 p3 p4 : 
  split4 n1 n2 n3 n4 (p1 ## p2 ## p3 ## p4) = (p1,p2,p3,p4).
Proof. by rewrite /split4 !split2app. Qed. 

Lemma split3eta n3 n2 n1 p: match split3 n1 n2 n3 p with (p1,p2,p3) => p1 ## p2 ## p3 end = p. Proof. rewrite /split3 /=. by rewrite -!split2eta. Qed. 

Lemma split4eta n4 n3 n2 n1 p: 
  match split4 n1 n2 n3 n4 p with (p1,p2,p3,p4) => p1 ## p2 ## p3 ## p4 end = p.  
Proof. rewrite /split4 /=. by rewrite -!split2eta. Qed. 

(*---------------------------------------------------------------------------
    Zero and sign extension
  ---------------------------------------------------------------------------*)

Lemma signExtendK extra n : pcancel (@signExtend extra n) (signTruncate extra). 
Proof. move => p. rewrite /signExtend /signTruncate split2app.
case: (msb p).
+ by rewrite /ones eq_refl. 
+ by rewrite /zero eq_refl.
Qed. 

Lemma signTruncateK extra n p q :
  signTruncate extra (n:=n) p = Some q ->
  signExtend extra (n:=n) q = p.
Proof. rewrite /signTruncate/signExtend.
rewrite (split2eta p) split2app.
case P: (_ || _) => // H.  
have EQ: low n.+1 p = q by congruence. subst.
case M: (msb _). 
+ rewrite M andTb andFb orbF in P. by rewrite (eqP P). 
+ rewrite M andTb andFb orFb in P. by rewrite (eqP P).  
Qed. 

Lemma zeroExtendK extra n : pcancel (@zeroExtend extra n) (zeroTruncate extra).
Proof. move => p. by rewrite /zeroExtend/zeroTruncate split2app eq_refl. Qed. 

Lemma zeroTruncateK extra n p q :
  zeroTruncate extra (n:=n) p = Some q ->
  zeroExtend extra (n:=n) q = p.
Proof. rewrite /zeroTruncate/zeroExtend.
rewrite (split2eta p) split2app.
case P: (high extra p == zero extra) => // H.  
have EQ: low n p = q by congruence. subst.
by rewrite (eqP P). 
Qed. 

(*---------------------------------------------------------------------------
    Properties of equality
  ---------------------------------------------------------------------------*)

Lemma iffBool (b1 b2:bool) : (b1 <-> b2) -> b1==b2.
Proof. destruct b1; destruct b2; intuition. Qed.

Lemma bitsEq_nat n {b1 b2: BITS n} :  (b1 == b2) = (toNat b1 == toNat b2).
Proof. suff: b1 == b2 <-> (toNat b1 == toNat b2). 

move => H. assert (H' := iffBool H). apply (eqP H'). 
split. move => H. rewrite (eqP H). done. 
move => H. assert (EQ:toNat b1 = toNat b2) by apply (eqP H). by rewrite (toNat_inj EQ). 
Qed. 


