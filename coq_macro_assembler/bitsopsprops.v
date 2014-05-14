 (*===========================================================================
  Proofs of properties of arithmetic and logical operations on n-bit words
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple zmodp fintype.
Require Import tuplehelp bitsrep bitsprops bitsops div nathelp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
    Properties of bitwise logical operations
  ---------------------------------------------------------------------------*)

Lemma liftUnOpCons n op b (p: BITS n) : 
  liftUnOp op (consB b p) = consB (op b) (liftUnOp op p). 
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth (op b)). Qed.

Lemma lift_associative op n : associative op -> associative (liftBinOp (n:=n) op).  
Proof. 
induction n => H. 
- move => x y z. apply trivialBits. 
- rewrite /liftBinOp. rewrite /liftBinOp in IHn. 
  case/tupleP => x xx. case/tupleP => y yy. case/tupleP => z zz.
  rewrite !zipCons !mapCons !zipCons !mapCons.
  rewrite H. by rewrite IHn. 
Qed. 

Lemma lift_left_id n id op : left_id id op -> 
  left_id (copy n id) (liftBinOp (n:=n) op).  
Proof. move => H.
induction n.
- move => x. apply: trivialBits. 
- case/tupleP => x xx.
  unfold liftBinOp in *. unfold copy. rewrite nseqCons zipCons mapCons IHn. 
  by rewrite H. 
Qed. 

Lemma lift_right_id n : forall id op, right_id id op -> 
  right_id (copy n id) (liftBinOp (n:=n) op).  
Proof. move => e op opI . unfold right_id. 
induction n.
- move => x. apply trivialBits.
- case/tupleP => x xx.
unfold liftBinOp in *.
unfold copy. rewrite nseqCons zipCons mapCons IHn. 
by rewrite opI. 
Qed. 

Lemma lift_commutative n : forall op, commutative op -> commutative (liftBinOp (n:=n) op).  
Proof. move => op opC.
induction n.
- move => x y. apply trivialBits.
- case/tupleP => x xx. case/tupleP => y yy.
unfold liftBinOp in *.
do 2 rewrite zipCons. 
do 2 rewrite mapCons. 
rewrite opC. by rewrite IHn. 
Qed. 

Lemma lift_idempotent n : forall op, idempotent op -> idempotent (liftBinOp (n:=n) op).  
Proof. move => op opI. 
induction n.
- move => x. apply trivialBits.
- case/tupleP => x xx. 
unfold liftBinOp in *.
rewrite zipCons. 
rewrite mapCons. 
rewrite opI. by rewrite IHn. 
Qed. 

Lemma xorBC n : commutative (xorB (n:=n)). 
Proof. apply lift_commutative. by elim; elim. Qed.

Lemma andBC n : commutative (andB (n:=n)). 
Proof. apply lift_commutative. by apply andbC. Qed.

Lemma andBB n : idempotent (andB (n:=n)). 
Proof. apply lift_idempotent. by apply andbb. Qed.

Lemma orBC n : commutative (orB (n:=n)). 
Proof. apply lift_commutative. by apply orbC. Qed.

Lemma orBB n : idempotent (orB (n:=n)). 
Proof. apply lift_idempotent. by apply orbb. Qed.

Lemma xorBA n : associative (xorB (n:=n)). 
Proof. apply lift_associative. by elim; elim; elim. Qed.

Lemma andBA n : associative (andB (n:=n)). 
Proof. apply lift_associative. by apply andbA. Qed.

Lemma and1B n : left_id (ones _) (andB (n:=n)).
Proof. by apply lift_left_id. Qed. 

Lemma andB1 n : right_id (ones _) (andB (n:=n)).
Proof. move => x. rewrite andBC. apply and1B. Qed. 

Lemma orBA n : associative (orB (n:=n)). 
Proof. apply lift_associative. by apply orbA. Qed.

Lemma or0B n : left_id #0 (orB (n:=n)). 
Proof. rewrite fromNat0. apply lift_left_id. by apply orFb. Qed. 

Lemma orB0 n : right_id #0 (orB (n:=n)). 
Proof. rewrite fromNat0. apply lift_right_id. by apply orbF. Qed. 

Lemma xor0B n : left_id #0 (xorB (n:=n)). 
Proof. rewrite fromNat0. apply lift_left_id. by elim. Qed. 

Lemma xorB0 n : right_id #0 (xorB (n:=n)). 
Proof. rewrite fromNat0. apply lift_right_id. by elim. Qed. 

Lemma xorBB n : forall x, xorB (n:=n) x x = #0.
Proof. induction n. 
- move => x. apply trivialBits.
- case/tupleP => b x. rewrite /zero/copy.
rewrite /xorB/liftBinOp zipCons mapCons.
rewrite /xorB/liftBinOp/zero/copy in IHn. 
rewrite IHn. by case b. Qed. 

Lemma xorBN : forall n (b : BITS n),
  xorB b (ones n) = invB b.
Proof.
induction n.
- move => x. apply trivialBits.
- case/tupleP => b x. 
  rewrite /xorB/liftBinOp/invB liftUnOpCons/ones/copy. 
  rewrite nseqCons zipCons mapCons. 
  rewrite /xorB/invB/ones/copy/liftBinOp in IHn. by rewrite IHn. 
Qed.

Lemma invB0 n : invB #0 = ones n.
Proof. rewrite /invB fromNat0 /zero /ones /liftUnOp /copy.
induction n. apply trivialBits.
by rewrite nseqCons mapCons IHn nseqCons.
Qed.

Lemma xorBNaux : forall n (b : BITS n),
  xorB b (invB b) = ones _.
Proof. move => n b. by rewrite -xorBN xorBA xorBB xor0B. Qed.

(*---------------------------------------------------------------------------
    Properties of increment and decrement operations
  ---------------------------------------------------------------------------*)
Lemma ones_decomp n : ones n.+1 = consB true (ones n).
Proof. by apply val_inj. Qed.

Lemma zero_decomp n : zero n.+1 = consB false (zero n).
Proof. by apply val_inj. Qed.

Lemma bitsEq_decomp n b1 b2 (p1 p2: BITS n) : 
  (consB b1 p1  == consB b2 p2) = (b1 == b2) && (p1 == p2).
Proof. done. Qed.


(* First, with respect to conversions *)
Lemma toNat_incB n : forall (p: BITS n), toNat (incB p) = if p == ones _ then 0 else (toNat p).+1.
Proof. induction n. 
+ move => p. by rewrite (tuple0 p). 
+ case/tupleP => [b p].
rewrite /= theadCons beheadCons toNatCons.
destruct b => //.
rewrite toNat_joinlsb add0n add1n IHn.  
case E: (p == ones n). 
+ by replace (_ == _) with true. 
+ by rewrite ones_decomp/= bitsEq_decomp doubleS E. 
Qed. 

Lemma toNatMod_incB n (p: BITS n) : toNat (incB p) = (toNat p).+1 %[mod 2^n].
Proof. rewrite toNat_incB.  
case E: (p == ones n) => //. 
by rewrite (eqP E) toNat_ones_succ modnn mod0n. 
Qed. 

Lemma toNat_decB_succ n : forall (p: BITS n), (toNat (decB p)).+1 = if p == #0 then 2^n else toNat p.
Proof. induction n.  
+ move => p. by rewrite (tuple0 p). 
+ case/tupleP => [b p].
rewrite /=theadCons beheadCons toNatCons. 
destruct b => //.
rewrite toNat_joinlsb add0n.
specialize (IHn p). 
case E: (p == #0) => //. 
+ rewrite (eqP E). rewrite (eqP E) eq_refl in IHn. rewrite expnS. rewrite -IHn. 
  replace (_ == _) with true. by rewrite add1n mul2n doubleS.
  rewrite /fromNat-/fromNat/=/joinlsb. simpl. by rewrite eq_refl. 
+ replace (_ == _) with false. rewrite E in IHn. rewrite -IHn. 
  rewrite doubleS. by rewrite add1n. 
Qed. 

Lemma toNat_decB n (p: BITS n) : toNat (decB p) = (if p == #0 then 2^n else toNat p).-1.
Proof. by rewrite -toNat_decB_succ succnK. Qed. 

Lemma nonZeroIsSucc n (p: BITS n) : p != #0 -> exists m, toNat p = m.+1. 
Proof. move => H. 
case E: (toNat p) => [| n']. 
+ rewrite -(toNatK p) in H. by rewrite E fromNat0 eq_refl in H.
+ by exists n'. 
Qed.

Lemma toNatMod_decB n (p: BITS n) : toNat (decB p) = (toNat p + (2^n).-1) %[mod 2^n].
Proof. rewrite toNat_decB. 
case E: (p == #0) => //. 
+ rewrite (eqP E) {E}. by rewrite toNat_fromNat0 add0n. 
+ apply negbT in E. destruct (nonZeroIsSucc E) as [m E']. rewrite E'. rewrite succnK.  
rewrite -!subn1. rewrite addnBA. rewrite addnC. rewrite -addnBA => //. 
rewrite subn1 succnK. by rewrite modnDl. 
apply expn_gt0. 
Qed. 

Lemma fromNatDouble b n : forall m, cons_tuple b (fromNat (n:=n) m) = fromNat (b + m.*2).
Proof. move => m. rewrite /fromNat-/fromNat/=. rewrite odd_add odd_double. 
destruct b. simpl. by rewrite uphalf_double.
by rewrite add0n half_double. 
Qed.  

Require Import ssralg. 
Import GRing.Theory. 

(*---------------------------------------------------------------------------
    All operations in BITS n (for n>0) have corresponding operations 
    in 'Z_(2^n).
  ---------------------------------------------------------------------------*)

Lemma toZp_incB n (p:BITS n.+1) : toZp (incB p) = (toZp p + 1)%R. 
Proof. apply val_inj. rewrite /= Zp_cast; last apply pow2_gt1. 
rewrite modnDml modnDmr addn1 toNat_incB.  
case E: (p == ones _) => //. 
by rewrite (eqP E) toNat_ones_succ modnn mod0n. 
Qed. 

Lemma toZp_decB n (p:BITS n.+1) : toZp (decB p) = (toZp p - 1)%R. 
Proof. apply val_inj.
set N := n.+1. 
set D :=decB p. 
rewrite /= Zp_cast; last apply pow2_gt1.
rewrite /D {D}.
rewrite toNatMod_decB. replace (1 %% 2^N) with 1. 
rewrite (@modn_small (2^N - 1)). 
rewrite (@modn_small (toNat p)). by rewrite subn1. 
apply toNatBounded. 
apply pow2_sub_ltn. 
rewrite modn_small => //; last apply pow2_gt1. 
Qed. 

Hint Rewrite toZp_incB toZp_decB : ZpHom.

(*---------------------------------------------------------------------------
    We can now prove properties via 'Z_(2^n).

    The pattern to these proofs is as follows:
    1. Deal with the n=0 case by 
         destruct n; first apply trivialBits
    2. Embed into toZp using
         apply toZp_inj
    3. Repeatedly apply homomorphisms from BITS n into 'Z_n using equations
       with names toZp_X such as toZp_incB or toZp_adcB
    4. You're now in the land of 'Z_n and ring theory, so apply lemmas from
       ssralg and zmodp.        
  ---------------------------------------------------------------------------*)

Lemma decBK n : cancel (@decB n) incB. 
Proof. move => p. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.  
by rewrite -addrA addNr addr0. 
Qed. 

Lemma incBK n : cancel (@incB n) decB.
Proof. move => p. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite -addrA addrN addr0. 
Qed. 

Lemma decB_zero n : decB (zero n) = ones _.
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite sub0r. 
Qed. 

Lemma incB_ones n : incB (ones n) = zero _.
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom. 
by rewrite addNr.  
Qed. 

Lemma incB_fromNat n m : incB (n:=n) #m = #(m.+1). 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom. 
by rewrite -(addn1 m) natrD. 
Qed. 

Lemma decB_fromSuccNat n m : decB (n:=n) #(m.+1) = #m.
Proof. destruct n => //. 
apply toZp_inj. autorewrite with ZpHom. 
rewrite -(addn1 m) GRing.natrD. 
by rewrite GRing.addrK. 
Qed. 

Lemma incBDistinct n : forall (p: BITS n.+1), incB p <> p.
Proof. case/tupleP => b p'. by elim b. Qed. 

Lemma incBincBDistinct n : forall (p: BITS n.+2), incB (incB p) <> p.
Proof. case/tupleP => b p'. case/tupleP: p' => b' p'. elim b; by elim b'. Qed. 

Lemma incBincBincBDistinct n : forall (p: BITS n.+2), incB (incB (incB p)) <> p.
Proof. case/tupleP => b p'. case/tupleP: p' => b' p'. elim b; by elim b'. Qed. 

Lemma incBneq n : forall (p: BITS n.+1), incB p != p. 
Proof. move => p. apply (introN eqP). apply: incBDistinct. Qed. 

Lemma incBincBneq n : forall (p: BITS n.+2), incB (incB p) != p. 
Proof. move => p. apply (introN eqP). apply: incBincBDistinct. Qed. 

Lemma incBincBincBneq n : forall (p: BITS n.+2), incB (incB (incB p)) != p. 
Proof. move => p. apply (introN eqP). apply: incBincBincBDistinct. Qed. 
(*
Lemma bitsEqInc n : forall (p: BITS n.+1), bitsEq (incB p) p = false.
Proof. move => p. replace (bitsEq (incB p) p) with (incB p == p) by done. 
apply negbTE. apply incBneq. Qed.

Lemma bitsEqIncInc n : forall (p: BITS n.+2), bitsEq (incB (incB p)) p = false.
Proof. move => p. replace (bitsEq _ p) with (incB (incB p) == p) by done. 
apply negbTE. apply incBincBneq. Qed.

Lemma bitsEqIncIncInc n : forall (p: BITS n.+2), bitsEq (incB (incB (incB p))) p = false.
Proof. move => p. replace (bitsEq _ p) with (incB (incB (incB p)) == p) by done. 
apply negbTE. apply incBincBincBneq. Qed.
*)
(*---------------------------------------------------------------------------
    Properties of inversion (one's complement)
  ---------------------------------------------------------------------------*)

Lemma invBCons n b (p: BITS n) : invB (cons_tuple b p) = cons_tuple (negb b) (invB p). 
Proof. rewrite /invB. by rewrite liftUnOpCons. Qed. 

Lemma negB_or_invB_fromNat n : forall m, m < 2^n -> 
   negB (n:=n) #m = #(2^n - m)
/\ invB (n:=n) #m = #((2^n).-1 - m). 
Proof. induction n. split; [done | apply trivialBits].
move => m H. 
rewrite expnS mul2n in H. pose H' := half_ltn_double H. elim (IHn _ H') => [IH1 IH2] {IHn}. 
split. 
+
rewrite /negB. 
rewrite /fromNat-/fromNat. rewrite invBCons IH2 /=!theadCons!beheadCons. 
rewrite odd_sub. rewrite odd_power2/=. 
case ODD: (odd m). 
- rewrite expnS mul2n. rewrite half_sub. 
  rewrite uphalf_half ODD -subn1 subnDA. done. apply (ltnW H). 
- rewrite incB_fromNat. 
  rewrite expnS mul2n half_sub. 
  rewrite uphalf_half ODD add0n.  
  rewrite -subn1. rewrite subnAC. rewrite subn1. rewrite prednK.  done.
  by rewrite subn_gt0.
  apply (ltnW H). 
- rewrite expnS mul2n. apply (ltnW H). 
rewrite /fromNat-/fromNat invBCons IH2. rewrite odd_sub/=.
rewrite odd_power2subn1/=. rewrite -!subn1 -!subnDA expnS mul2n. 
rewrite half_sub. done. apply H. 
rewrite expnS mul2n. apply leq_subn; last done. rewrite -mul2n -expnS. apply expn_gt0. 
Qed.

Corollary negB_fromNat n m : m < 2^n -> negB (n:=n) #m = #(2^n - m). 
Proof. apply negB_or_invB_fromNat. Qed. 

Corollary invB_fromNat n m : m < 2^n -> invB (n:=n) #m = #((2^n).-1 - m). 
Proof. apply negB_or_invB_fromNat. Qed. 

Lemma toNat_negB_or_invB n : forall (p: BITS n), 
   (toNat (negB p) = if toNat p == 0 then 0 else 2^n - toNat p)
/\ (toNat (invB p) = (2^n).-1 - toNat p).
Proof. induction n. move => p. by rewrite (tuple0 p)/toNat/=. 
case/tupleP => [b p]. rewrite /negB !invBCons!toNatCons/=!theadCons!beheadCons. 
elim (IHn p) => [IH1 IH2]. split. case b.  
+ simpl. rewrite toNatCons IH2. 
  rewrite doubleB expnS mul2n. rewrite -subn1 doubleB/=. 
  rewrite add1n. rewrite -!mul2n. rewrite muln1. rewrite subnAC. rewrite subn2.
  rewrite subnDA.  rewrite subnAC. rewrite prednK. by rewrite subn1. 
  assert (B:=toNatBounded p). rewrite !mul2n -doubleB. 
  rewrite -subn1. rewrite subn_gt0. rewrite -subn_gt0 in B. rewrite -half_gt0. 
  rewrite doubleK. done. 

+ simpl. rewrite toNatCons. rewrite !add0n. 
rewrite /negB in IH1. rewrite IH1. 
  case E: (toNat p) => [| n']. done. 
  simpl. rewrite doubleB expnS -muln2 mulnC. done.  

case b. 
+ simpl. rewrite add0n. rewrite IH2. rewrite expnS. rewrite -!subn1 !doubleB. 
  rewrite -!muln2. rewrite mul1n subnDA. rewrite mulnC. rewrite !subn1 subn2. done. 
+ simpl. rewrite add0n. rewrite IH2. rewrite expnS. rewrite -!subn1 !doubleB. 
  rewrite -!muln2. rewrite mul1n. rewrite add1n. rewrite subnAC. rewrite mulnC.
  rewrite subn2. 
  assert (B:0 < (2*2^n - toNat p * 2).-1).
  assert (B':=toNatBounded p). rewrite mul2n muln2. rewrite -doubleB. 
  rewrite -subn_gt0 in B'.  rewrite -subn1 subn_gt0 -half_gt0 doubleK. done. 
  rewrite (ltn_predK B). rewrite -subn1. by rewrite subnAC. 
Qed.   

Corollary toNat_invB n (p: BITS n) : toNat (invB p) = (2^n).-1 - toNat p.
Proof. apply toNat_negB_or_invB. Qed. 

Corollary toNat_negB n (p: BITS n) : toNat (negB p) = 
  if toNat p == 0 then 0 else 2^n - toNat p.
Proof. apply toNat_negB_or_invB. Qed. 

(* There must be an easier way to prove this! *)
Lemma toZp_invB n (p:BITS n.+1) : toZp (invB p) = (-toZp p - 1)%R.
Proof. apply val_inj. 
rewrite /= Zp_cast; last apply pow2_gt1. 
rewrite toNat_invB. 
rewrite (@modn_small 1); last apply pow2_gt1.
rewrite (@modn_small (toNat p)); last apply toNatBounded. 
rewrite (@modn_small (2^n.+1-1)); last apply pow2_sub_ltn. 

rewrite modn_small.

case E: (toNat p) => [| p']. 
+ rewrite 2!subn0. rewrite modnn add0n.
  rewrite modn_small; last apply pow2_sub_ltn. by rewrite subn1.  
 
  rewrite -subn1 -subnDA add1n. 
  rewrite (@modn_small (2^n.+1 - p'.+1)); last apply pow2_sub_ltn.
  rewrite addnBA; last apply expn_gt0.
  rewrite addnC. 
  rewrite -addnBA. 
  rewrite addnC.   rewrite modnDr.
  rewrite -subnDA. rewrite addn1. rewrite modn_small; last apply pow2_sub_ltn.
  done.      
  have B:= toNatBounded p. 
  rewrite -E. 
  by rewrite subn_gt0. 
  rewrite -subn1. rewrite -subnDA. rewrite add1n. apply pow2_sub_ltn. 
Qed. 

(*
Corollary invB_fromNatAux n m : m < 2^n -> invB (n:=n) #m = #((2^n).-1 - m). 
Proof. move => H. destruct n; first apply trivialBits. 
apply toZp_inj. rewrite toZp_invB 2!toZp_fromNat. 
rewrite -subn1. rewrite natr_sub.  
rewrite natr_sub; last apply expn_gt0. rewrite addrAC. 
done. rewrite oppr_sub. subrCA. rewrite modZp. done.  simpl. . done. => //. rewrite subrr. _sub. rewrite -Zp_opp.  rewrapply apply negB_or_invB_fromNat. Qed. 
*)

(*---------------------------------------------------------------------------
    Properties of negation (two's complement)
  ---------------------------------------------------------------------------*)

Lemma toZp_negB n (p:BITS n.+1) : toZp (negB p) = (-toZp p)%R.
Proof. apply val_inj. rewrite /= Zp_cast; last apply pow2_gt1. 
rewrite toNat_negB. 
case E: (toNat p) => [| n']. 
+ simpl. rewrite modn_small. by rewrite subn0 modnn. 
  apply expn_gt0. 
+ simpl. rewrite modn_small.
  rewrite (@modn_small (n'.+1)). 
  rewrite modn_small.   done. 
  apply pow2_sub_ltn. 
  rewrite -E. apply toNatBounded. 
  apply pow2_sub_ltn. 
Qed. 

Hint Rewrite toZp_negB : ZpHom.

Lemma negBK n : involutive (@negB n). 
Proof. move => p. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite opprK. 
Qed. 

Lemma negB_zero n : negB (zero n) = zero _. 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite oppr0. 
Qed.

Corollary negB0 n : @negB n #0 = #0. 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite oppr0. 
Qed. 

(*---------------------------------------------------------------------------
    Properties of addition
  ---------------------------------------------------------------------------*)

Lemma fullAdderTT c : fullAdder c true true = (true,c). 
Proof. by destruct c. Qed.

Lemma adcB_nat n : forall b (p1 p2: BITS n), adcB b p1 p2 = #(b + toNat p1 + toNat p2).
Proof. 
induction n.
+ move => b p1 p2. rewrite 2!toNatNil. by destruct b. 
+ move => b. case/tupleP => [b1 p1]. case/tupleP => [b2 p2]. 
  rewrite /fromNat-/fromNat/=. 
  rewrite !theadCons !beheadCons !toNatCons !odd_add !odd_double /=. 
  case e: (fullAdder b b1 b2) => [carry' b0].    
  specialize (IHn carry' p1 p2). rewrite IHn /= addnA.
  assert (b0 = odd b (+) (odd b1 (+) false) (+) (odd b2 (+) false)). 
  rewrite /fullAdder in e. destruct b; destruct b1; destruct b2; inversion e; subst; done.  
  rewrite -H. 
  assert (carry' + toNat p1 + toNat p2 = 
          (b + (b1 + (toNat p1).*2) + b2 + (toNat p2).*2)./2). 
  rewrite addnA (addnC _ b2) -!addnA -doubleD !addnA. 
  rewrite /fullAdder in e. destruct b; destruct b1; destruct b2; inversion e; subst; simpl;
  by (try rewrite uphalf_double; try rewrite half_double). 
  rewrite H0. by apply val_inj. 
Qed. 

Lemma adcB_bounded n (b:bool) (p1 p2: BITS n) : b + toNat p1 + toNat p2 < 2^n.+1. 
Proof.
have B1 := toNatBounded p1. 
have B2 := toNatBounded p2. 
rewrite expnS mul2n -addnn.
have B :=leq_add B1 B2.  
destruct b. 
+ rewrite addnC add1n -addn1 addnC addnA add1n. apply leq_add; done. 
+ rewrite add0n -addn1 addnC addnA add1n. apply leq_add; first done. by rewrite ltnW. 
Qed.

Corollary toNat_adcB n b (p1 p2: BITS n) : toNat (adcB b p1 p2) = b + toNat p1 + toNat p2.
Proof. 
rewrite adcB_nat. rewrite toNat_fromNatBounded => //. 
apply adcB_bounded. 
Qed. 

Lemma toZp_adcB n b (p1 p2:BITS n) : 
  toZp (adcB b p1 p2) = (bool_inZp _ b + toZpAux p1 + toZpAux p2)%R. 
Proof. 
apply val_inj. rewrite /= Zp_cast; last apply pow2_gt1. 
rewrite toNat_adcB.
have BOUND:= adcB_bounded b p1 p2. 
rewrite modn_small => //.
rewrite (@modn_small b).
rewrite (@modn_small (toNat p1)).
rewrite (@modn_small (toNat p2)).
rewrite (@modn_small (b + toNat p1)).
rewrite modn_small => //.
apply: leq_ltn_trans BOUND. apply leq_addr. 
apply: leq_ltn_trans BOUND. rewrite addnC. apply leq_addr. 
apply: leq_ltn_trans BOUND. rewrite -addnAC. apply leq_addl. 
apply: leq_ltn_trans BOUND. rewrite -addnA. apply leq_addr. 
Qed. 

Corollary toNat_addB n (p1 p2: BITS n) : toNat (addB p1 p2) = (toNat p1 + toNat p2) %% 2^n.
Proof. rewrite /addB. rewrite toNat_dropmsb toNat_adcB. 
by rewrite add0n. 
Qed. 

Corollary toZp_addB n (p1 p2: BITS n.+1) : toZp (addB p1 p2) = (toZp p1 + toZp p2)%R. 
Proof. apply val_inj. rewrite /toZp. rewrite toNat_addB. 
rewrite /= Zp_cast; last apply pow2_gt1. 
rewrite (@modn_small (toNat p1)); last apply toNatBounded. 
rewrite (@modn_small (toNat p2)); last apply toNatBounded.
by rewrite modn_mod.
Qed. 

Hint Rewrite toZp_adcB toZp_addB : ZpHom.

Lemma addBC n : commutative (@addB n).
Proof. move => x y. destruct n; first apply trivialBits.    
apply toZp_inj. autorewrite with ZpHom.
by rewrite addrC. 
Qed.

(*=addBA *)
Lemma addBA n : associative (@addB n).
Proof. move => x y z. destruct n; first apply trivialBits.
  apply toZp_inj. autorewrite with ZpHom.
  by rewrite addrA. Qed.
(*=End *)

Lemma adcBC n c : commutative (@adcB n c).
Proof. move => x y.
apply toZp_inj. autorewrite with ZpHom.
by rewrite addrAC. 
Qed.

Lemma adc0B n (p : BITS n) : adcB false #0 p = joinmsb0 p.
Proof. 
apply toZp_inj. rewrite fromNat0.  autorewrite with ZpHom. 
rewrite /bool_inZp -Zp_nat. 
by rewrite 2!add0r. 
Qed. 

Lemma adcB0 n (p : BITS n) : adcB false p #0 = joinmsb0 p.
Proof. 
apply toZp_inj. rewrite fromNat0. autorewrite with ZpHom. 
by rewrite /bool_inZp addr0 -!Zp_nat add0r. 
Qed. 

Lemma add0B n : left_id #0 (@addB n). 
Proof. move => x. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom. 
by rewrite add0r. 
Qed.

Lemma addB0 n : right_id #0 (@addB n). 
Proof. move => x. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite addr0. 
Qed.

Lemma fromNat_addBn n m1 m2 : #m1 +# m2 = fromNat (n:=n) (m1 + m2). 
Proof. apply toNat_inj. rewrite toNat_addB !toNat_fromNat. by rewrite modnDm. Qed. 

Lemma addB_addn n (p:BITS n) m1 m2 : p +# (m1+m2) = p +# m1 +# m2. 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite natrD addrA. 
Qed. 

Lemma addB1 n (p: BITS n) : p +# 1 = incB p. 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
done. 
Qed. 

Lemma addB_negBn n (p: BITS n) m : addB (p +# m) (negB #m) = p. 
Proof. destruct n; first apply trivialBits.
apply toZp_inj. autorewrite with ZpHom. 
by rewrite -addrA addrN addr0.   
Qed. 

Lemma addB_decB_incB n (c a: BITS n) : addB (decB c) (incB a) = addB c a.
Proof. destruct n; first apply trivialBits.
apply toZp_inj. autorewrite with ZpHom. 
by rewrite addrAC -2!addrA addrN addr0. 
Qed. 

Lemma addBN n (p: BITS n) : addB (negB p) p = #0. 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite addNr. 
Qed. 

Lemma addNB n (p: BITS n) : addB p (negB p) = #0. 
Proof. by rewrite addBC addBN. Qed. 

Lemma adcIsInc n c (p:BITS n) : dropmsb (adcB c p #0) = if c then incB p else p.
Proof. rewrite adcB_nat dropmsb_fromNat fromNat0 toNat_zero addn0. destruct c. 
+ by rewrite -incB_fromNat toNatK.  
+ by rewrite add0n toNatK. 
Qed. 


(* Add is iterated increment *)
(* Proof seems a bit contorted! *)
Lemma adcIsIterInc n m : forall c (p:BITS n), 
  dropmsb (adcB c p #m) = iter m incB (if c then incB p else p). 
Proof. 
induction m => c p. 
+ by rewrite /= adcIsInc. 
+ rewrite /= -IHm. clear IHm. rewrite 2!adcB_nat. rewrite !dropmsb_fromNat. 
  set D := c + toNat p.
  rewrite incB_fromNat.  
  rewrite -(addn1 (D + toNat #m)) -addnA. 
  apply fromNat_addn. rewrite toNatK addn1. apply fromNat_succn. by rewrite toNatK. 
Qed. 


Corollary addIsIterInc n (p:BITS n) m : p +# m = iter m incB p. 
Proof. apply adcIsIterInc. Qed.

(*---------------------------------------------------------------------------
    Properties of subtraction
  ---------------------------------------------------------------------------*)

Lemma subB_is_dropmsb_adcB_invB  n (p q: BITS n) : subB p q = dropmsb (adcB true p (invB q)). 
Proof. rewrite /subB/dropmsb/sbbB. simpl (~~false). 
by case (splitmsb (adcB true p (invB q))).  
Qed. 

Lemma toZp_subB n (p q: BITS n.+1) : toZp (subB p q) = (toZp p - toZp q)%R.
Proof. rewrite subB_is_dropmsb_adcB_invB. 
apply val_inj. rewrite toZp_dropmsb /toZpAux.
rewrite toNat_adcB toNat_invB. rewrite add1n. 
rewrite /inZp/= Zp_cast; last apply pow2_gt1.  
rewrite (@modn_small (toNat p)); last apply toNatBounded. 
rewrite (@modn_small (toNat q)); last apply toNatBounded.
rewrite -addn1. 
rewrite -subn1. rewrite -subnDA. rewrite addnAC. rewrite -addnA. rewrite addn1 add1n. rewrite -subSn; last apply toNatBounded.
case E: (toNat q) => [| n']. 
  rewrite !subn0 modnn addn0. rewrite subn1. rewrite succnK. by rewrite modnDr. 
  rewrite (@modn_small (2^n.+1 - n'.+1)); last apply pow2_sub_ltn. 
  done.   
Qed. 

Hint Rewrite toZp_subB : ZpHom.

Lemma subB_equiv_addB_negB n (p q: BITS n): subB p q = addB p (negB q). 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. by autorewrite with ZpHom. 
Qed. 

(* This is absurdly complicated! *)
Lemma sbb0B_carry n (p: BITS n.+1) : fst (sbbB false #0 p) = (p != #0).
Proof. rewrite /sbbB. simpl (~~false). 
elim E: (splitmsb (adcB true #0 (invB p))) => [carry res]. 
rewrite -(toNatK (adcB true #0 (invB p))) in E. 
rewrite splitmsb_fromNat in E. 
rewrite toNat_adcB toNat_fromNat0 addn0 toNat_invB in E.
inversion E.  
clear E H0 H1. 
rewrite add1n.
case E: (p == #0).
+ rewrite (eqP E). rewrite toNat_fromNat0. 
rewrite subn0. rewrite prednK; last apply expn_gt0.  
by rewrite divnn expn_gt0.  
+ apply negbT in E. have [m H] := (nonZeroIsSucc E).  
  rewrite H.
  rewrite divn_small => //.
  rewrite -subSn.  rewrite prednK; last apply expn_gt0.  
  apply pow2_sub_ltn. 
  have B:= toNatBounded p. 
  rewrite H in B. 
  have HH := @ltn_sub2r 1 m.+1 (2^n.+1). 
  rewrite subn1 in HH. 
  rewrite prednK in HH => //. 
  rewrite subn1 in HH. 
  apply HH. 
  apply pow2_gt1. 
  apply B.
Qed. 

Lemma subB0 n (p: BITS n) : subB p #0 = p. 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite subr0. 
Qed. 

Lemma sub0B n (p: BITS n) : subB #0 p = negB p.  
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite sub0r. 
Qed. 

Lemma subBB n (p: BITS n) : subB p p = #0.
Proof. destruct n; first apply trivialBits.
apply toZp_inj. autorewrite with ZpHom.
by rewrite subrr. 
Qed. 

Lemma toNat_addBn n : forall (p: BITS n) m, toNat (p +# m) = (toNat p + m) %% 2^n.
Proof. move => p m. 
rewrite /addB adcB_nat add0n dropmsb_fromNat. 
rewrite !toNat_fromNat. 
by rewrite modnDmr. 
Qed. 

Corollary inZp_addBn n (p:BITS n.+1) m : toZp (p +# m) = inZp (toNat p + m).
Proof. apply val_inj. rewrite /inZp/toZp. 
rewrite toNat_addBn.
rewrite /= Zp_cast; last apply pow2_gt1. 
apply modn_mod. 
Qed. 


Lemma toNat_addBn_wrap n : forall (p: BITS n) m, 
  m<2^n -> toNat p + m >= 2^n -> toNat (p +# m) + 2^n = toNat p + m. 
Proof. 
move => p m BOUND H.
rewrite /addB adcB_nat add0n dropmsb_fromNat. 
rewrite toNat_fromNat. rewrite toNat_fromNat.
rewrite modnDmr. apply modn_sub.
+ apply expn_gt0. + apply toNatBounded. + done. + done. 
Qed.  

Lemma addBsubBn n (p: BITS n) m1 m2 : m2 <= m1 -> p +# (m1-m2) = p +# m1 -# m2.
Proof. move => H. destruct n; first apply trivialBits.
apply toZp_inj. autorewrite with ZpHom.
rewrite natrB => //. 
by rewrite addrA. 
Qed.

Lemma subB_def n (p q: BITS n.+1) : subB p q = fromZp (toZp p - toZp q)%R.
Proof. apply toZp_inj. by autorewrite with ZpHom. Qed. 

Lemma addB_def n (p q: BITS n.+1) : addB p q = fromZp (toZp p + toZp q)%R.
Proof. apply toZp_inj. by autorewrite with ZpHom. Qed. 

Lemma addB0_inv n (p: BITS n) m : m < 2^n -> p == p +# m -> m = 0. 
Proof. move => BOUND EQ. 
destruct n. by destruct m.
have: toNat p == toNat (p +# m). by rewrite {1}(eqP EQ). 
rewrite toNat_addB. 
rewrite toNat_fromNat. rewrite (@modn_small m); last done. 
rewrite -{1}(@modn_small (toNat p) (2^n.+1)).  
rewrite -{1}(addn0 (toNat p)).
rewrite eqn_modDl. rewrite modn_small.
rewrite modn_small; last done.  
by move/eqP ->. 
apply expn_gt0. apply toNatBounded. 
Qed. 

Lemma subB_eq n (x y z: BITS n) : (subB x z == y) = (x == addB y z). 
Proof. destruct n. by rewrite (tuple0 x) (tuple0 y) (tuple0 z). 
rewrite 2!toZp_eq. autorewrite with ZpHom.
by rewrite subr_eq. 
Qed. 

Lemma subB_eq0 n (x y: BITS n) : (subB x y == #0) = (x == y).
Proof. destruct n. by rewrite (tuple0 x) (tuple0 y).
rewrite 2!toZp_eq. autorewrite with ZpHom.
by rewrite subr_eq0. 
Qed.

Lemma subB1 n (p: BITS n) : p -# 1 = decB p.
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. by autorewrite with ZpHom.
Qed. 

Lemma subB_addn n (p:BITS n) m1 m2 : p -# (m1+m2) = p -# m1 -# m2. 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite natrD opprD addrA. 
Qed. 

Lemma subB_addB n (p: BITS n) m1 m2 : 
  p -# m1 +# m2 = if m1<m2 then p +# (m2-m1) else p -# (m1-m2). 
Proof.  destruct n; first apply trivialBits. 
case E: (m1 < m2). 
apply toZp_inj. autorewrite with ZpHom.
rewrite natrB. rewrite addrAC.  by rewrite addrA. by apply ltnW. 
apply toZp_inj. autorewrite with ZpHom.
rewrite natrB. rewrite addrAC. rewrite opprB. by rewrite addrA. 
rewrite leqNgt. by rewrite E. 
Qed. 

(*---------------------------------------------------------------------------
    Properties of unsigned comparison
  ---------------------------------------------------------------------------*)


Lemma ltB_nat n : forall p1 p2: BITS n, ltB p1 p2 = (toNat p1 < toNat p2). 
Proof. 
induction n. move => p1 p2. by rewrite (tuple0 p1) (tuple0 p2). 
move => p1 p2. case/tupleP: p1 => [b1 q1]. case/tupleP: p2  => [b2 q2]. 
rewrite 2!toNatCons /= !beheadCons !theadCons IHn. 
case E: (toNat q1 < toNat q2). simpl. 
case b1; case b2; simpl.
+ by rewrite ltn_add2l ltn_double.  
+ by rewrite add0n addnC addn1 ltn_Sdouble. 
+ by rewrite add0n addnC addn1 ltnS leq_double ltnW. 
+ by rewrite !add0n ltn_double. 
case b1; case b2; simpl. 
+ rewrite ltn_add2l ltn_double E. by rewrite andbF.  
+ rewrite add0n addnC addn1 ltn_Sdouble E. by rewrite andbF. 
+ rewrite add0n addnC addn1 ltnS leq_double. rewrite !andbT.
rewrite leq_eqVlt E. rewrite orbF.
apply bitsEq_nat. 
+ rewrite !add0n ltn_double E. by rewrite andbF. 
Qed. 

Lemma leB_nat n (p1 p2: BITS n) : leB p1 p2 = (toNat p1 <= toNat p2).
Proof. 
rewrite /leB. 
rewrite ltB_nat. 
rewrite bitsEq_nat. rewrite orbC.
by rewrite (leq_eqVlt (toNat p1)). 
Qed. 


Lemma ltB_bound n (p q: BITS n) : ltB p q -> toNat p < (2^n).-1.
Proof. rewrite ltB_nat. have B:= toNatBounded q.  
move => H. eapply leq_trans.  apply H. rewrite -ltnS. 
rewrite prednK; last apply expn_gt0. done. 
Qed. 


Lemma ltB_leB n (p q: BITS n.+1) : ltB p q -> leB (p +# 1) q.
Proof. move => H. rewrite leB_nat toNat_addB toNat_fromNat. 
rewrite (@modn_small 1). 
rewrite modn_small. rewrite addn1. by rewrite ltB_nat in H. have LTB := ltB_bound H. 
rewrite -(ltn_add2r 1) in LTB. 
rewrite addn1. rewrite !addn1 in LTB. rewrite prednK in LTB. apply LTB. 
apply expn_gt0. apply pow2_gt1. 
Qed. 


(*
Lemma ltB_inc n (p: BITS n) : ~isOnes p -> ltB p (incB p).
Proof. move => H. rewrite ltB_nat. rewrite toNat_incB.  simpl in H. H. toNatMod_incB. Qed. 
*)

Lemma leB_weaken n (p1 p2: BITS n) : ltB p1 p2 -> leB p1 p2. 
Proof. move => H. by rewrite /leB H. Qed. 

(*
Lemma leB_inc n (p: BITS n) : ~isOnes p -> leB p (incB p).
Proof. move => H. apply leB_weaken. by apply ltB_inc. Qed.
*)

Lemma ltB_trans n (p1 p2 p3: BITS n) : ltB p1 p2 -> ltB p2 p3 -> ltB p1 p3.
Proof. move => H1 H2. 
rewrite ltB_nat in H1. rewrite ltB_nat in H2. rewrite ltB_nat. by apply: ltn_trans H1 H2. 
Qed. 

Lemma leB_trans n (p1 p2 p3: BITS n) : leB p1 p2 -> leB p2 p3 -> leB p1 p3.
Proof. move => H1 H2. 
rewrite leB_nat in H1. rewrite leB_nat in H2. rewrite leB_nat. by apply: leq_trans H1 H2.
Qed. 

Lemma ltB_leB_trans n (p1 p2 p3: BITS n) : ltB p1 p2 -> leB p2 p3 -> ltB p1 p3.
Proof. move => H1 H2. 
rewrite ltB_nat in H1. rewrite leB_nat in H2. rewrite ltB_nat. 
rewrite leq_eqVlt in H2. destruct (orP H2).
+ by rewrite -(eqP H). 
apply: ltn_trans H1 H. 
Qed. 

Lemma leB_ltB_trans n (p1 p2 p3: BITS n) : leB p1 p2 -> ltB p2 p3 -> ltB p1 p3.
Proof. move => H1 H2. 
rewrite leB_nat in H1. rewrite ltB_nat in H2. rewrite ltB_nat. apply: leq_ltn_trans H1 H2. 
Qed. 

Lemma leB_refl n (p : BITS n) : leB p p.
Proof. by rewrite /leB eq_refl orbT. Qed. 

Lemma leB0 n (p : BITS n) : leB #0 p. 
Proof. by rewrite leB_nat toNat_fromNat0. Qed. 


Lemma ltB_joinmsb0 n (p q : BITS n) : ltB (joinmsb0 p) (joinmsb0 q) = ltB p q.
Proof. by rewrite ltB_nat 2!toNat_joinmsb0 -ltB_nat. Qed. 

Lemma leB_bounded {n} : forall (p: BITS n) m, 
  m < 2^n -> 
  leB p (p +# m) -> 
  toNat p + m < 2^n.
Proof. move => p m BOUND. 
rewrite leB_nat => H.
case B:(toNat p + m < 2^n); first done. 
apply negbT in B. rewrite -ltnNge ltnS in B.
assert (HH:= toNat_addBn_wrap BOUND B). 
rewrite -(leq_add2r m) in H. 
rewrite -HH in H. 
rewrite leq_add2l in H. 
rewrite leqNgt in H.
rewrite BOUND in H.  
done. 
Qed. 

Lemma leB_bounded_weaken {n} : forall (p:BITS n) m1 m2 m3, 
  m3 < 2^n ->
  m1 <= m2 ->
  m2 <= m3 ->
  leB p (p +# m3) ->
  leB (p +# m1) (p +# m2). 
Proof.   
move => p m1 m2 m3 BOUND LE1 LE2. move => H. 
assert (H1 := leB_bounded BOUND H). 
rewrite leB_nat. rewrite /addB !adcB_nat add0n !dropmsb_fromNat. 
assert (m2 < 2^n) by apply (leq_ltn_trans LE2 BOUND). 
rewrite (toNat_fromNatBounded H0). 
assert (m1 < 2^n) by apply (leq_ltn_trans (leq_trans LE1 LE2) BOUND). 
rewrite (toNat_fromNatBounded H2). 
rewrite !toNat_fromNatBounded. 
by rewrite leq_add2l. 
assert (toNat p + m2 <= toNat p + m3). 
by rewrite leq_add2l. 
apply (leq_ltn_trans H3 H1). 
assert (toNat p + m1 <= toNat p + m3). 
rewrite leq_add2l. apply (leq_trans LE1 LE2). 
apply (leq_ltn_trans H3 H1). 
Qed. 


Lemma ltB_incR n q (p:BITS n) : ltB p q -> ltB p (p +# 1).
Proof. move => H. have LTB := ltB_bound H.  
rewrite ltB_nat addB1 toNat_incB. 
case E: (p == ones _). 
+ rewrite (eqP E) in LTB. by rewrite toNat_ones ltnn in LTB. 
+ apply ltnSn. 
Qed. 

Lemma ltB_incL n q (p: BITS n.+1) : leB #1 q -> ltB p (q -#1) -> ltB (p +#1) q. 
Proof. rewrite leB_nat !ltB_nat toNat_addB toNat_fromNat. 
rewrite modn_small; last apply pow2_gt1. rewrite subB1. rewrite toNat_decB. 
case E: (q == #0).
+ by rewrite (eqP E) toNat_fromNat0. 
+ move => E1 E2. 
  rewrite -(ltn_add2r 1) in E2. rewrite 2!addn1 in E2. 
  rewrite prednK in E2 => //. 
  rewrite addn1. rewrite modn_small => //. 
  have B:= toNatBounded q. by apply (ltn_trans E2). 
Qed. 

(*---------------------------------------------------------------------------
    Relationship of ltB/leB with addition
  ---------------------------------------------------------------------------*)
Lemma ltBleB_joinmsb0_adcB n : forall c (p1 p2: BITS n),
  if c then ltB (joinmsb0 p1) (adcB c p1 p2) else leB (joinmsb0 p1) (adcB c p1 p2).
Proof. 
move => c p1 p2. 
rewrite ltB_nat leB_nat adcB_nat toNat_joinmsb0. 
assert (B1 := toNatBounded p1). 
assert (B2 := toNatBounded p2). 
assert (c + toNat p1 + toNat p2 < 2^n.+1). 
  rewrite expnS mul2n -addnn.
  assert (B:=leq_add B1 B2).  
  destruct c. 
  rewrite addnC add1n -addn1 addnC addnA add1n. apply leq_add; done. 
  rewrite add0n -addn1 addnC addnA add1n. apply leq_add; first done. by rewrite ltnW. 
destruct c. 
rewrite toNat_fromNatBounded; last done. by rewrite ltn_addr. 
rewrite toNat_fromNatBounded; last done. rewrite add0n. by rewrite leq_addr. 
Qed. 

Corollary leB_joinmsb0_adcB n : forall p1 p2: BITS n, leB (joinmsb0 p1) (adcB false p1 p2).
Proof. apply (ltBleB_joinmsb0_adcB false). Qed. 

Corollary ltB_joinmsb0_adcB n : forall p1 p2: BITS n, ltB (joinmsb0 p1) (adcB true p1 p2).
Proof. apply (ltBleB_joinmsb0_adcB true). Qed.

Lemma ltBleB_adcB n : 
  forall c (p1 p2 p : BITS n), 
  splitmsb (adcB c p1 p2) = (false,p) -> 
  if c then ltB p1 p else leB p1 p.
Proof. induction n. 
+ move => c p1 p2 p H. rewrite (tuple0 p) (tuple0 p1).
  destruct c. simpl in H. inversion H. done. 
+ move => c. case/tupleP => [b1 p1]. case/tupleP => [b2 p2]. case/tupleP => [b p]. 
simpl. rewrite !theadCons !beheadCons.
destruct c.
(* c = true *)
move => H. simpl in H. 
destruct b1.
(* b1 = true *)
specialize (IHn true p1 p2). 
case E: (splitmsb (adcB true p1 p2)) => [carry' p']. 
destruct b2. 
(* b2 = true *)
rewrite beheadCons theadCons E in H. inversion H. apply val_inj in H3. subst. 
rewrite IHn; first by rewrite orTb. done. 
(* b2 = false *) 
rewrite beheadCons E in H. inversion H. apply val_inj in H3. subst. 
rewrite IHn; first by rewrite orTb. done. 
(* b1 = false *)
destruct b2. 
(* b2 = true *)
specialize (IHn true p1 p2). 
case E: (splitmsb (adcB true p1 p2)) => [carry' p']. 
rewrite beheadCons E in H. inversion H. apply val_inj in H3. subst. 
rewrite IHn; first by rewrite orTb. done. 
(* b2 = false *) 
specialize (IHn false p1 p2). 
case E: (splitmsb (adcB false p1 p2)) => [carry' p']. 
rewrite beheadCons E in H. inversion H. apply val_inj in H3. subst. simpl. 
rewrite /leB in IHn. rewrite !andbT. by rewrite IHn.  

(* c = false *)
move => H. simpl in H. 
destruct b1.
(* b1 = true *)
destruct b2. 
(* b2 = true *)
specialize (IHn true p1 p2). 
case E: (splitmsb (adcB true p1 p2)) => [carry' p']. 
rewrite beheadCons E in H. inversion H. apply val_inj in H3. subst. 
specialize (IHn _ E). rewrite /leB. simpl. rewrite !beheadCons. by rewrite IHn. 
(* b2 = false *) 
specialize (IHn false p1 p2). 
case E: (splitmsb (adcB false p1 p2)) => [carry' p']. 
rewrite beheadCons E in H. inversion H. apply val_inj in H3. subst. 
rewrite /leB. simpl. rewrite !beheadCons. specialize (IHn _ E). 
rewrite /leB in IHn. rewrite andbF. rewrite orbF. done. 
(* b1 = false *)
specialize (IHn false p1 p2). destruct b2. 
(* b2 = true *)
case E: (splitmsb (adcB false p1 p2)) => [carry' p']. 
rewrite beheadCons E in H. inversion H. apply val_inj in H3. subst.
rewrite /leB.  
simpl. rewrite !beheadCons !theadCons. 
rewrite /leB in IHn. specialize (IHn _ E). rewrite orbA. rewrite orbF.  
rewrite orbA. rewrite orbF. rewrite IHn. done. 
(* b2 = false *) 
case E: (splitmsb (adcB false p1 p2)) => [carry' p']. 
rewrite beheadCons E in H. inversion H. apply val_inj in H3. subst. 
rewrite /leB. simpl. 
rewrite !beheadCons !theadCons. specialize (IHn _ E). 
rewrite /leB in IHn. rewrite andbT. rewrite andbF. rewrite orbF.
done.  

Qed. 

Corollary addB_leB n : forall p1 p2 p: BITS n, splitmsb (adcB false p1 p2) = (false, p) -> leB p1 p.
Proof. apply: ltBleB_adcB. Qed. 

Corollary adcB_ltB n : forall p1 p2 p: BITS n, splitmsb (adcB true p1 p2) = (false, p) -> ltB p1 p.
Proof. apply: ltBleB_adcB. Qed.



Lemma adcB_leB_op n : forall (p1 p2 p: BITS n) c carry, 
  splitmsb (adcB c p1 p2) = (carry,p) ->
  (if c then ltB p1 p else leB p1 p) -> carry = false. 
Proof. induction n.
+ move => p1 p2 p. rewrite (tuple0 p1) (tuple0 p2) (tuple0 p) /= => c carry. 
  destruct c. congruence. rewrite theadCons/=. congruence. 
+ case/tupleP => [b1 p1]. case/tupleP => [b2 p2]. case/tupleP => [b p]. 
  move => c carry.  
  rewrite/leB/= !beheadCons!theadCons.
  move => EQ PE.
  destruct c.
  rewrite /= in EQ. 
  (* c = true *)
  destruct b1. 
  (* b1 = true *)
  destruct b2. 
  (* b2 = true *)
  case E: (splitmsb (adcB true p1 p2)) => [carry'' p'].
  specialize (IHn _ _ _ _ _ E). rewrite beheadCons E in EQ. 
  injection EQ => E1 E2 E3. 
  rewrite -E3. apply IHn. 
  rewrite /= -(val_inj _ _ E1) in PE. by rewrite andbF andFb orbF in PE. 
  (* b2 = false *)
  case E: (splitmsb (adcB true p1 p2)) => [carry'' p'].
  specialize (IHn _ _ _ _ _ E). rewrite beheadCons E in EQ. 
  injection EQ => E1 E2 E3. 
  rewrite -E3. apply IHn. 
  rewrite -(val_inj _ _ E1) in PE. by rewrite andbF andFb orbF in PE. 
  (* b1 = false *)
  destruct b2. 
  (* b2 = true *)
  case E: (splitmsb (adcB true p1 p2)) => [carry'' p'].
  specialize (IHn _ _ _ _ _ E). rewrite beheadCons E in EQ. 
  injection EQ => E1 E2 E3. 
  rewrite -E3. apply IHn. 
  rewrite /= -(val_inj _ _ E1) in PE. by rewrite -E2 andbF orbF in PE.   
  (* b2 = false *)
  case E: (splitmsb (adcB false p1 p2)) => [carry'' p'].
  specialize (IHn _ _ _ _ _ E). rewrite beheadCons E in EQ. 
  injection EQ => E1 E2 E3. 
  rewrite -E3. apply IHn. 
  rewrite -(val_inj _ _ E1) -E2 in PE. rewrite /leB. by rewrite !andbT in PE. 

  (* c = false *) 
  rewrite /= in EQ. 
  destruct b1. 
  (* b1 = true *)
  destruct b2. 
  (* b2 = true *)
  case E: (splitmsb (adcB true p1 p2)) => [carry'' p'].
  specialize (IHn _ _ _ _ _ E). rewrite beheadCons E in EQ. 
  injection EQ => E1 E2 E3. 
  rewrite -E3. apply IHn. 
  rewrite /= -(val_inj _ _ E1) -E2 in PE. by rewrite !andbF orbF/= orbF in PE. 
  (* b2 = false *)
  case E: (splitmsb (adcB false p1 p2)) => [carry'' p'].
  specialize (IHn _ _ _ _ _ E). rewrite beheadCons E in EQ. 
  injection EQ => E1 E2 E3. 
  rewrite -E3. apply IHn. 
  rewrite -(val_inj _ _ E1) -E2 in PE. rewrite /leB. by rewrite /= andbF andbT orbF /= in PE. 
  (* b1 = false *)
  destruct b2. 
  (* b2 = true *)
  case E: (splitmsb (adcB false p1 p2)) => [carry'' p'].
  specialize (IHn _ _ _ _ _ E). rewrite beheadCons E in EQ. 
  injection EQ => E1 E2 E3. 
  rewrite -E3. apply IHn. 
  rewrite /= -(val_inj _ _ E1) -E2 in PE. by rewrite !andbT /= orbF in PE. 
  (* b2 = false *)
  case E: (splitmsb (adcB false p1 p2)) => [carry'' p'].
  specialize (IHn _ _ _ _ _ E). rewrite beheadCons E in EQ. 
  injection EQ => E1 E2 E3. 
  rewrite -E3. apply IHn. 
  rewrite -(val_inj _ _ E1) -E2 in PE. rewrite /leB. by rewrite !andbT andbF orbF in PE. 
Qed.   

Lemma thead_negB n : forall b (p:BITS n), thead (negB (cons_tuple b p)) = b.
Proof. move => b p. by destruct b. Qed. 

Corollary sbbB_ltB_leB n (p1 p2: BITS n) : 
  if (sbbB false p1 p2).1 then ltB p1 p2 else leB p2 p1.
Proof. rewrite /sbbB adcB_nat toNat_invB splitmsb_fromNat ltB_nat leB_nat. 
simpl. rewrite !add1n. assert (POS: 2^n > 0) by apply expn_gt0.  
assert (B1 := toNatBounded p1). 
assert (B2 := toNatBounded p2). 
rewrite addnBA. rewrite -subn1. rewrite addnBA; last done. rewrite -addn1. 
rewrite -addnAC. rewrite addn1 subn1/=. rewrite addnC. rewrite addn1.
case P: (toNat p1 < toNat p2).
assert (2^n + toNat p1 - toNat p2 < 2^n).
rewrite -(ltn_add2r (toNat p2)). rewrite subnK. by rewrite ltn_add2l. 
assert (H: 2^n <= 2^n + toNat p1) by apply leq_addr. 
apply: leq_trans H. apply (ltnW B2). 
rewrite (divn_small H). done. 

apply negbT in P. rewrite -leqNgt in P. 
rewrite -(addnBA _ P) divnDl; last done. rewrite divnn POS odd_add/=.
rewrite negbK. 
assert (toNat p1 - toNat p2 < 2^n). 
assert (H := leq_subr (toNat p2) (toNat p1)). 
apply: leq_ltn_trans. apply H.  done. rewrite (divn_small H). done.  
rewrite -(leq_add2r 1). 
rewrite !addn1 prednK. done. apply expn_gt0. 
Qed. 

Lemma toNat_subB n (p q: BITS n) : leB q p -> toNat (subB p q) = toNat p - toNat q.
Proof. move => LE.
have P := toNatBounded p. 
have Q := toNatBounded q. 
case E: (p == q). rewrite (eqP E). by rewrite subBB toNat_fromNat0 subnn.  
rewrite subB_equiv_addB_negB. 
rewrite toNat_addB. 
rewrite toNat_negB. 
case E': (toNat q == 0). rewrite (eqP E') subn0 addn0. 
rewrite modn_small //. 
rewrite addnBA; last first. apply ltnW => //. 
rewrite addnC. rewrite -addnBA. rewrite modnDl. rewrite modn_small => //.
have H : (toNat p - toNat q <= toNat p) by apply leq_subr. 
apply: leq_ltn_trans H P. 
by rewrite leB_nat in LE. 
Qed. 

(*---------------------------------------------------------------------------
    Shifts and rotates
  ---------------------------------------------------------------------------*)
Lemma toNat_shrB n : forall (p: BITS n), toNat (shrB p) = (toNat p)./2. 
Proof. destruct n. move => p. by rewrite (tuple0 p). 
case/tupleP => [b p]. 
by rewrite /shrB toNat_joinmsb0 /droplsb/splitlsb beheadCons theadCons toNatCons half_bit_double. 
Qed. 

Lemma toNat_shlBaux n : forall (p: BITS n), toNat (shlBaux p) = (toNat p).*2. 
Proof. move => p. by rewrite /shlBaux toNatCons. Qed. 

Lemma toNat_shlB n  (p: BITS n) : toNat (shlB p) = ((toNat p).*2) %% 2^n.
Proof. by rewrite /shlB toNat_dropmsb toNat_shlBaux. Qed.

Lemma toNat_rorB n (p: BITS n.+1) : toNat (rorB p) = (toNat p)./2 + (toNat p %% 2) * 2^n.
Proof. case/tupleP: p => [b p].
rewrite /rorB toNat_joinmsb /droplsb/splitlsb beheadCons theadCons toNatCons /=. 
rewrite half_bit_double. rewrite modn2 odd_add odd_double addnC. by destruct b. 
Qed. 

Lemma toNat_rolB n (p: BITS n.+1) : toNat (rolB p) = (toNat p %% 2^n).*2 + toNat p %/ 2^n.
Proof.
rewrite /rolB. rewrite -{1}(toNatK p).  
rewrite splitmsb_fromNat. 
rewrite toNatCons toNat_fromNat. 
rewrite addnC. 
have H:= toNatBounded p. 
case E: (toNat p %/ 2^n) => [| n']. 
+ by rewrite addn0.
+ case E': n' => [| n'']. done. 
+ rewrite E' in E.  
  rewrite expnS in H. 
  rewrite -ltn_divLR in H; last apply expn_gt0. 
  rewrite E in H. subst.
  destruct n'' => //. 
Qed. 

Lemma rorBK n : cancel (@rorB n) (@rolB n). 
Proof. rewrite /cancel/rorB/rolB.  
case/tupleP => [b p]. case C: (splitlsb [tuple of b::p]) => [b' p']. rewrite joinmsbK.  
by rewrite -C splitlsbK. 
Qed. 

Lemma rolBK n : cancel (@rolB n) (@rorB n). 
Proof. rewrite /cancel/rorB/rolB.  
case/tupleP => [b p]. case C: (splitmsb [tuple of b::p]) => [b' p']. rewrite joinlsbK. 
by rewrite -C splitmsbK. 
Qed. 

Lemma toZp_shlBaux n (p: BITS n) : toZp (shlBaux p) = (toZpAux p * 2%:R)%R. 
Proof. destruct n. by rewrite (tuple0 p). 
apply val_inj. 
rewrite /toZp toNat_shlBaux. rewrite /=Zp_cast; last apply pow2_gt1.
rewrite modn_small. 
rewrite (@modn_small 1); last apply pow2_gt1.  
rewrite (@modn_small (1+1)). 
rewrite (@modn_small (toNat p)).
rewrite addnn. rewrite muln2. 
rewrite (@modn_small) => //. 
rewrite expnS mul2n ltn_double. apply toNatBounded.
have B:=toNatBounded p. 
have: 2^n.+1 <= 2^n.+2. replace (2^n.+2) with (2 * 2^n.+1). apply leq_pmull => //. 
by rewrite -expnS. apply: leq_trans B.  
rewrite addnn. rewrite expnS mul2n. rewrite ltn_double. apply pow2_gt1. 
rewrite expnS mul2n. rewrite ltn_double. apply toNatBounded. 
Qed. 

Lemma toZp_shlB n (p: BITS n) : toZp (shlB p) = (toZp p * 2%:R)%R. 
Proof. destruct n. by rewrite (tuple0 p). 

destruct n. 
case/tupleP: p => [b p]. 
rewrite (tuple0 p). by destruct b. 

rewrite /shlB.  rewrite toZp_dropmsb /toZpAux. 
rewrite toNat_shlBaux. rewrite /toZp.
apply val_inj. rewrite /=Zp_cast.
rewrite (@modn_small 1); last apply pow2_gt1.  
rewrite (@modn_small (toNat p)); last apply toNatBounded. 
rewrite addnn.  
rewrite (@modn_small 1.*2). 
by rewrite muln2. 
rewrite expnS mul2n. rewrite ltn_double. 
apply pow2_gt1. apply pow2_gt1. 
Qed. 

Lemma toZpCons n (p: BITS n) b : toZp  [tuple of b :: p] = (b%:R + toZpAux p * 2%:R)%R. 
Proof. 
rewrite /toZp. rewrite toNatCons. rewrite -muln2. rewrite -Zp_nat. 
rewrite natrD natrM. 
by rewrite /toZpAux -Zp_nat. 
Qed.

Hint Rewrite toZp_shlBaux toZp_shlB : ZpHom.

Lemma shlB_dropmsb n (p: BITS n.+1) : shlB (dropmsb p) = dropmsb (shlB p). 
Proof.
apply toNat_inj. 
rewrite toNat_shlB 2!toNat_dropmsb toNat_shlB. 
rewrite -(mul2n (toNat p)). rewrite (expnS 2 n). rewrite -muln_modr; last done. 
by rewrite mul2n. 
Qed. 

Lemma shrB_droplsb n (p: BITS n.+1) : shrB (droplsb p) = droplsb (shrB p). 
Proof. destruct n. simpl. case/tupleP: p => [b p]. 
rewrite /droplsb. simpl. by rewrite !beheadCons. 
by apply toNat_inj. Qed. 

Lemma dropmsb_iter_shlB n count c (p: BITS n) : 
  dropmsb (iter count shlB (joinmsb (c, p))) = iter count shlB p.
Proof. induction count => //.
+ apply toNat_inj. rewrite /iter. by rewrite dropmsb_joinmsb. 
+ rewrite !iterS. rewrite -IHcount.
  by rewrite shlB_dropmsb. 
Qed.   

Lemma droplsb_iter_shrB n count c (p: BITS n) :
  droplsb (iter count shrB (joinlsb (p, c))) = iter count shrB p.
Proof. induction count => //.
+ by apply toNat_inj. 
+ rewrite 2!iterS. by rewrite -shrB_droplsb IHcount. 
Qed.    


(*---------------------------------------------------------------------------
    Multiplication
  ---------------------------------------------------------------------------*)

Lemma toNat_fullmulB n1 n2 (p1:BITS n1) (p2: BITS n2) : 
  toNat (fullmulB p1 p2) = (toNat p1 * toNat p2). 
Proof. induction n1. 
rewrite (tuple0 p1)/=. by rewrite !mul0n toNat_fromNat mod0n.
case/tupleP: p1 => [b p].
rewrite /=theadCons toNatCons beheadCons. 
destruct b. 

+ rewrite toNat_addB toNat_joinlsb toNat_joinmsb0 IHn1 add0n toNat_zeroExtendAux. 
  rewrite -!muln2. rewrite mulnDl mul1n addnC -mulnAC. 
  rewrite modn_small => //. 
  rewrite -{1}(mul1n (toNat p2)).  
  rewrite -mulnDl.
  rewrite expnD.   
  rewrite ltn_mul => //. 
  rewrite expnS. rewrite add1n muln2 mul2n. rewrite ltn_Sdouble. 
  apply (toNatBounded p). 
  apply (toNatBounded p2).

by rewrite toNat_joinlsb IHn1 !add0n -!muln2 mulnAC.
Qed. 

Lemma modZp_pow m n : inZp (m %% 2 ^ n.+1) = inZp (p' := (Zp_trunc (2^n.+1)).+1) m. 
Proof. apply val_inj. simpl. rewrite prednK. 
rewrite prednK. by rewrite modn_mod. apply expn_gt0. 
have P:= pow2_gt1 n. 
rewrite -(ltn_add2r 1). rewrite !addn1 prednK.
done. apply expn_gt0. 
Qed. 

Lemma toZp_mulB n (p1 p2: BITS n) : toZp (mulB p1 p2) = (toZp p1 * toZp p2)%R. 
Proof. destruct n. by rewrite (tuple0 p1) (tuple0 p2).
rewrite /mulB/toZp. rewrite toNat_low. rewrite toNat_fullmulB.
rewrite modZp_pow. rewrite -!Zp_nat. by rewrite !natrM. 
Qed. 

Hint Rewrite toZp_mulB : ZpHom.

Lemma toNat_mulB n (p1 p2: BITS n) : toNat (mulB p1 p2) = (toNat p1 * toNat p2) %% 2^n. 
Proof. by rewrite toNat_low toNat_fullmulB. Qed. 

Lemma mul1B n (p: BITS n) : mulB #1 p = p.
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite GRing.mul1r. 
Qed. 

Lemma mulB1 n (p: BITS n) : mulB p #1 = p.
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite GRing.mulr1. 
Qed. 

Lemma mulB0 n (p: BITS n) : mulB p #0 = #0.
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite GRing.mulr0. 
Qed. 

Lemma mulBC n (p q: BITS n) : mulB p q = mulB q p. 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite GRing.mulrC. 
Qed. 

Lemma mul0B n (p: BITS n) : mulB #0 p = #0.
Proof. by rewrite mulBC mulB0. Qed. 

Lemma mulBA n (p q r: BITS n) : mulB p (mulB q r) = mulB (mulB p q) r. 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite GRing.mulrA.
Qed. 

Lemma mulBDl n : left_distributive (@mulB n) (@addB n). 
Proof. move => p q r. 
destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite GRing.mulrDl. 
Qed.

Lemma mulBDr n : right_distributive (@mulB n) (@addB n). 
Proof. move => p q r. 
destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite GRing.mulrDr. 
Qed.

Lemma shlB_asMul n (p:BITS n) : shlB p = mulB p #2. 
Proof.
destruct n. by rewrite (tuple0 p) /shlB/shlBaux/mulB/joinlsb/dropmsb/=beheadCons. 
apply toZp_inj. by autorewrite with ZpHom.
Qed.

Lemma mulB_muln n (p:BITS n) m1 m2 : p *# (m1*m2) = p *# m1 *# m2. 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite natrM mulrA.
Qed. 

Lemma mulB_addn n (p:BITS n) m1 m2 : p *# (m1+m2) = addB (p *# m1) (p *# m2). 
Proof. destruct n; first apply trivialBits. 
apply toZp_inj. autorewrite with ZpHom.
by rewrite natrD mulrDr. 
Qed. 

Lemma fromNat_mulBn n m1 m2 : #m1 *# m2 = fromNat (n:=n) (m1 * m2). 
Proof. apply toNat_inj. rewrite toNat_mulB !toNat_fromNat. by rewrite modnMm. Qed. 

Lemma shrB_shlBaux n (p: BITS n) : shrB (shlBaux p) = joinmsb (false, p). 
Proof. apply toNat_inj.
rewrite toNat_shrB toNat_shlBaux toNat_joinmsb. 
by rewrite mul0n add0n doubleK.  
Qed. 

Lemma msbCons n b (p:BITS n.+1) : msb (consB b p) = msb p. 
Proof. case/tupleP: p => [b' p]. by rewrite /msb last_cons. Qed. 

Lemma msb0Bounded n (p: BITS n.+1) : msb p == false <-> toNat p < 2^n.
Proof. induction n. case/tupleP: p => [b p]. rewrite (tuple0 p). by destruct b.
case/tupleP: p => [b p]. 
split => H. 
rewrite toNatCons. 
rewrite msbCons in H. destruct (IHn p) as [H1 H2]. specialize (H1 H). 
destruct b. 
rewrite add1n expnS mul2n. by rewrite ltn_Sdouble. 
rewrite add0n expnS mul2n. by rewrite ltn_double.
rewrite toNatCons in H. 
destruct (IHn p) as [H1 H2]. 
rewrite msbCons. apply H2.
destruct b. rewrite add1n expnS mul2n in H. 
by rewrite ltn_Sdouble in H. 
rewrite add0n expnS mul2n in H.
by rewrite ltn_double in H.
Qed. 

Lemma shrB_shlB n (p: BITS n.+1) : msb p == false -> shrB (shlB p) = p.
Proof. move => H. 
apply toNat_inj. 
rewrite toNat_shrB toNat_shlB. 
rewrite expnS mul2n. rewrite -!muln2. rewrite -muln_modl => //. 
have: toNat p < 2^n. apply (proj1 (msb0Bounded _)) => //. 
move => LT. rewrite modn_small => //. 
by rewrite muln2 doubleK. 
Qed. 

Lemma shrB_mul2 n (p: BITS n.+1) : msb p == false -> shrB (p *# 2) = p.
Proof. move => H. rewrite -shlB_asMul. by apply shrB_shlB. Qed. 

Lemma shrB_mul2exp m : forall n (p: BITS (m+n)), toNat p < 2^n -> iter m shrB (p *# (2^m)) = p.
Proof. 
induction m. move => n p H. by rewrite /iter expn0 mulB1. 
move => n. rewrite (addSn m n). 
case/tupleP => [b p]. move => H. 
rewrite iterSr expnS mulB_muln.
rewrite -mulBA (mulBC #2) mulBA.
specialize (IHm n.+1). rewrite addnS in IHm. 
specialize (IHm ([tuple of b::p])). 
rewrite expnS mul2n in IHm. 
rewrite shrB_mul2. rewrite IHm. done. 
apply (ltn_trans H). rewrite -muln2. apply ltn_Pmulr => //. apply expn_gt0. 
rewrite msb0Bounded. 
rewrite !expnD. rewrite toNat_mulB. rewrite toNatCons. rewrite toNat_fromNat.
rewrite (@modn_small (2^m)). 
rewrite expnS expnD. rewrite toNatCons in H. set BB := b + (toNat p).*2. fold BB in H. 
rewrite modn_small. rewrite mulnC. rewrite ltn_mul2l. rewrite H andbT. apply expn_gt0. 
rewrite mulnC. rewrite (mulnC 2 _) -mulnA. rewrite ltn_mul2l. 
rewrite (expn_gt0 2 m)/=.
have: 2^n < 2^n * 2. rewrite ltn_Pmulr => //. apply expn_gt0. by apply (ltn_trans).  
rewrite expnS expnD mulnCA. rewrite ltn_Pmulr => //. rewrite -expnS. apply pow2_gt1. 
apply expn_gt0. 
Qed. 

Lemma shlB_mul2exp n m (p:BITS n) : iter m shlB p = p *# 2^m. 
Proof. induction m. by rewrite expn0 mulB1.  
by rewrite iterS expnS IHm shlB_asMul -mulB_muln mulnC.  
Qed. 



(*---------------------------------------------------------------------------
    Algebraic structures
  ---------------------------------------------------------------------------*)
Section Structures.

Variable n:nat. 

Require Import choice fintype fingroup finalg. 
Definition BITS_zmodMixin := ZmodMixin (@addBA n) (@addBC n) (@add0B n) (@addBN n). 
Canonical Structure BITS_zmodType := Eval hnf in ZmodType (BITS n) BITS_zmodMixin.
Canonical Structure BITS_finZmodType := Eval hnf in [finZmodType of BITS n].
Canonical Structure BITS_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of (BITS n) for +%R].
Canonical Structure BITS_finGroupType :=
  Eval hnf in [finGroupType of  (BITS n) for +%R].

End Structures.

(*---------------------------------------------------------------------------
    Definitions for ring tactics on DWORDs and BYTEs
  ---------------------------------------------------------------------------*)
Definition BITSring (n:nat) := 
  @mk_rt (BITS n) #0 #1 addB mulB subB negB eq 
  (@add0B n) (@addBC n) (@addBA n)
  (@mul1B n) (@mulBC n) (@mulBA n)
  (@mulBDl n) (@subB_equiv_addB_negB n) (@addNB n).

Definition xorInvB n (p q: BITS n) := xorB p (invB q). 

Lemma andBDl n : left_distributive (@andB n) (@xorB n). 
Proof. rewrite /left_distributive.  
induction n. move => x y z. apply trivialBits. 
case/tupleP => [x xx]. 
case/tupleP => [y yy]. 
case/tupleP => [z zz].
rewrite /andB/xorB/liftBinOp. rewrite !zipCons !mapCons !zipCons !mapCons.
rewrite /andB/xorB/liftBinOp in IHn. 
rewrite IHn. simpl. 
set X := (_ && z). set Y := (xorb _ _).  
have: X = Y. rewrite /X/Y. 
by elim x; elim y; elim z. by move ->. 
Qed. 

Definition BITSbooleanring (n:nat) :=
  @mk_rt (BITS n) #0 (ones _) xorB andB xorB id eq
  (@xor0B n) (@xorBC n) (@xorBA n)
  (@and1B n) (@andBC n) (@andBA n)
  (@andBDl n) (fun _ _ => refl_equal _) (@xorBB n).

Add Ring DWORDring : (BITSring 32). 
Add Ring BYTEring : (BITSring 8). 

Add Ring DWORDbooleanring : (BITSbooleanring 32).
Add Ring BYTEbooleanring : (BITSbooleanring 8).

(* Small hint database for directed "shrinking" rewrites *)
Hint Rewrite 
  decBK incBK decB_zero incB_ones incB_fromNat decB_fromSuccNat
  xorBB xorB0 xor0B xorBN xorBNaux
  invB0 invB_fromNat
  negB0 negBK negB_fromNat
  add0B addB0 addBN addNB addB_negBn addB_decB_incB
  subB0 sub0B subBB subB_addB
  mul1B mulB1 mul0B mulB0
  orB0 or0B orBB
  andB1 and1B andBB 
  rorBK rolBK 
  shlB_asMul shlB_mul2exp : bitsHints.

Hint Rewrite
  <- addB_addn subB_addn : bitsHints. 

