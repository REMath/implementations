(*===========================================================================
    Macro for multiplication by a constant
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe basic program.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor basic macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Generate a sequence that computes r1 + r2*m with result in r1 and r2 trashed *)
Open Scope instr_scope.
(*=add_mulc *)
Fixpoint add_mulc nbits (r1 r2: Reg) (m: nat) : program :=
  if nbits is nbits'.+1 
  then if odd m
       then ADD r1, r2;; 
            SHL r2, 1;; 
            add_mulc nbits' r1 r2 m./2
       else SHL r2, 1;; 
            add_mulc nbits' r1 r2 m./2
  else prog_skip.
(*=End *)

(*=add_mulcCorrect *)
Lemma add_mulcCorrect nbits : forall (r1 r2: Reg) m, 
  m < 2^nbits ->
  |-- Forall v, Forall w, 
  basic
  (r1 ~= v ** r2 ~= w ** OSZCP_Any)
  (add_mulc nbits r1 r2 m)
  (r1 ~= addB v (mulB w (fromNat m)) ** r2? ** OSZCP_Any).
(*=End *)
Proof. 
  induction nbits => r1 r2 m LT; rewrite /add_mulc; fold add_mulc; specintros => v w.

  (* nbits = 0 *) 
  destruct m => //. autorewrite with bitsHints push_at. 
  apply: basic_roc_post; last apply basic_skip.
  rewrite /regAny. sbazooka. 

  (* nbits != 0 *)
  have H: m./2 < 2 ^nbits.
  rewrite expnS mul2n in LT.   
  rewrite -(odd_double_half m) in LT. 
  rewrite -ltn_double.
  apply (ltn_addl (odd m)) in LT. 
  by rewrite -(ltn_add2l (odd m)). 

  autorewrite with push_at.

  case ODD: (odd m). 

(* lsb is 1 *)  
  (* ADD r1, r2 *)
  basicapply ADD_RR_ruleNoFlags.
  basicapply SHL_RI_rule => //.
  basicapply IHnbits => //. 
  
  rewrite /iter -addBA shlB_asMul -mulB_muln mul2n. 
  rewrite -{2}(odd_double_half m).  
  by rewrite ODD mulB_addn mulB1. 

  basicapply SHL_RI_rule => //. 
  basicapply IHnbits => //. 
  
  by rewrite /iter shlB_asMul -mulB_muln mul2n -{2}(odd_double_half m) ODD add0n. 
Qed. 


(* More efficient version that does multi-bit shifts *)
Fixpoint add_mulcAux nbits (c:nat) (r1 r2: Reg) (m: nat) : program :=
  (if nbits is nbits'.+1 
  then if odd m
       then 
         if c == 0
         then ADD r1, r2;; add_mulcAux nbits' 1 r1 r2 m./2
         else SHL r2, c;; ADD r1, r2;; add_mulcAux nbits' 1 r1 r2 m./2
       else add_mulcAux nbits' c.+1 r1 r2 m./2
  else prog_skip)%asm.

Lemma add_mulcAuxCorrect nbits : forall (c:nat) (r1 r2: Reg) (m:nat), 
  c+nbits <= 32 -> 
  m < 2^nbits ->
  |-- Forall v, Forall w, 
  basic
  (r1 ~= v ** r2 ~= w)
  (add_mulcAux nbits c r1 r2 m)
  (r1 ~= addB v (w *# (m*2^c)) ** r2?) @ OSZCP_Any.
Proof. 
  induction nbits => c r1 r2 m LT1 LT3;
  rewrite /add_mulcAux; fold add_mulcAux; specintros => v w.

  (* nbits = 0 *) 
  destruct m => //. autorewrite with bitsHints push_at.
  apply: basic_roc_post; last apply basic_skip.
  rewrite /regAny. sbazooka. 

  (* nbits != 0 *)
  have H: m./2 < 2 ^nbits.
  rewrite expnS mul2n in LT3.   
  rewrite -(odd_double_half m) in LT3. 
  rewrite -ltn_double.
  apply (ltn_addl (odd m)) in LT3. 
  by rewrite -(ltn_add2l (odd m)). 

  autorewrite with push_at.

  case ODD: (odd m). 

(* lsb is 1 *)  

  case ZERO: (c == 0). 
  (* c is 0 *)

  (* ADD r1, r2 *)
  basicapply ADD_RR_ruleNoFlags. 

  basicapply IHnbits => //. 
  rewrite (eqP ZERO).  rewrite expn0 muln1 expn1.
  rewrite muln2. rewrite -{2}(odd_double_half m) ODD.  rewrite mulB_addn mulB1 addBA. 
  sbazooka. 

  rewrite (eqP ZERO) add0n in LT1. by rewrite add1n. 

  (* c is not 0 *)

  (* SHL r2, c *)
  basicapply SHL_RI_rule => //. 

  (* ADD r1, r2 *)
  basicapply ADD_RR_ruleNoFlags.

  basicapply IHnbits => //.

  rewrite expn1 -{2}(odd_double_half m) ODD. rewrite muln2. rewrite -addBA.
  rewrite mulnDl mul1n. rewrite mulB_addn. rewrite mulnC. 
  rewrite shlB_mul2exp mulB_muln. sbazooka. 
     
  rewrite add1n. rewrite -addn1 addnA addn1 addnC in LT1. 
  apply (ltn_addr c) in LT1. by rewrite -(ltn_add2r c). 

  rewrite -(addn1) addnA addn1 in LT1. 
  apply (ltn_addr nbits) in LT1. by rewrite -(ltn_add2r nbits). 



(* lsb is 0 *)

  basicapply IHnbits => //. 
  rewrite expnS.  
  rewrite -{2}(odd_double_half m) ODD add0n. 
  rewrite mulnA. rewrite muln2. 
  sbazooka. 
  by rewrite -(addn1 c) -addnA add1n. 
Qed. 

(* Now a peephole optimization, using LEA for special cases *)
Definition add_mulcOpt (r1 r2: NonSPReg) (m:nat) : program :=
  (if m == 2 
  then LEA r1, [r1 + r2*2]
  else
  if m == 4
  then LEA r1, [r1 + r2*4]
  else
  if m == 8
  then LEA r1, [r1 + r2*8]
  else add_mulcAux 32 0 r1 r2 m)%asm.

Lemma add_mulcOptCorrect (r1 r2: NonSPReg) (m:nat): 
  m < 2^32 -> 
  |-- Forall v, Forall w, 
  basic
  (r1 ~= v ** r2 ~= w)
  (add_mulcOpt r1 r2 m)
  (r1 ~= addB v (w *# m) ** r2?) @ OSZCP_Any.
Proof. 
rewrite /add_mulcOpt.
move => LT. specintros => v w. 
autorewrite with push_at. 

case EQ2: (m == 2). 

basicapply LEA_ruleSameBase => //. 
rewrite /eval.scaleBy shlB_asMul addB0 /regAny (eqP EQ2).
sbazooka. 

case EQ4: (m == 4). 

basicapply LEA_ruleSameBase => //.
rewrite /eval.scaleBy !shlB_asMul addB0 /regAny (eqP EQ4) -mulB_muln.
replace (2*2) with 4 by done. sbazooka. 

case EQ8: (m == 8). 
basicapply LEA_ruleSameBase => //. 
rewrite /eval.scaleBy !shlB_asMul addB0 /regAny (eqP EQ8) -!mulB_muln.
replace (2*_) with 8 by done. sbazooka. 

basicapply add_mulcAuxCorrect => //. 
by rewrite expn0 muln1. 
Qed. 


(* More efficient version that does multi-bit shifts. 
   Also with clever use of LEA where possible, iterated *)
Fixpoint add_mulcAux2 nbits (c:nat) (r1:Reg) (r2: NonSPReg) (m: nat) : program :=
  (if nbits is nbits'.+1 
  then if odd m
       then 
         if c == 0
         then ADD r1, r2;; add_mulcAux2 nbits' 1 r1 r2 m./2
         else 
         if c == 1
         then LEA r1, [r1 + r2*2];; add_mulcAux2 nbits' c.+1 r1 r2 m./2
         else
         if c == 2
         then LEA r1, [r1 + r2*4];; add_mulcAux2 nbits' c.+1 r1 r2 m./2
         else
         if c == 3
         then LEA r1, [r1 + r2*8];; add_mulcAux2 nbits' c.+1 r1 r2 m./2
         else SHL r2, c;; ADD r1, r2;; add_mulcAux2 nbits' 1 r1 r2 m./2
       else add_mulcAux2 nbits' c.+1 r1 r2 m./2
  else prog_skip)%asm.


Lemma add_mulcAux2Correct nbits : forall (c:nat) (r1:Reg) (r2:NonSPReg) (m:nat), 
  c+nbits <= 32 -> 
  m < 2^nbits ->
  |-- Forall v, Forall w, 
  basic
  (r1 ~= v ** r2 ~= w)
  (add_mulcAux2 nbits c r1 r2 m)
  (r1 ~= addB v (w *# (m*2^c)) ** r2?) @ OSZCP_Any.
Proof. 
  induction nbits => c r1 r2 m LT1 LT3;
  rewrite /add_mulcAux2; fold add_mulcAux2; specintros => v w.
  autorewrite with push_at. 

  (* nbits = 0 *) 
  destruct m => //. autorewrite with bitsHints.
  apply: basic_roc_post; last apply basic_skip.
  rewrite /regAny. sbazooka. 

  (* nbits != 0 *)
  have H: m./2 < 2 ^nbits.
  rewrite expnS mul2n in LT3.   
  rewrite -(odd_double_half m) in LT3. 
  rewrite -ltn_double.
  apply (ltn_addl (odd m)) in LT3. 
  by rewrite -(ltn_add2l (odd m)). 

  autorewrite with push_at.

  case ODD: (odd m). 

(* lsb is 1 *)  

  case ZERO: (c == 0). 
  (* c is 0 *)

  (* ADD r1, r2 *)
  
  basicapply ADD_RR_ruleNoFlags.

  basicapply IHnbits => //. 
  rewrite (eqP ZERO). rewrite expn0 muln1 expn1.
  rewrite muln2. rewrite -{2}(odd_double_half m) ODD. by rewrite mulB_addn mulB1 addBA. 

  rewrite (eqP ZERO) add0n in LT1. by rewrite add1n. 

  case ONE: (c == 1). 

  (* c is 1 *)
  basicapply LEA_ruleSameBase. 
  rewrite addB0 (eqP ONE) /eval.scaleBy shlB_asMul.

  basicapply IHnbits => //. 
  rewrite expn1 -{2}(odd_double_half m) ODD. rewrite muln2. rewrite -addBA.
  replace (2^2) with (2*2) by done. rewrite mulnA. rewrite -mulB_addn. rewrite !muln2.
  rewrite -(odd_double_half m). by rewrite ODD mulB_addn. 

  rewrite (eqP ONE) in LT1. rewrite add1n in LT1. 
  by apply LT1. 

  case TWO: (c == 2). 

  (* c is 2 *)
  basicapply LEA_ruleSameBase. 
  rewrite addB0 (eqP TWO) /eval.scaleBy shlB_asMul.

  basicapply IHnbits => //. 
  rewrite shlB_asMul. 
  rewrite -addBA. rewrite <-mulBA. rewrite <- (mulBDr w).
  rewrite 3!expnS expn0 muln1 mulnA. 
  rewrite fromNat_mulBn. rewrite fromNat_addBn. rewrite mulnA. rewrite -mulnDl.
  replace (2+m./2 * 2 *2) with (true*2 + m./2 * 2 * 2) by done.  
  rewrite -mulnDl.
  rewrite -ODD. rewrite !muln2. rewrite -> (odd_double_half m).  
  rewrite -!muln2. by rewrite mulnA. 

  rewrite (eqP TWO) in LT1. apply LT1.  

  case THREE: (c == 3). 

  (* c is 3 *)
  basicapply LEA_ruleSameBase. 
  rewrite addB0 (eqP THREE) /eval.scaleBy !shlB_asMul.

  basicapply IHnbits => //.
  rewrite -addBA. rewrite <-!mulBA. rewrite <- (mulBDr w).
  rewrite 4!expnS expn0 muln1 mulnA. 
  rewrite 2!fromNat_mulBn. rewrite fromNat_addBn. rewrite 2!mulnA. rewrite -mulnDl.
  rewrite 2!mulnA. 
  rewrite -mulnDl. 
  replace (2+m./2 * 2 *2) with (true*2 + m./2 * 2 * 2) by done.  
  rewrite -mulnDl.
  rewrite -ODD. rewrite !muln2. rewrite -> (odd_double_half m).  
  rewrite -!muln2. by rewrite mulnA. 

  rewrite (eqP THREE) in LT1. apply LT1.  

  (* c is something else *)

  (* SHL r2, c *)
  basicapply SHL_RI_rule => //.

  (* ADD r1, r2 *)
  basicapply ADD_RR_ruleNoFlags.

  basicapply IHnbits => //. 
  rewrite expn1 -{2}(odd_double_half m) ODD. rewrite muln2. rewrite -addBA.
  rewrite mulnDl mul1n. rewrite mulB_addn. rewrite mulnC.  
  by rewrite shlB_mul2exp mulB_muln. 

  rewrite add1n. rewrite -addn1 addnA addn1 addnC in LT1. 
  apply (ltn_addr c) in LT1. by rewrite -(ltn_add2r c). 

  rewrite -(addn1) addnA addn1 in LT1. 
  apply (ltn_addr nbits) in LT1. by rewrite -(ltn_add2r nbits). 



(* lsb is 0 *)

  basicapply IHnbits.
  rewrite expnS.  
  rewrite -{2}(odd_double_half m) ODD add0n. 
  rewrite mulnA. rewrite muln2. 
  sbazooka. 
  by rewrite -(addn1 c) -addnA add1n. 
  done. 
Qed. 

Definition add_mulcFast (r1:Reg) (r2: NonSPReg) (d:DWORD) : program :=
  add_mulcAux2 32 0 r1 r2 (toNat d).

Lemma add_mulcFastCorrect (r1 r2: NonSPReg) (d:DWORD): 
  |-- Forall v, Forall w, 
  basic
  (r1 ~= v ** r2 ~= w)
  (add_mulcFast r1 r2 d)
  (r1 ~= addB v (mulB w d) ** r2?) @ OSZCP_Any.
Proof. 
rewrite /add_mulcFast.
specintros => v w. 

have LT: toNat d < 2^32 by apply toNatBounded.
autorewrite with push_at.
basicapply add_mulcAux2Correct => //. by rewrite expn0 muln1 toNatK. 
Qed. 

Definition screenWidth:DWORD := Eval compute in #160.
Eval showinstr in linearize (add_mulcFast EDI EDX screenWidth).

