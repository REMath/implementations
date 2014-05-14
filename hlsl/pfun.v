(*===========================================================================
    Partial functions, represented as X -> option Y
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section PFun.

  Variable X Y : Type.

  (* Asymmetric combination of partial functions, right-hand operand taking priority *)
  Definition extend (f1 f2: X -> option Y) :=
  fun x => if f2 x is Some z then Some z else f1 x.

  Definition includedIn (f1 f2: X -> option Y) :=
  forall x y, f1 x = Some y -> f2 x = Some y.

  Lemma includedIn_refl f : includedIn f f.
  Proof. rewrite /includedIn; intuition.
  Qed.

  Lemma includedIn_trans f1 f2 f3 : includedIn f1 f2 -> includedIn f2 f3 -> includedIn f1 f3.
  Proof.  rewrite /includedIn. move => H1 H2. move => x y.
  auto. Qed.


  Definition splitsAs (f f1 f2: X -> option Y) :=
  forall x, 
  if f x is Some y
    then (f1 x = Some y /\ f2 x = None) 
      \/ (f2 x = Some y /\ f1 x = None)
    else f1 x = None /\ f2 x = None.

  Lemma splitsAsExtend f f1 f2 : splitsAs f f1 f2 -> f =1 extend f1 f2.
  Proof. rewrite /extend /splitsAs. move => H. move => x. 
  specialize (H x). case e: (f x) => [z |]; rewrite e in H. 
  + destruct H; by rewrite (proj2 H) (proj1 H). 
  + by rewrite (proj2 H) (proj1 H). Qed.

  Definition empFun : X -> option Y := fun _ => None.

  Lemma splitsAs_commutative f f1 f2 : splitsAs f f1 f2 -> splitsAs f f2 f1.
  Proof. rewrite /splitsAs. move => H x.  
  specialize (H x). case e: (f x) => [y |]; rewrite e in H. 
  case H; [by right | by left]. intuition.
  Qed. 

  Lemma splitsAs_f_emp_g f g : splitsAs f empFun g -> f =1 g. 
  Proof. rewrite /splitsAs. move => H x. specialize (H x).
  case e: (f x) => [z |]; rewrite e in H; [by destruct H; destruct H | intuition]. 
  Qed.

  Lemma splitsAs_f_g_emp f g : splitsAs f g empFun -> f =1 g. 
  Proof. rewrite /splitsAs. move => H x. specialize (H x). 
  case e: (f x) => [z |]; rewrite e in H; [by destruct H; destruct H | intuition]. 
  Qed.

  Lemma splitsAs_f_f_emp f : splitsAs f f empFun. 
  Proof. move => x. case (f x); intuition. Qed. 

  Lemma splitsAs_f_emp_f f : splitsAs f empFun f. 
  Proof. move => x. case (f x); intuition. Qed. 

  Lemma splitsAs_f_g_f f g : splitsAs f g f -> g =1 empFun.
  Proof. rewrite /splitsAs. move => H x. specialize (H x). 
  case e:(f x) => [y |]; rewrite e in H. by elim H; intuition. by intuition. 
  Qed. 

  Lemma splitsAs_f_f_g f g: splitsAs f f g -> g =1 empFun.
  Proof. rewrite /splitsAs. move => H x. specialize (H x). 
  case e:(f x) => [y |]; rewrite e in H. by elim H; intuition. by intuition.
  Qed. 


  Lemma splitsAsIncludedInSplitsAs f f1 f2 g :
    let g2 :=fun x => if f1 x is Some _ then None else if f2 x is Some y then Some y else g x
    in
    splitsAs f f1 f2 -> includedIn f g -> 
    splitsAs g f1 g2 /\ includedIn f2 g2.
  Proof. move => g2 fsplit fg. 
  rewrite /splitsAs in fsplit. rewrite /includedIn in fg. 
  split.
  rewrite /splitsAs => x. 
  specialize (fsplit x). 
  case E: (f x) => [z |]. 
  rewrite E in fsplit. specialize (fg _ _ E). rewrite fg. 
    destruct fsplit; destruct H as [H1 H2]. 
    + left. by rewrite /g2 H2 H1. 
    + right. by rewrite /g2 H2 H1. 
  rewrite E in fsplit. 
  destruct fsplit as [H1 H2]. case E2: (g x) => [y |]. right. by rewrite /g2 H1 H2. 
  by rewrite /g2 H1 H2. 

  rewrite /includedIn => x y E. 
  case E2: (f x) => [z |]. 
  specialize (fg _ _ E2). specialize (fsplit x). rewrite E2 in fsplit. 
  destruct fsplit; destruct H as [H1 H2]. 
  + congruence. rewrite /g2 H2 H1. congruence.  
  + specialize (fsplit x). rewrite E2 in fsplit. destruct fsplit as [H1 H2]. 
  congruence. 
  Qed. 

  Lemma splitsAs_associative f f1 f2 f3 f4 :
    let f5 := fun x => if f4 x is Some y then Some y else f1 x in
    splitsAs f f1 f2 -> splitsAs f2 f3 f4 ->
    splitsAs f f3 f5 /\ splitsAs f5 f1 f4.
  Proof. rewrite /splitsAs. move => H1 H2. 
  split. 
  * move => x. specialize (H1 x). specialize (H2 x). 
  case e: (f x) => [y |]. 
  + rewrite e in H1.
    case e': (f2 x) => [y' |]. 
    - rewrite e' in H2. 
      destruct H1. destruct H. congruence.
      destruct H2. destruct H. destruct H0.  
      rewrite H2. left. rewrite H in e'. rewrite e'. done. 
      destruct H. destruct H0. 
      rewrite H2. right. rewrite H0. rewrite H in e'. rewrite e'. done. 
    - rewrite e' in H2. destruct H2. destruct H1. right. rewrite H0. intuition. 
      destruct H1. rewrite e' in H1. done. 
  + rewrite e in H1. destruct H1. rewrite H0 in H2. destruct H2. rewrite H2. done. 
  * move => x. specialize (H1 x). specialize (H2 x). 
  case e: (f x) => [y |]. rewrite e in H1. 
  case e': (f2 x) => [y' |]. rewrite e' in H2. 
  destruct H2. destruct H. rewrite H0. 
  destruct H1. destruct H1. rewrite H1. left. done. 
  destruct H1. rewrite H2. done. 
  destruct H. rewrite H. 
  destruct H1. destruct H1. rewrite H2 in e'. done. right. destruct H1. done. 
  rewrite e' in H2. destruct H2. rewrite H0. 
  destruct H1. destruct H1. rewrite H1. left. done. 
  destruct H1. rewrite H2. done. 
  rewrite e in H1. destruct H1. rewrite H0 in H2. destruct H2. rewrite H2. 
  rewrite H. done. 
  Qed.


  Lemma splitsAsIncludes f f1 f2 : splitsAs f f1 f2 -> includedIn f1 f /\ includedIn f2 f.
  Proof. move => S. split; move => x y H; specialize (S x);
  case e: (f x) => [y' | ]; rewrite e in S; intuition; congruence. 
  Qed. 

  Lemma splitsAsExtendL s s1 s2 s3 s4 : splitsAs s s1 s2 -> splitsAs s2 s3 s4 ->
  splitsAs s (extend s1 s3) s4.
  Proof. move => H1 H2 x.  
  rewrite /splitsAs in H1, H2. specialize (H1 x). specialize (H2 x). rewrite /extend.
  case E1: (s x) => [y |]; rewrite E1 in H1. 
  + case E2: (s2 x) => [z |]; rewrite E2 in H2. 
    - case H2 => {H2} H2'. destruct H2' as [H2a H2b].
      case H1 => {H1} H1'; destruct H1' as [H1a H1b]. congruence.
      left. rewrite H2a. split;  congruence. 
    - case H1 => {H1} H1'; destruct H1' as [H1a H1b]. congruence. 
      destruct H2' as [H2a H2b]. rewrite H2b. right. split; congruence. 
    destruct H2 as [H2a H2b]. rewrite H2a. left. 
    case H1 => {H1} H1'; destruct H1' as [H1a H1b]. done. congruence. 
  + case E2: (s2 x) => [z |]; rewrite E2 in H2. 
    destruct H1 as [H1a H1b]. rewrite H1a. rewrite H1b in E2. done. 
    destruct H2 as [H2a H2b]. rewrite H2a. intuition. 
  Qed. 

End PFun.

  Hint Resolve splitsAsIncludes.
  Hint Resolve includedIn_refl.