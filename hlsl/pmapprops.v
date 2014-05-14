(*===========================================================================
  Properties of partial finite maps
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
Require Import tuplehelp bitsrep bitsprops pmap.
Require Export update.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Equality.
Lemma existsVal {n} : 
  forall {V} (m:NEPMAP V n), exists v, exists p: BITS n, lookupNE m p = Some v.
Proof. induction n. 
+ dependent destruction m. by exists v, (nil_tuple _). 
+ dependent destruction m. 
  destruct (IHn _ m1) as [v [p H]]. exists v, (cons_tuple false p). by rewrite /=beheadCons. 
  destruct (IHn _ m) as [v [p H]]. exists v, (cons_tuple false p). by rewrite /=beheadCons. 
  destruct (IHn _ m) as [v [p H]]. exists v, (cons_tuple true p). by rewrite /=beheadCons. 
Qed. 

Lemma extensional_NEPMAP {n} : 
  forall {V} (m1 m2: NEPMAP V n), (forall x, lookupNE m1 x = lookupNE m2 x) -> m1 = m2.
Proof. induction n => V m1 m2 H. 
  + dependent destruction m1.  dependent destruction m2. 
    specialize (H (nil_tuple _)). simpl in H. congruence. 
  + dependent destruction m1.  
    - dependent destruction m2. 
      * simpl in H. rewrite (IHn _ m1_1 m2_1). rewrite (IHn _ m1_2 m2_2). done. 
        move => x. specialize (H (cons_tuple true x)). by rewrite beheadCons in H. 
        move => x. specialize (H (cons_tuple false x)). by rewrite beheadCons in H.
      * destruct (existsVal m1_2) as [v [p H1]]. 
        specialize (H (cons_tuple true p)). simpl in H. rewrite beheadCons in H. rewrite H in H1. inversion H1.
      * destruct (existsVal m1_1) as [v [p H1]]. 
        specialize (H (cons_tuple false p)). simpl in H. rewrite beheadCons in H. rewrite H in H1. inversion H1.

    - dependent destruction m2. 
      * destruct (existsVal m2_2) as [v [p H1]]. 
        specialize (H (cons_tuple true p)). simpl in H. rewrite beheadCons in H. rewrite H1 in H. inversion H.
      * simpl in H. rewrite (IHn _ m1 m2). done. 
        move => p. specialize (H (cons_tuple false p)). simpl in H. by rewrite beheadCons in H.
      * simpl in H. 
        destruct (existsVal m1) as [v [p H1]]. 
        specialize (H (cons_tuple false p)). simpl in H. rewrite beheadCons in H. rewrite H in H1. inversion H1.

    - dependent destruction m2. 
      * destruct (existsVal m2_1) as [v [p H1]]. 
        specialize (H (cons_tuple false p)). simpl in H. rewrite beheadCons in H. rewrite H1 in H. inversion H.
      * simpl in H. 
        destruct (existsVal m2) as [v [p H1]]. 
        specialize (H (cons_tuple false p)). simpl in H. rewrite beheadCons in H. rewrite H1 in H. inversion H.
      * simpl in H. rewrite (IHn _ m1 m2). done. 
        move => p. specialize (H (cons_tuple true p)). simpl in H. by rewrite beheadCons in H.
Qed. 

Lemma extensional_PMAP {n V} :
  forall (m1 m2: PMAP V n), (forall x, m1 x = m2 x) -> m1 = m2.
Proof. case => [a1 |]. 
  case => [a2 |]. 
    move => H. by rewrite (extensional_NEPMAP H).  
    move => H. simpl in H. destruct (existsVal a1) as [v [p H1]]. by rewrite (H p) in H1. 
    case => [a2 |]. 
    move => H. simpl in H. destruct (existsVal a2) as [v [p H1]]. by rewrite -(H p) in H1. 
    move => H. done. 
Qed. 


Lemma singleNEThenLookup {n V} :
  forall (p: BITS n) (v:V), lookupNE (singleNE p v) p = Some v.
Proof. induction n => p v. 
+ done. 
+ case/tupleP: p => b p'. case b; by simpl. 
Qed.

Lemma updateNEThenLookup {n V} : 
  forall (m: NEPMAP V n) (p: BITS n) (v: V),
  lookupNE (updateNE m p v) p = Some v.
Proof. induction m => p v0.
  + done.
  + simpl. case e: (thead p); simpl; rewrite e. by rewrite IHm2. by rewrite IHm1.
  + simpl. case e: (thead p); simpl; rewrite e. by rewrite singleNEThenLookup. by rewrite IHm. 
  + simpl. case e: (thead p); simpl; rewrite e. done.
  + by rewrite singleNEThenLookup.  
Qed. 

Open Scope update_scope.
Lemma updateThenLookup {n V} : 
  forall (m: PMAP V n) (p: BITS n) (v: V),
  (m !p:=v) p = Some v.
Proof. case => *; simpl. by rewrite updateNEThenLookup. by rewrite singleNEThenLookup. Qed.    

Lemma tlneq {n} {h} (t t': BITS n) : cons_tuple h t <> cons_tuple h t' -> t <> t'. 
Proof. move => neq. move => H. by rewrite H in neq. Qed. 

Lemma singleNEThenLookupOther {n V} : 
  forall (p q: BITS n) (v:V),
   p<>q -> lookupNE (singleNE p v) q = None.
Proof.
  induction n.
    + move => p q v pq. case: pq. by rewrite (tuple0 p) (tuple0 q). 
    + case/tupleP => b p'. case/tupleP => b' q'. 
      move => v pq. simpl. rewrite beheadCons.
      destruct b. 
      - destruct b'. simpl. rewrite beheadCons. apply IHn. apply: tlneq pq. done.
      - destruct b'. done. simpl. rewrite beheadCons. apply IHn. apply: tlneq pq. 
Qed. 

(* test
Definition m :PMAP DWORD 32 := EmptyPMap !#5:=#23 !#6:=#123 !#7:=#213 !#8:= #100 !#1234:=#121. 
*)

Fixpoint nodesNEaux {n V} (c:nat) (m: NEPMAP n V) :=
  match m with
  | VAL _ => c.+1
  | LSPLIT _ m => nodesNEaux (c.+1) m
  | RSPLIT _ m => nodesNEaux (c.+1) m
  | SPLIT _ m1 m2 => nodesNEaux (nodesNEaux (c.+1) m1) m2
  end.
Definition nodes {n V} (m: PMAP n V) := 
  match m with
  | EmptyPMap => 0
  | PMap m => nodesNEaux 0 m
  end.

Lemma updateNEThenLookupDistinct {n V} :
  forall (m: NEPMAP V n) (p q: BITS n) (v: V),
  p <> q -> lookupNE (updateNE m p v) q = lookupNE m q.
Proof.
induction m.  
+ simpl. move => p q. rewrite (tuple0 p) (tuple0 q). by intuition.  
+ simpl. case/tupleP => b p. case: b.  
  case/tupleP => b' q. 
  case: b'. 
    move => v pq. simpl. rewrite !beheadCons. rewrite IHm2. done. apply: tlneq pq.
    done. 
  case/tupleP => b' q. 
  case: b'. 
    done. 
    move => v pq. simpl. rewrite !beheadCons. rewrite IHm1. done. apply: tlneq pq.
+ simpl. case/tupleP => b p. case: b.  
  case/tupleP => b' q.
    move => v pq. simpl. rewrite !beheadCons !theadCons. 
    destruct b'. apply singleNEThenLookupOther. 
    apply: tlneq pq. 
    done. 
  case/tupleP => b' q. 
    move => v pq. simpl. rewrite !beheadCons !theadCons. 
    destruct b'. done. 
    rewrite IHm. done. apply: tlneq pq. 
+ simpl. case/tupleP => b p. case/tupleP => b' q. 
  move => v pq. rewrite !theadCons. rewrite !beheadCons.
  destruct b'. destruct b. simpl. rewrite beheadCons. rewrite IHm. done. apply: tlneq pq. 
  simpl. by rewrite beheadCons.
  destruct b.  done. simpl. rewrite beheadCons. 
  rewrite singleNEThenLookupOther. done. apply: tlneq pq. 
Qed. 

Lemma updateThenLookupDistinct {n V} :
  forall (m: PMAP V n) (p q: BITS n) (v: V),
  p <> q -> (m !p:=v) q = m q.
Proof. 
case.  
move => m p q v pq. 
simpl. by rewrite updateNEThenLookupDistinct. 
simpl. move => p q v pq. by rewrite singleNEThenLookupOther.
Qed.

Instance PMapUpdate {n} V : Update (PMAP V n) (BITS n) V.
  apply Build_Update. 
  (* update same key *)
  move => m k v w. apply extensional_PMAP => p.
  case e: (p==k). 
  + rewrite (eqP e). by rewrite !updateThenLookup. 
  + assert (k<>p). intro E. rewrite E in e. rewrite eq_refl in e. inversion e. rewrite !updateThenLookupDistinct; done. 
  (* update different keys *)
  move => m k l v w kl. 
  apply extensional_PMAP => p.     
  case e: (p==k). 
  + rewrite (eqP e). rewrite updateThenLookup. rewrite updateThenLookupDistinct. by rewrite updateThenLookup. intuition. 
  + assert (k<>p). intro E. rewrite E in e. rewrite eq_refl in e. inversion e. 
    case e': (p==l).
    - rewrite (eqP e'). rewrite updateThenLookup. rewrite updateThenLookupDistinct. by rewrite updateThenLookup. intuition. 
    - assert (l<>p). intro E. rewrite E in e'. rewrite eq_refl in e'. inversion e'. 
      rewrite !updateThenLookupDistinct. done. intuition. done.  done. done. 
  Qed.

Lemma fillNE_lookup V n (f: BITS n -> V) k:
  lookupNE (fillNE f) k = Some (f k).
Proof.
  move: f k. elim: n => [|n IHn] f k.
  - rewrite /fillNE /lookupNE. f_equal. f_equal. apply trivialBits.
  - rewrite /fillNE -/fillNE /lookupNE; fold (@lookupNE V n).
    case Hsplit: (splitlsb k) => [p []].
    - rewrite IHn. rewrite /consBfun.
      replace (consB true p) with (joinlsb (p,true)) by done. rewrite -Hsplit. 
      by rewrite splitlsbK. 
    - rewrite IHn. rewrite /consBfun.
      replace (consB false p) with (joinlsb (p,false)) by done. rewrite -Hsplit. 
      by rewrite splitlsbK. 
Qed.

Lemma fill_lookup n V (f: BITS n -> V) k:
  (fill f) k = Some (f k).
Proof. rewrite /fill /PMapToFun /lookup. apply fillNE_lookup. Qed.

Lemma splitlsb_consBfun {A} {n} p' p b (f: BITS n.+1 -> A):
  splitlsb p' = (p, b) ->
  consBfun b f p = f p'.
Proof.
  move=> Hsplit. rewrite /consBfun.
  replace (consB b p) with (joinlsb (p,b)) by done. by rewrite -Hsplit splitlsbK. 
Qed.

Lemma pmap_of_lookup n V (f: BITS n -> option V) k:
  (pmap_of f) k = f k.
Proof.
  rewrite /PMapToFun. move: f k. elim: n => [|n IHn] f k.
  - rewrite /pmap_of /lookupNE. case Hf: (f (zero 0)) => [v|].
    - rewrite /lookup /lookupNE. rewrite <-Hf.
      f_equal. apply trivialBits.
    - rewrite /lookup -Hf. f_equal. apply trivialBits.
  - rewrite /pmap_of; fold (@pmap_of V n). rewrite /lookup.
    (* This is a copy-paste mess. Maybe it can be improved, but the number of
       cases does actually correspond to the number of cases in the functions
       involved. *)
    case Hleft: (pmap_of (consBfun false f)) => [ml|];
      case Hright: (pmap_of (consBfun true f)) => [mr|].
    - rewrite /lookupNE; fold (@lookupNE V n).
      case Hsplit: (splitlsb k) => [p []].
      - specialize (IHn (consBfun true f) p).
        rewrite /lookup Hright in IHn. rewrite IHn. exact: splitlsb_consBfun.
      - specialize (IHn (consBfun false f) p).
        rewrite /lookup Hleft in IHn. rewrite IHn. exact: splitlsb_consBfun.
    - rewrite /lookupNE; fold (@lookupNE V n).
      case Hsplit: (splitlsb k) => [p []].
      - specialize (IHn (consBfun true f) p).
        rewrite /lookup Hright in IHn. rewrite IHn. exact: splitlsb_consBfun.
      - specialize (IHn (consBfun false f) p).
        rewrite /lookup Hleft in IHn. rewrite IHn. exact: splitlsb_consBfun.
    - rewrite /lookupNE; fold (@lookupNE V n).
      case Hsplit: (splitlsb k) => [p []].
      - specialize (IHn (consBfun true f) p).
        rewrite /lookup Hright in IHn. rewrite IHn. exact: splitlsb_consBfun.
      - specialize (IHn (consBfun false f) p).
        rewrite /lookup Hleft in IHn. rewrite IHn. exact: splitlsb_consBfun.
    - case Hsplit: (splitlsb k) => [p []].
      - specialize (IHn (consBfun true f) p).
        rewrite /lookup Hright in IHn. rewrite IHn. exact: splitlsb_consBfun.
      - specialize (IHn (consBfun false f) p).
        rewrite /lookup Hleft in IHn. rewrite IHn. exact: splitlsb_consBfun.
Qed.

