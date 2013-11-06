(*===========================================================================
    Points-to predicates
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype tuple seq choice fintype.
Require Import bitsrep bitsops bitsprops bitsopsprops procstate.
Require Import monad reader SPred septac pfun cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Transparent ILFun_Ops.

(* The intended meaning of 
      (p -- q :-> v) s
   is that the memory from p inclusive to q exclusive represents the value v
*)
Class MemIs T := memIs: Cursor 32 -> Cursor 32 -> T -> SPred.
Notation "p '--' q ':->' x" := (memIs p q x) (at level 50, q at next level, no associativity).

Definition pointsTo {R} {_:MemIs R} p v := Exists q, memIs p q v.
Notation "p :-> x" := (pointsTo p x) (at level 50, no associativity). 

(* The default memIs predicate makes use of the Reader for the type:
     (p -- q :-> v) s
   if there exists a memory m such that reading m
   from p produces a new pointer q and s agrees with m in the range
   p inclusive to q exclusive
*)
Instance readerMemIs {R:readerType} : MemIs R := fun p q (v:R) (s:PState) =>
  exists m, read m p = readerOk v q /\ 
  forall p':BITS 32, inRange p q p' -> s Memory p' = Some (m p').

Lemma memComplete_read {R:readerType} (s s1: PState) p q (v:R):
  (p -- q :-> v) s1 ->
  stateIncludedIn s1 s ->
  read (memComplete s) p = readerOk v q.
Proof.
  move=> [m [Hread Hm]] Hs1. have Hgood := readP R m p. rewrite Hread in Hgood.
  case: Hgood => Hle. apply => p' Hp'.
  erewrite memComplete_inverse; [reflexivity|]. apply Hs1. by apply Hm.
Qed.

Lemma readerMemIs_leCursor {R: readerType} p q (v: R):
  p -- q :-> v |-- leCursor p q /\\ ltrue.
Proof.
  move=> s [m [Hok _]].
  split; last done. eapply read_leCursor. eassumption.
Qed.

Lemma memIsDWORD_next (p q:BITS _) (v:DWORD) s : (p -- q :-> v) s -> q = p+#4.
Proof. move => [m [H1 H2]]. apply: readDWORD_next H1. Qed.


(*---------------------------------------------------------------------------
   readerMemIs for bytes
  ---------------------------------------------------------------------------*)

Lemma memIsBYTE_next (p q:BITS _) (v:BYTE) s : (p -- q :-> v) s -> q = incB p.
Proof. move => [m [H1 H2]]. assert (NXT := readBYTE_next H1). rewrite /next in NXT.   
destruct (p == ones _); first done. congruence. Qed.

Lemma memIsBYTE_nextCursor (p:BITS _) q (v:BYTE) s : (p -- q :-> v) s -> q = next p.
Proof. move => [m [H1 H2]]. by apply (readBYTE_next H1). Qed.

Lemma memIsBYTE_next_entails (p:BITS _) q (v:BYTE) :
  p -- q :-> v |-- q = next p /\\ p -- q :-> v.
Proof.
  move=> s H. have HQ := memIsBYTE_nextCursor H. subst q. rewrite lentails_eq.
  ssplit; first done. by rewrite -lentails_eq. 
Qed.

(*---------------------------------------------------------------------------
   MemIs for pairs
  ---------------------------------------------------------------------------*)
Instance pairMemIs {X Y} {MX: MemIs X} {MY: MemIs Y} : MemIs (X*Y) :=
  fun p q (v: X*Y) => Exists p', p -- p' :-> (fst v) ** p' -- q :-> (snd v). 

(*---------------------------------------------------------------------------
   MemIs for sequences
  ---------------------------------------------------------------------------*)

Section SeqMemIs.
  Context {X} {MX: MemIs X}.

  Global Instance seqMemIs : MemIs (seq X) := fix F p q (vs: seq X) :=
    match vs with
    | v::vs => Exists p', p -- p' :-> v ** memIs (MemIs:=F) p' q vs
    | nil => p = q /\\ empSP
    end.

  Lemma seqMemIs_cat p q xs ys:
    p -- q :-> (xs ++ ys) -|- p -- q :-> (xs, ys).
  Proof.
    elim: xs p => [|x xs IHxs] p.
    - rewrite {2}/memIs /pairMemIs. rewrite /fst.
      rewrite {2}/memIs /seqMemIs. split.
      - apply lexistsR with p. ssplit => //. by apply empSPL.
      - sdestructs => _ <-. by apply empSPL.
    - rewrite /=. rewrite /memIs /seqMemIs /pairMemIs /fst /snd.
      setoid_rewrite IHxs.
      rewrite /memIs /pairMemIs /seqMemIs -/seqMemIs /fst /snd.
      split; sbazooka.
  Qed.
End SeqMemIs.

Notation "p -- q :[ R , n ]> vs" :=
  (memIs (MemIs := readerMemIs (R:=seq_readerType R n)) p q vs)
  (at level 50, q at next level, no associativity).

Lemma reader_seqMemIs {R:readerType} p q vs:
  p -- q :[R, size vs]> vs |-- p -- q :-> vs ** ltrue.
Proof.
  elim: vs p => [|v vs IHvs] p.
  - rewrite /memIs /memIs /readerMemIs. 
    move => s [m [H1 H2]]. case: H1 => [<-]. rewrite lentails_eq.
    rewrite /seqMemIs. ssplit; first done. by ssimpl.
  - rewrite /memIs /seqMemIs /readerMemIs.
    rewrite /read /getReader /seq_readerType.
    move=> s [m [Hread Heq]]. rewrite [size _]/= in Hread.
    case: (readSeqCons Hread) => pos' [Hreadv Hreadvs].
    rewrite lentails_eq. ssplit. instantiate (1:=pos').
    rewrite sepSPA. rewrite <-IHvs => {IHvs}. rewrite -lentails_eq.
    pose splitpred := fun f =>
      match f return fragDom f -> bool with
      | Memory => fun p' => inRange p pos' (mkCursor p')
      | _ => fun _ => false
      end.
    eexists. eexists. split; [apply (stateSplitsOn _ splitpred)|]. split.
    - exists m. split; [assumption|]. move=> p' Hrange.
      rewrite <-Heq.
      - rewrite /splitpred /restrictState. by rewrite Hrange.
      rewrite /inRange in Hrange. rewrite /inRange. apply/andP. split.
      - by move/andP: Hrange => [].
      eapply ltCursor_leCursor_trans.
      - move/andP: Hrange => [_ Hp'pos']. by apply Hp'pos'.
      clear -Hreadvs. destruct (readSeq R (size vs)) as [op Hop].
      simpl in Hreadvs. specialize (Hop m pos'). rewrite ->Hreadvs in Hop.
      tauto.
    - exists m. split; [assumption|]. move=> p' Hrange.
      rewrite <-Heq.
      - rewrite /splitpred /restrictState. rewrite /inRange negb_and.
        rewrite /inRange in Hrange. move/andP: Hrange => [Hrange _].
        rewrite leCursor_Ngt in Hrange. by rewrite Hrange orb_true_r.
      rewrite /inRange in Hrange. rewrite /inRange. apply/andP. split.
      - clear -Hreadv Hrange. destruct (@read R) as [op Hop].
        simpl in Hreadv. specialize (Hop m p). rewrite ->Hreadv in Hop.
        move/andP: Hrange => [Hrange _].
        eapply leCursor_trans; last apply Hrange. tauto.
      - by move/andP: Hrange => [].
Qed.

Lemma seqMemIs_reader {R:readerType} p q vs:
  p -- q :-> vs |-- p -- q :[R, size vs]> vs.
Proof.
  elim: vs p => [|v vs IHvs] p.
  - rewrite /memIs /seqMemIs /readerMemIs. sdestruct => <- {q}.
    move => s H. exists mem.initialMemory.
    split; first reflexivity. move=> p' Hp'. 
    move/andP: Hp' => [Hle Hlt].
    have Hpp := leCursor_ltCursor_trans Hle Hlt.
    rewrite ->negb_involutive_reverse in Hpp.
    rewrite -leCursor_Ngt in Hpp. rewrite leCursor_refl in Hpp. done.
  - rewrite /memIs /seqMemIs /readerMemIs.
    rewrite /read /getReader /seq_readerType.
    sdestruct => p'. rewrite ->IHvs => {IHvs}.
    move=> s [s1 [s2 [Hs [Hs1 Hs2]]]].
    have [Hsplit1 Hsplit2] := stateSplitsAsIncludes Hs => {Hs}.
    exists (memComplete s). split.
    - rewrite /= /bindRead_op /unitRead_op.
      erewrite ->memComplete_read; try eassumption.
      rewrite -[readSeq R (size vs)]/read.
      erewrite ->memComplete_read; try eassumption. reflexivity.
    move=> p'' Hp''.
    suff [v' Hv']: exists v', s Memory p'' = Some v'.
    - erewrite memComplete_inverse; eassumption.
    destruct (inRange_case (p':=p') Hp'').
    - rewrite ->lentails_eq in Hs1.
      lforwardR Hs1; first apply readerMemIs_leCursor.
      by destruct (Hs1 s1).
    - rewrite ->lentails_eq in Hs2.
      lforwardR Hs2; first apply readerMemIs_leCursor.
      by destruct (Hs2 s2).
    - destruct Hs1 as [m1 [_ Hm1]]. eexists.
      erewrite Hsplit1; first reflexivity. by apply Hm1.
    - destruct Hs2 as [m2 [_ Hm2]]. eexists.
      erewrite Hsplit2; first reflexivity. by apply Hm2.
Qed.

Lemma seqMemIs_nil (X:readerType) (p q:Cursor 32) : p -- q :-> ([::]:seq X) -|- p = q /\\ empSP.
Proof. 
rewrite /memIs/seqMemIs. 
split => // s H. 
Qed. 

Lemma seqMemIs_cons (X:readerType) (p q: Cursor 32) (v:X) (vs:seq X) : 
  p -- q :-> (v::vs) -|- Exists p', p -- p' :-> v ** p' -- q :-> vs.
Proof. by rewrite {1}/memIs/seqMemIs-/seqMemIs. Qed. 

Lemma pointsTo_consBYTE (p:DWORD) (b:BYTE) bs : p :-> (b::bs) -|- p :-> b ** (next p) :-> bs. 
Proof.
rewrite /pointsTo. 
split. 
+ sdestruct => q. rewrite seqMemIs_cons. sdestruct => q'.
rewrite -> memIsBYTE_next_entails. 
sdestructs => ->. sbazooka. 

+ sdestruct => q.
sdestruct => q'.  
apply lexistsR with q'. rewrite seqMemIs_cons. rewrite -> memIsBYTE_next_entails.
sdestructs => ->. sbazooka.  
Qed.

Lemma seq_BYTE_hwm (q: DWORD) (xs: seq BYTE):
  hwm 32 -- q :-> xs |-- lfalse.
Proof.
  case: xs => [|x xs].
  - rewrite /memIs /seqMemIs. by sdestruct.
  - rewrite /memIs /seqMemIs -/seqMemIs. sdestruct => p'.
    rewrite {1}/memIs /readerMemIs.
    move=> s [s1 [_ [_ [Hs1 _]]]]. case: Hs1 => m [Hm _].
    discriminate Hm.
Qed.

Lemma cons_BYTE_hwm (q: Cursor 32) (x:BYTE) (xs: seq BYTE):
  hwm 32 -- q :-> (x::xs) |-- lfalse.
Proof.
  - rewrite /memIs /seqMemIs-/seqMemIs. sdestruct => p'. 
    rewrite {1}/memIs /readerMemIs.
    move=> s [s1 [_ [_ [Hs1 _]]]]. case: Hs1 => m [Hm _].
    discriminate Hm.
Qed.



Lemma seq_BYTE_size (p q: DWORD) (vs: seq BYTE) :
  p -- q :-> vs |-- q = p +# size vs /\\ p -- q :-> vs.
Proof.
  elim: vs p => [|b bs IHbs] p.
  - rewrite /memIs /seqMemIs. sdestruct => [[<-]]. ssplits => //.
    by rewrite addB0.
  - rewrite /memIs /seqMemIs /size -/size. sdestruct => [[p'|]].
    - rewrite ->IHbs. sdestruct => Hq. rewrite ->memIsBYTE_next_entails.
      sdestruct => Hp'. subst. ssplit; last by sbazooka.
      clear IHbs.       replace (p +# (size bs).+1) with (incB p +# size bs).
      apply nextIsInc in Hp'. subst. rewrite <-addB_addn. rewrite -addB1. 
      by rewrite ->addB_addn. rewrite -addB1. rewrite <-addB_addn. by rewrite add1n.
    - rewrite ->seq_BYTE_hwm. rewrite lfalse_is_exists. sdestruct => [[]].
Qed.

Lemma seqMemIs_leCursor {R: readerType} (vs:seq R) : forall p q,
  p -- q :-> vs |-- leCursor p q /\\ ltrue.
Proof. move => p q. 
setoid_rewrite seqMemIs_reader. 
by rewrite -> readerMemIs_leCursor. 
Qed. 

Require Import bitsopsprops.
Lemma seqMemIsBYTE_addn (vs:seq BYTE) : forall m (p:DWORD), 
  m < 2^32 ->
  p -- (p +# m) :-> vs |-- size vs = m /\\ p -- (p+#m) :-> vs. 
Proof. 
  induction vs => m p BOUND.
+ rewrite seqMemIs_nil.
  sdestruct => EQ.
  have H: m = 0. 
  apply (addB0_inv (p:=p) BOUND). have: p = p +# m by congruence. by move => {1}->. 
  rewrite H addB0. sbazooka.  
+ rewrite seqMemIs_cons. 
  sdestruct => p'.
  rewrite -> memIsBYTE_next_entails. 
  sdestruct => ->. 

  destruct m.
  - rewrite addB0. rewrite -> seqMemIs_leCursor. rewrite leCursor_next. rewrite /ltCursor.
    rewrite ltB_nat. rewrite ltnn. rewrite lpropandF. rewrite sepSP_falseR.
    apply lfalseL. 
  - simpl (size _). apply ltnW in BOUND. 
    specialize (IHvs m (p+#1) BOUND). rewrite <- addB_addn in IHvs. rewrite add1n in IHvs.

    case E: (next p) => [q |].
    * symmetry in E. have NI := nextIsInc E. subst.  
      rewrite -> IHvs. sbazooka. congruence. 
    * rewrite -> seq_BYTE_hwm. rewrite sepSP_falseR. apply lfalseL.   
Qed. 

(*---------------------------------------------------------------------------
   memAny
  ---------------------------------------------------------------------------*)


Definition memAny p q := Exists bs: seq BYTE, p -- q :-> bs.

Lemma memAnyMerge p q r : memAny p q ** memAny q r |-- memAny p r. 
Proof.
  rewrite /memAny. sdestructs => s1 s2. 
  apply lexistsR with (s1 ++ s2). rewrite seqMemIs_cat. 
  rewrite {3}/memIs/pairMemIs. simpl fst. simpl snd.
  by apply lexistsR with q. 
Qed.

Lemma entails_memAnyNext (p: BITS 32) q : 
  ltCursor p q -> memAny p q |-- Exists b: BYTE, p :-> b ** memAny (next p) q.
Proof. 
  rewrite -leCursor_next. 
  move => LT. 
  rewrite /memAny. sdestruct => bs. 
  destruct bs.
  rewrite -> seqMemIs_nil.
  sdestructs => EQ.
  rewrite <- EQ in LT.
  rewrite leCursor_next in LT. 
  rewrite /ltCursor in LT. 
  rewrite ltB_nat in LT. by rewrite ltnn in LT. 

  rewrite seqMemIs_cons.
  sdestruct => q'. apply lexistsR with b.
  rewrite /pointsTo. 
  rewrite -> memIsBYTE_next_entails. sbazooka. subst. reflexivity. 
Qed. 

Lemma entails_memAnySplit p q r : 
  leCursor p q -> leCursor q r -> memAny p r |-- memAny p q ** memAny q r. 
Proof. move/LeCursorP. elim. 
  - move=> _. rewrite <-empSPL at 1. cancel2; []. apply lexistsR with nil.
    apply lpropandR; first constructor. reflexivity.
  - move => {q} q Hpq Hind Hqr. rewrite leCursor_next in Hqr.
    etransitivity; [apply Hind|]; first exact: leCursor_weaken.
    rewrite ->entails_memAnyNext; last done.
    sdestruct => b. ssimpl.
    rewrite {1}/memAny. sdestructs => s.
    rewrite /memAny. apply lexistsR with (s ++ [:: b]).
    rewrite seqMemIs_cat. rewrite /memIs/pairMemIs. simpl fst. simpl snd. 
    apply lexistsR with q. ssimpl. 
    rewrite /memIs/seqMemIs.
    apply lexistsR with (next q). rewrite seqMemIs_nil. ssimpl.
    rewrite /pointsTo. sdestruct => q'. rewrite -> memIsBYTE_next_entails.
    sdestructs => ->. by ssimpl. 
Qed.

Corollary memAnySplit p q r : 
  leCursor p q -> leCursor q r -> memAny p r -|- memAny p q ** memAny q r. 
Proof. move => H1 H2. 
split. by apply entails_memAnySplit. by apply memAnyMerge. 
Qed. 

Lemma memAnyLe p q : memAny p q |-- leCursor p q /\\ ltrue.
Proof. rewrite /memAny. sdestruct => bs. apply seqMemIs_leCursor. Qed. 

(* Without this, the Qed check after memAnySplitAdd loops forever. *)
Local Opaque leB.

Corollary memAnySplitAdd (p:DWORD) m1 m2 : 
  m1 + m2 < 2 ^ 32 ->
  memAny p (p+#(m1+m2)) -|- memAny p (p+#m1) ** memAny (p+#m1) (p+#(m1+m2)). 
Proof. move => BOUND. 
split. 
+ move => s H. destruct (memAnyLe H) as [MAL _]. rewrite /leCursor in MAL. 
apply entails_memAnySplit.  
rewrite -{1}(addB0 p). apply (leB_bounded_weaken BOUND) => //. apply leq_addr. 
apply (leB_bounded_weaken BOUND) => //. apply leq_addr. done. 

+ apply memAnyMerge. 
Qed.

