(*===========================================================================
    Points-to predicates
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype tuple seq choice fintype.
Require Import bitsrep bitsops bitsprops bitsopsprops procstate.
Require Import monad reader writer roundtrip SPred septac pfun cursor iltac.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Transparent ILFun_Ops.

(*--------------------------------------------------------------------------- 
   The intended meaning of 
      p -- q :-> v
   is that the memory from p inclusive to q exclusive represents the value v.
   Points-to is a derived notion:
      p :-> v   
   iff there exists some q such that p -- q :-> v. 
  ---------------------------------------------------------------------------*)
Class MemIs T := memIs: Cursor 32 -> Cursor 32 -> T -> SPred.
Notation "p '--' q ':->' x" := (memIs p q x) (at level 50, q at next level, no associativity).

Definition pointsTo {R} {_:MemIs R} p v := Exists q, memIs p q v.
Notation "p :-> ? : t" := (Exists x:t, pointsTo p x)(at level 50, no associativity).
Notation "p :-> x" := (pointsTo p x) (at level 50, no associativity). 

(*--------------------------------------------------------------------------- 
   We can interpret reader terms purely logically, using the primitive 
   byteIs predicate and separating conjunction.
  ---------------------------------------------------------------------------*)
Fixpoint interpReader T (rt:Reader T) (p q: Cursor 32) (v: T) :=
  match rt with
  | readerRetn x => 
    v = x /\\ p = q /\\ empSP

  | readerNext rd => 
    (* We can't read beyond the last byte of memory! *)
    if p is mkCursor p' 
    then Exists b, byteIs p' b ** interpReader (rd b) (next p') q v
    else lfalse

  | readerCursor rd => 
    interpReader (rd p) p q v
  end.

Lemma interpReader_entails_leCursor T (rt: Reader T) : 
  forall p q v, interpReader rt p q v |-- leCursor p q /\\ interpReader rt p q v.
Proof. induction rt => p q v; rewrite /interpReader-/interpReader.
- sdestructs => -> ->. sbazooka. by rewrite leCursor_refl. 
- destruct p => //. sdestructs => byte. rewrite -> H. 
  rewrite leCursor_next. sdestructs => H2. sbazooka. by rewrite leCursor_weaken. 
- destruct p => //.   
Qed.

Lemma interpReader_nonHwm T (rt: Reader T) :
  forall (c:Cursor 32) (q:DWORD) v, interpReader rt c q v |-- Exists p: DWORD, c = mkCursor p /\\ interpReader rt c q v.
Proof. induction rt => c q v; rewrite /interpReader-/interpReader.
- sdestructs => -> ->. sbazooka. 
- case E: c => [b |]. sdestructs => byte. rewrite -> H. 
  sdestructs => p. move ->. sbazooka.  
  done. 
apply H.   
Qed. 

Lemma interpReader_retn T (v w:T) p q: 
  interpReader (retn v) p q w -|- p = q /\\ v = w /\\ empSP.
Proof. simpl (retn _). rewrite /interpReader-/interpReader. 
split; sdestructs => -> ->; sbazooka. 
Qed. 

Lemma interpReader_bind T1 T2 (r1: Reader T1) : forall (r2: T1 -> Reader T2) w p q,
  interpReader (readerBind r1 r2) p q w -|-
  Exists p', Exists v, interpReader r1 p p' v ** interpReader (r2 v) p' q w.
Proof. induction r1 => r2 w p q. 
+ rewrite /readerBind/interpReader-/interpReader. split.
  * sbazooka. 
  * sdestructs => p' v -> ->. sbazooka. 
+ simpl readerBind. rewrite {1}/interpReader-/interpReader. 
  destruct p.  
  * split; rewrite /interpReader-/interpReader.
      sdestructs => byte. rewrite H. sbazooka. 
      sdestructs => p' v byte. setoid_rewrite H. sbazooka. 
  * split; rewrite /interpReader-/interpReader. 
      done. 
      sbazooka.
(* readerCursor *)
  rewrite /readerBind-/readerBind/interpReader-/interpReader. 
  destruct p => //. 
Qed.  

Definition interpReaderFixedLength T (r: Reader T) n :=
  forall p q v, interpReader r p q v |-- subCursor q p = n /\\ interpReader r p q v.

(*--------------------------------------------------------------------------- 
  Typically we use interpReader to instantiate MemIs
  ---------------------------------------------------------------------------*)
Instance readerMemIs R {r:Reader R} : MemIs R := interpReader readNext. 

(* Some useful properties of p -- q :-> v for readers *)
Corollary readerMemIs_entails_leCursor R {r: Reader R} p q (v: R):
  p -- q :-> v |-- leCursor p q /\\ p -- q :-> v. 
Proof. rewrite /memIs/readerMemIs. by rewrite <- interpReader_entails_leCursor. Qed. 

Lemma readerMemIs_nonHwm R {r: Reader R} (p: Cursor 32) (q:DWORD) (v: R):
  p -- q :-> v |-- Exists p':DWORD, p = mkCursor p' /\\ p -- q :-> v. 
Proof. rewrite /memIs/readerMemIs. by rewrite -> interpReader_nonHwm. Qed. 

Lemma interpReaderPair T1 T2 (r1: Reader T1) (r2: Reader T2) v1 v2 p r :
  Exists q, interpReader r1 p q v1 ** interpReader r2 q r v2 -|- 
  interpReader (let! x1 = r1; let! x2 = r2; retn (x1, x2)) p r (v1,v2).
Proof. rewrite interpReader_bind.
split. 
+ sdestructs => q. sbazooka. rewrite interpReader_bind. sbazooka.
+ sdestructs => p' v. rewrite interpReader_bind. sdestructs => p'' v'.
  rewrite interpReader_retn. sdestructs => -> EQ. inversion EQ. subst. sbazooka. 
Qed. 

(*---------------------------------------------------------------------------
   readerMemIs for bytes
  ---------------------------------------------------------------------------*)

Lemma interpReader_bindBYTE T (r: BYTE -> Reader T) w (p:DWORD) (q:Cursor 32) :
  interpReader (readerBind readNext r) p q w -|-
  Exists b:BYTE, byteIs p b ** interpReader (r b) (next p) q w.
Proof. 
rewrite interpReader_bind/readNext/readBYTE/interpReader-/interpReader.
split. sbazooka. subst. by ssimpl. sbazooka. 
Qed. 

Lemma interpReader_bindBYTE_hwm T (r: BYTE -> Reader T) w (q:Cursor 32) :
  interpReader (readerBind readNext r) (hwm _) q w -|-
  lfalse.
Proof. 
rewrite interpReader_bind/readNext/readBYTE/interpReader-/interpReader.
split => //. sbazooka.  
Qed.  

Lemma memIsBYTE_nextCursor (p:BITS _) q (v:BYTE) s : (p -- q :-> v) s -> q = next p.
Proof. move => [b [s1 [s2 [H1 [H2 [H3 [H4 H5]]]]]]]. done. Qed. 

Lemma memIsBYTE_next_entails (p:BITS _) q (v:BYTE) :
  p -- q :-> v |-- q = next p /\\ p -- q :-> v.
Proof.
  move=> s H. have HQ := memIsBYTE_nextCursor H. subst q. rewrite lentails_eq.
  ssplit; first done. by rewrite -lentails_eq. 
Qed.

(* In fact p :-> b for b:BYTE is just a long-winded way of saying byteIs p b *)
Lemma pointsToBYTE_byteIs (p:DWORD) b : p :-> b -|- byteIs p b.
Proof. 
rewrite /pointsTo. 
rewrite /memIs/readerMemIs/readNext/readBYTE/interpReader. 
split. sdestructs => c b' ->. move => EQ. by ssimpl.
sbazooka.   
Qed. 

Lemma interpReaderFixedLengthBYTE : interpReaderFixedLength (readNext (T:=BYTE)) #1. 
Proof. move => p q v.
rewrite /readNext/readBYTE/interpReader. 
case E: p => [p' |]. sdestructs => c -> H2. sbazooka. clear E.  
rewrite -H2. by rewrite subCursor_next. done. 
Qed. 

(*---------------------------------------------------------------------------
   MemIs for pairs and sequences
  ---------------------------------------------------------------------------*)
Section PairMemIs.

  Context {X Y} {MX: MemIs X} {MY: MemIs Y}.

  Global Instance pairMemIs : MemIs (X*Y) :=
  fun p q (v: X*Y) => Exists p', p -- p' :-> (fst v) ** p' -- q :-> (snd v). 

End PairMemIs. 

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
      split; sbazooka; reflexivity.
  Qed.

  Lemma seqMemIs_nil (p q:Cursor 32): 
    p -- q :-> ([::]:seq X) -|- p = q /\\ empSP.
  Proof. by rewrite /memIs/seqMemIs. Qed. 

  Lemma seqMemIs_cons (p q: Cursor 32) (v:X) (vs:seq X) : 
    p -- q :-> (v::vs) -|- Exists p', p -- p' :-> v ** p' -- q :-> vs.
  Proof. by rewrite {1}/memIs/seqMemIs-/seqMemIs. Qed. 


End SeqMemIs.

  Lemma readerSeqMemIs_nonHwm R {r: Reader R} (vs: seq R) : forall (p: Cursor 32) (q:DWORD),
    p -- q :-> vs |-- Exists p':DWORD, p = mkCursor p' /\\ p -- q :-> vs. 
  Proof. induction vs => p q. rewrite /memIs/readerMemIs/seqMemIs. 
    case E: p => [p' |]. sbazooka. subst. sdestruct => H. rewrite H.  sbazooka. 
    rewrite /memIs/seqMemIs. sdestruct => p0. 
    case E: p0 => [p0' |]. specialize (IHvs p0' q). setoid_rewrite IHvs. 
    case E': p => [p' |]. subst.  sbazooka. set C := p0' -- q :-> vs.  sbazooka.
    subst. setoid_rewrite readerMemIs_nonHwm. sdestruct => d. sdestruct => H. discriminate H.
    specialize (IHvs (hwm 32) q). setoid_rewrite IHvs .
    sdestruct => d'. sdestruct => E''. discriminate E''. 
  Qed.     

  Lemma seqMemIs_entails_leCursor R (_: Reader R) (vs:seq R) : forall p q,
    p -- q :-> vs |-- leCursor p q /\\ ltrue.
  Proof. induction vs => p q.
  setoid_rewrite seqMemIs_nil. apply lpropandL => ->. by rewrite leCursor_refl. 
  setoid_rewrite seqMemIs_cons. apply lexistsL => p'.
  setoid_rewrite IHvs. setoid_rewrite readerMemIs_entails_leCursor. sdestructs => H1 H2. 
  by rewrite (leCursor_trans H1 H2). 
  Qed. 

Lemma memIs_consBYTE (p:DWORD) q (b:BYTE) bs : p -- q :-> (b::bs) -|- p :-> b ** (next p) -- q :-> bs. 
Proof.
split. 
  setoid_rewrite seqMemIs_cons. sdestruct => q'.
  rewrite -> memIsBYTE_next_entails. 
  sdestructs => ->. rewrite /pointsTo. sbazooka. 

  rewrite /pointsTo. sdestructs => p'. rewrite -> memIsBYTE_next_entails.    
  setoid_rewrite seqMemIs_cons. ssplits.
  sdestructs => q'. subst. by ssimpl.
Qed.

Lemma pointsTo_consBYTE (p:DWORD) (b:BYTE) bs : p :-> (b::bs) -|- p :-> b ** (next p) :-> bs. 
Proof.
rewrite /pointsTo. 
split. 
  sdestruct => q. setoid_rewrite seqMemIs_cons. sdestruct => q'.
  rewrite -> memIsBYTE_next_entails. 
  sdestructs => ->. sbazooka. 

  sdestruct => q.
  sdestruct => q'.  
  apply lexistsR with q'. 
  setoid_rewrite seqMemIs_cons. rewrite -> memIsBYTE_next_entails.
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
Qed.

Lemma cons_BYTE_hwm (q: Cursor 32) (x:BYTE) (xs: seq BYTE):
  hwm 32 -- q :-> (x::xs) |-- lfalse.
Proof.
  - rewrite /memIs /seqMemIs-/seqMemIs. sdestruct => p'. 
    rewrite {1}/memIs /readerMemIs.
    move=> s [s1 [_ [_ [Hs1 _]]]]. case: Hs1 => m [Hm _].
Qed.


Lemma seq_BYTE_size (p q: DWORD) (vs: seq BYTE) :
  p -- q :-> vs |-- q = p +# size vs /\\ p -- q :-> vs.
Proof.
  elim: vs p => [|b bs IHbs] p.
  - rewrite /memIs /seqMemIs. sdestruct => [[<-]]. ssplits => //.
    by rewrite addB0.
  - rewrite /memIs /seqMemIs -/seqMemIs /size -/size. sdestruct => [[p'|]].
    - rewrite ->IHbs. sdestruct => Hq. rewrite ->memIsBYTE_next_entails.
      sdestruct => Hp'. symmetry in Hp'. subst. ssplit; last by sbazooka.
      clear IHbs. replace (p +# (size bs).+1) with (incB p +# size bs).
      apply nextIsInc in Hp'. subst. rewrite <-addB_addn. rewrite -addB1. 
      by rewrite ->addB_addn. rewrite -addB1. rewrite <-addB_addn. by rewrite add1n.
    - rewrite ->seq_BYTE_hwm. rewrite lfalse_is_exists. sdestruct => [[]].
Qed.

Lemma seqMemIsBYTE_addn (vs:seq BYTE) : forall m (p:DWORD), 
  m < 2^32 ->
  p -- (p+#m) :-> vs |-- 
  size vs = m /\\ p -- (p+#m) :-> vs. 
Proof. 
  induction vs => m p BOUND.
(* vs is nil *)
  setoid_rewrite seqMemIs_nil.
  sdestruct => EQ.
  have H: m = 0. 
  apply (addB0_inv (p:=p) BOUND). have: p = p +# m by congruence. by move => {1}->. 
  rewrite H addB0. sbazooka.  
(* vs is non-nil *)
  setoid_rewrite seqMemIs_cons. 
  sdestruct => p'.
  rewrite -> memIsBYTE_next_entails. 
  sdestruct => ->. 

  destruct m.
    rewrite addB0. rewrite -> seqMemIs_entails_leCursor. 
    rewrite leCursor_next /ltCursor.
    rewrite ltB_nat ltnn.  rewrite lpropandF. by ssimpl.  
    simpl (size _). apply ltnW in BOUND. 
    specialize (IHvs m (p+#1) BOUND). rewrite <- addB_addn in IHvs. rewrite add1n in IHvs.

    case E: (next p) => [q |].
      symmetry in E. have NI := nextIsInc (sym_equal E). subst.  
      rewrite -> IHvs. sbazooka.  congruence. 
      rewrite -> seq_BYTE_hwm. by ssimpl. 
Qed. 

Lemma pointsToNil (p:Cursor 32) : empSP -|- p :-> ([::]: seq BYTE). 
Proof. 
rewrite /pointsTo/memIs. 
split.

ssplit.
sbazooka.
sdestructs => q.
rewrite /seqMemIs. 
sdestructs => //.
Qed. 

Lemma hwmPointsTo_consBYTE (x:BYTE) (xs: seq BYTE) : hwm _ :-> (x::xs) -|- lfalse. 
Proof. split => //. 
rewrite /pointsTo/memIs/seqMemIs. 
sdestructs => p q. rewrite {1}/memIs/readerMemIs/readNext/readBYTE.
(* should be able to use sbazooka *)
rewrite /interpReader. 
by ssimpl. 
Qed. 

Fixpoint catBYTES (xs: seq BYTE) : BITS (size xs * 8) :=
  if xs is x::xs return BITS (size xs * 8) then catBYTES xs ## x else nilB. 

Lemma pointsToDWORD_BYTES (p:DWORD) (b0 b1 b2 b3:BYTE):
  p :-> [::b0;b1;b2;b3] -|- p :-> (b3 ## b2 ## b1 ## b0).
Proof.
rewrite {2}/pointsTo.
rewrite /memIs/readerMemIs/readNext/readDWORD.
split => //. 

ssplit. 

rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. ssplit.
case E: (next p) => [p' |].
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. ssplit. 
case E': (next p') => [p'' |].
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. ssplit. 
case E'': (next p'') => [p''' |].
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. ssplit. 
rewrite <-pointsToNil. setoid_rewrite interpReader_retn.
rewrite /bytesToDWORD.
sbazooka.
have H:= (nextIsInc E). 
have H':= (nextIsInc E'). 
have H'':= (nextIsInc E'').
subst. reflexivity.

by (rewrite interpReader_bindBYTE_hwm hwmPointsTo_consBYTE).
by (rewrite interpReader_bindBYTE_hwm hwmPointsTo_consBYTE). 
by (rewrite interpReader_bindBYTE_hwm hwmPointsTo_consBYTE). 

sdestruct => q. 
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. 
sdestruct => b0'. 
case E: (next p) => [p' |]. 
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. 
sdestruct => b1'. 
case E': (next p') => [p'' |]. 
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. 
sdestruct => b2'. 
case E'': (next p'') => [p''' |]. 
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. 
sdestruct => b3'. 
rewrite interpReader_retn.
rewrite <- pointsToNil.
rewrite /bytesToDWORD.
sdestructs => H1 H2. ssimpl. 
destruct (catB_inj (n1:=8) (n2:=24) H2) as [H2a H2']. 
destruct (catB_inj (n1:=8) (n2:=16) H2') as [H2b H2'']. 
destruct (catB_inj (n1:=8) (n2:=8) H2'') as [H2c H2d]. 
subst. by ssimpl.  

rewrite interpReader_bindBYTE_hwm. by ssimpl. 
rewrite interpReader_bindBYTE_hwm. by ssimpl. 
rewrite interpReader_bindBYTE_hwm. by ssimpl. 
Qed. 

Corollary pointsToDWORD_asBYTES (d: DWORD) (p:DWORD):
  let: (b3,b2,b1,b0) := split4 8 8 8 8 d in
  p :-> [::b0;b1;b2;b3] -|- p :-> d.
Proof.
have SE := @split4eta 8 8 8 8 d. 
elim E: (split4 8 8 8 8 d) => [[[b3 b2] b1] b0]. 
rewrite E in SE. rewrite -SE. apply pointsToDWORD_BYTES. 
Qed. 


Lemma memIsDWORD_rangeGen (p c: DWORD) (q:Cursor 32) :
  p -- q :-> c |-- q = next (p +# 3) /\\ p -- q :-> c.
Proof.
rewrite {1}/memIs/readerMemIs/readNext/interpReader-/interpReader/readDWORD.
rewrite interpReader_bind.
sdestructs => c0 b0. 
elim E0: c0 => [p0 |]; last first. rewrite -> interpReader_bindBYTE_hwm.
by rewrite !sepSP_falseR. 
rewrite interpReader_bind.
sdestructs => c1 b1. 
elim E1: c1 => [p1 |]; last first. rewrite -> interpReader_bindBYTE_hwm.
by rewrite !sepSP_falseR.
rewrite interpReader_bind.
sdestructs => c2 b2.
elim E2: c2 => [p2 |]; last first. rewrite -> interpReader_bindBYTE_hwm.
by rewrite !sepSP_falseR.
rewrite interpReader_bind.
sdestructs => c3 b3.
rewrite interpReader_retn.

sdestruct => -> {c3}. 
replace (interpReader readNext p p0 b0) with (p -- p0 :-> b0) by done. 
replace (interpReader readNext p0 p1 b1) with (p0 -- p1 :-> b1) by done. 
replace (interpReader readNext p1 p2 b2) with (p1 -- p2 :-> b2) by done. 
replace (interpReader readNext p2 q b3) with (p2 -- q :-> b3) by done. 
rewrite -> (@memIsBYTE_next_entails _ p0). 
rewrite -> (@memIsBYTE_next_entails _ p1). 
rewrite -> (@memIsBYTE_next_entails _ p2). 
rewrite -> (@memIsBYTE_next_entails _ q).
sdestruct => H0. have H0' := nextIsInc (sym_equal H0). 
sdestruct => H1. have H1' := nextIsInc (sym_equal H1). 
sdestruct => H2. have H2' := nextIsInc (sym_equal H2). 
sdestruct => H3. 
rewrite -H0' in H1'. rewrite -H1' in H2'. rewrite -!addB_addn in H2'. 
replace (1+ (1+1)) with 3 in H2' by done. 
rewrite -H2' in H3.
rewrite {2}H3.
ssplits => //.
sdestructs => H. 
rewrite -H.
rewrite {5}/memIs/readerMemIs/readNext/interpReader-/interpReader/readDWORD.
replace readBYTE with (readNext (T:=BYTE)) by done. 
rewrite interpReader_bindBYTE.
apply lexistsR with b0. rewrite -H0.
rewrite interpReader_bindBYTE.
ssplit. rewrite -H1. 
rewrite interpReader_bindBYTE.
ssplit. rewrite -H2. 
rewrite interpReader_bindBYTE.
ssplit. rewrite interpReader_retn.
ssplit. congruence. 
ssimpl. 
rewrite <-pointsToBYTE_byteIs. rewrite /pointsTo. ssplit. 
rewrite <-pointsToBYTE_byteIs. rewrite /pointsTo. ssplit. 
rewrite <-pointsToBYTE_byteIs. rewrite /pointsTo. ssplit. 
rewrite <-pointsToBYTE_byteIs. rewrite /pointsTo. ssplit.
instantiate (1:=b1). 
instantiate (1:=b2). 
instantiate (1:=b3).
instantiate (1:=q).
instantiate (1:=p2). 
instantiate (1:=p1). instantiate (1:=p0). sbazooka.
clear.
(* WHY ? *)
set C0 := p -- p0 :-> b0. 
set C1 := p0 -- p1 :-> b1. 
set C2 := p1 -- p2 :-> b2. 
set C3 := p2 -- q :-> b3. 
by ssimpl. 
Qed. 
 
Corollary memIsDWORD_range (p q c: DWORD): 
  p -- q :-> c -|- q = p +# 4 /\\ p -- q :-> c.
Proof. split; last by sdestruct. 
have H := @memIsDWORD_rangeGen p c q. 
have H0 : (mkCursor q = next (p +# 3) -> q = p+#4).
move => H1. 
rewrite <-(nextIsInc (sym_equal H1)). by rewrite -addB_addn.
eapply lentailsPre.  apply H. sdestruct => H1. rewrite (H0 H1). sbazooka. 
Qed. 


Fixpoint interpWriterTm {T} (wt:WriterTm T) (p q: Cursor 32) (t: T) :=
  match wt with
  | writerRetn t' => t = t' /\\ p = q /\\ empSP
  | writerNext b wt' => 
      (* We can't write beyond the last byte of memory! *)
      if p is mkCursor p' 
      then byteIs p' b ** interpWriterTm wt' (next p') q t
      else lfalse
  | writerCursor wt' => interpWriterTm (wt' p) p q t
  | writerFail => lfalse
  end.

Lemma interpWriterTm_roundtrip X T (wt: WriterTm T) (R: Reader X) p q x t:
  simrw x p R wt ->
  interpWriterTm wt p q t |-- p -- q :-> x.
Proof.
  intros Hsim. induction Hsim => //=.
  - move=> s [_ [<- Hs]]. eauto.
  move=> s [s1 [s2 [Hs [Hs1 Hs2]]]].
  do 3 eexists. split; first eassumption. split; first eassumption.
  exact: IHHsim.
Qed.

Opaque ILFun_Ops. (* TODO: hack *)

Lemma runWriterTm_pointsto T (W: WriterTm T) p q t bytes:
  runWriterTm W p = Some (t, bytes) ->
  p -- q :-> bytes |-- interpWriterTm W p q t.
Proof.
  revert p bytes. induction W => p bytes //=.
  - case => <- <- /=. rewrite ->seqMemIs_nil. by sbazooka.
  - destruct p as [p|]; last done.
    remember (runWriterTm W (next p)) as runw.
    destruct runw as [[q' bytes']|] => // Hinj.
    injection Hinj => ? ? {Hinj}. subst bytes q'.
    rewrite <-IHW; last by rewrite Heqrunw.
    rewrite ->memIs_consBYTE, ->pointsToBYTE_byteIs. reflexivity.
  - exact: H.
Qed.

Lemma interpWriterTm_bind {X Y} (w1: WriterTm X) (w2: X -> WriterTm Y) p q y:
  interpWriterTm (let! x = w1; w2 x) p q y -|-
  Exists p', Exists x, interpWriterTm w1 p p' x ** interpWriterTm (w2 x) p' q y.
Proof.
  revert p. induction w1 => p //=.
  - split.
    * by sbazooka. 
    * sdestructs => p' x' -> ->. by sbazooka.
  - destruct p.  
    * split.
      - rewrite IHw1. by sbazooka. 
      - sdestructs => p' v. rewrite IHw1. by sbazooka. 
    * split; first done. by sbazooka.
  - split; first done. by sbazooka.
Qed.

Lemma interpWriterTm_hwm T (wt: WriterTm T) t (q: DWORD) :
  interpWriterTm wt (hwm _) q t -|-
  lfalse.
Proof. 
  split; last done. induction wt => //=.
  sdestructs. discriminate.
Qed.
Transparent ILFun_Ops. (* TODO: hack *)

(* This could also be an instance of memIs just like readerMemIs, but we don't
   want typeclass resolution to be ambiguous. *)
Definition interpWriter X {W: Writer X} (p q: Cursor 32) (x: X) :=
  interpWriterTm (W x) p q tt.

Lemma interpWriter_roundtrip X (W: Writer X) (R: Reader X)
      {RT: Roundtrip R W} p q x:
  interpWriter p q x |-- p -- q :-> x.
Proof.
  exact: interpWriterTm_roundtrip.
Qed.

Lemma runWriter_interpWriter X (W: Writer X) p q bytes x:
  runWriter writeNext p x = Some bytes ->
  p -- q :-> bytes |-- interpWriter p q x.
Proof.
  rewrite /interpWriter /runWriter /writeNext => H. simpl in H.
  apply runWriterTm_pointsto.
  destruct (runWriterTm (W x) p) as [[[] bytes']|]; congruence.
Qed.

(*---------------------------------------------------------------------------
   memAny: memory whose value we don't care about
  ---------------------------------------------------------------------------*)

Definition memAny p q := Exists bs: seq BYTE, p -- q :-> bs.

Lemma memAnyMerge p q r : memAny p q ** memAny q r |-- memAny p r. 
Proof.
  rewrite /memAny. sdestructs => s1 s2. 

  apply lexistsR with (s1 ++ s2). setoid_rewrite seqMemIs_cat. 
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

  setoid_rewrite seqMemIs_cons.
  sdestruct => q'. apply lexistsR with b.
  rewrite /pointsTo. 
  rewrite -> memIsBYTE_next_entails. sbazooka. subst. reflexivity. 
Qed. 

Lemma entails_memAnySplit p q r : 
  leCursor p q -> leCursor q r -> memAny p r |-- memAny p q ** memAny q r. 
Proof. 
move/LeCursorP. elim. 
  - move=> _. rewrite <-empSPL at 1. cancel2; []. apply lexistsR with nil.
    done.     
  - move => {q} q Hpq Hind Hqr. rewrite leCursor_next in Hqr.
    etransitivity; [apply Hind|]; first exact: leCursor_weaken.
    rewrite ->entails_memAnyNext; last done.
    sdestruct => b. ssimpl.
    rewrite {1}/memAny. sdestructs => s.
    rewrite /memAny. apply lexistsR with (s ++ [:: b]).
    setoid_rewrite seqMemIs_cat. rewrite /memIs/pairMemIs. simpl fst. simpl snd. 
    apply lexistsR with q. cancel2; first reflexivity.
    rewrite /memIs/seqMemIs.
    apply lexistsR with (next q). 
    rewrite /pointsTo. sdestruct => q'. rewrite -> memIsBYTE_next_entails.
    sdestructs => ->. by ssimpl. 
Qed.

Corollary memAnySplit p q r : 
  leCursor p q -> leCursor q r -> memAny p r -|- memAny p q ** memAny q r. 
Proof. move => H1 H2. 
split. by apply entails_memAnySplit. by apply memAnyMerge. 
Qed. 

Lemma four X (bs: seq X) : size bs = 4 -> exists b1 b2 b3 b4, bs = [::b1;b2;b3;b4].
move => H. 
destruct bs => //. 
destruct bs => //. 
destruct bs => //. 
destruct bs => //. 
exists x, x0, x1, x2.
destruct bs => //. 
Qed. 

Lemma memAny_entails_pointsToDWORD (p:DWORD) :
  memAny p (p+#4) |-- Exists d:DWORD, p :-> d. 
Proof.
rewrite /memAny. sdestruct => bs.
setoid_rewrite seqMemIsBYTE_addn; last done. sdestruct => EQ. 
destruct (four EQ) as [b0 [b1 [b2 [b3 H]]]]. rewrite H.
apply lexistsR with (b3 ## b2 ## b1 ## b0).
rewrite <- pointsToDWORD_BYTES. rewrite /pointsTo. ssplit. 
reflexivity. 
Qed. 

(*
(* NOT TRUE; consider p = 0xfffffffc *)
Lemma pointsToDWORD_entails_memAny (p:DWORD) :
  Exists d:DWORD, p :-> d |-- memAny p (if p+#4 == #0 then hwm _ else p+#4).
Proof. 
rewrite /memAny. sdestruct => d.
elim E: (split4 8 8 8 8 d : BYTE*BYTE*BYTE*BYTE) => [[[b3 b2] b1] b0].
apply (lexistsR (x:=[::b0;b1;b2;b3])). 
have PDB := pointsToDWORD_BYTES p b0 b1 b2 b3.
have: d = b3 ## b2 ## b1 ## b0. 
have SE := @split4eta 8 8 8 8 d.
by rewrite E in SE. 

move ->. rewrite -PDB {PDB E}.
rewrite /pointsTo. sdestruct => q. 

case B: (p +# 4 == #0). 

Corollary memAnyDWORD (p:DWORD) :
  Exists d:DWORD, p :-> d -|- memAny p (if p+#4 == #0 then hwm _ else p+#4).
Proof. split; [apply pointsToDWORD_entails_memAny | apply memAny_entails_pointsToDWORD]. Qed.
*)

Lemma memAnyLe p q : memAny p q |-- leCursor p q /\\ ltrue.
Proof. rewrite /memAny. sdestruct => bs. apply seqMemIs_entails_leCursor. Qed. 

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


(* Other tactics such as ssimpl are very sensitive to syntax. *)
Ltac ptsimpl :=
(replace (@pointsTo (@DWORDorBYTE true)) with (@pointsTo DWORD) by done;  
replace (@readerMemIs (@DWORDorBYTE true)) with (@readerMemIs DWORD) by done;  
replace (@readDWORDorBYTE true) with (readDWORD) by done). 

