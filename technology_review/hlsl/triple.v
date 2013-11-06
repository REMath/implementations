(*===========================================================================
  Hoare triples for reasoning about instruction semantics
  This is architecture-neutral, and assumes only a model that supports 
  registers, flags and memory.
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool ssrnat eqtype tuple seq fintype.
Require Import bitsrep bitsprops bitsopsprops procstate procstatemonad.
Require Import monad monadinst reader SPred septac pointsto pfun cursor enc codec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Transparent ILFun_Ops.

(* A full machine state can be interpreted as a partial state *)
Definition toPState (s:ProcState) : PState :=
  fun f:Frag =>
  match f return fragDom f -> option (fragTgt f) with
  | Registers => fun r => Some (registers s r)
  | Flags => fun f => Some (flags s f)
  | Memory => fun p => Some (memory s p)
  | Traces => fun ch => None
  end. 

(* Hoare triple for machine state monad *)
Definition TRIPLE (P:SPred) (c:ST unit) (Q:SPred) := 
  forall s:ProcState, P (toPState s) ->
    exists f, c s = Success _ (f,tt) /\ Q (toPState f).

Require Import Setoid Program.Basics.

(* Triples behave contravariantly in the precondition and covariantly in the postcondition wrt
   entailment *)
Add Morphism (@TRIPLE) with signature lentails --> eq ==> lentails ==> impl as TRIPLE_mor2.
Proof. move => P P' PP' c Q Q' QQ' H. 
move => s H'. assert (H'' : P (toPState s)) by firstorder. 
specialize (H _ H''). destruct H as [f [H1 H2]]. 
exists f. 
split; first done. 
firstorder. 
Qed. 

(* Unfortunately we need special case for equivalence *)
Add Morphism (@TRIPLE) with signature lequiv ==> eq ==> lequiv ==> iff as TRIPLE_mor.
Proof. move => P P' PP' c Q Q' QQ'. 
split => H. 
move => s H'. assert (H'' : P (toPState s)) by firstorder. 
specialize (H _ H''). destruct H as [f [H1 H2]]. 
exists f. 
split; first done. 
firstorder. 

move => s H'. assert (H'' : P' (toPState s)) by firstorder. 
specialize (H _ H''). destruct H as [f [H1 H2]]. 
exists f. 
split; first done. 
firstorder. 
Qed.

Lemma triple_roc P' Q' P c Q:
  P |-- P' -> Q' |-- Q -> TRIPLE P' c Q' -> TRIPLE P c Q.
Proof. move=> HP HQ H. by rewrite ->HP, <-HQ. Qed.

Lemma triple_roc_pre P' P c Q:
  P |-- P' -> TRIPLE P' c Q -> TRIPLE P c Q.
Proof. move=> HP H. by rewrite ->HP. Qed.

Lemma triple_roc_post Q' P c Q:
  Q' |-- Q -> TRIPLE P c Q' -> TRIPLE P c Q.
Proof. move=> HQ H. by rewrite <-HQ. Qed.

Lemma triple_skip P : TRIPLE P (retn tt) P.
Proof.  move => s pre; exists s; intuition. Qed. 

Lemma triple_pre_exists T (Pf: T -> SPred) c Q : 
  (forall t:T, TRIPLE (Pf t) c Q) -> TRIPLE (Exists t, Pf t) c Q.
Proof. move => TR. 
move => s [t' H]. by apply (TR t' s H). 
Qed. 

Lemma triple_pre_existsOp T (Pf: T -> _) c Q : 
  TRIPLE (Exists t, Pf t) c Q -> (forall t:T, TRIPLE (Pf t) c Q).
Proof. move => TR t s pre. 
apply (TR s). by exists t. 
Qed. 

Lemma triple_pre_existsSep T (Pf: T -> _) c Q S : 
  (forall t, TRIPLE (Pf t ** S) c Q) -> TRIPLE ((Exists t, Pf t) ** S) c Q.
Proof.
  move => TR. apply triple_roc_pre with (Exists t, Pf t ** S).
  - sbazooka.
  move => s [t H]. apply (TR t s H). 
Qed. 

Lemma triple_pre_existsSepOp T (Pf: T -> _) c Q S : 
  TRIPLE ((Exists t, Pf t) ** S) c Q -> (forall t, TRIPLE (Pf t ** S) c Q). 
Proof.
  move=> TR t. eapply triple_roc_pre; [|eassumption]. ssplit; reflexivity.
Qed. 

Lemma triple_post_disjL P c Q1 Q2 :
   TRIPLE P c Q1 -> TRIPLE P c (Q1 \\// Q2).
Proof. move => TR s H. 
specialize (TR s H). 
destruct TR as [f [EQ HH]]. 
exists f. split; [done | by left]. 
Qed.

Lemma triple_post_disjR P c Q1 Q2 :
   TRIPLE P c Q2 -> TRIPLE P c (Q1 \\// Q2).
Proof. move => TR s H. 
specialize (TR s H). 
destruct TR as [f [EQ HH]]. 
exists f. split; [done | by right]. 
Qed.

Lemma triple_post_existsSep T (t:T) P (Qf: T -> _) c S : 
  TRIPLE P c (Qf t ** S) -> TRIPLE P c ((Exists t, Qf t) ** S).
Proof.
  move=> TR. eapply triple_roc_post; [|eassumption]. ssplit; reflexivity.
Qed. 

Lemma triple_pre_hideFlag f v P c Q : 
  TRIPLE (flagAny f ** P) c Q ->
  TRIPLE (flagIs f v ** P) c Q.
Proof. move => H. by apply (triple_pre_existsSepOp). Qed. 


Lemma triple_pre_instFlag f P c Q :
  (forall v, TRIPLE (flagIs f v ** P) c Q) -> 
  TRIPLE (flagAny f ** P) c Q.
Proof. move => TR. apply triple_pre_existsSep => v. apply TR. Qed. 

Lemma triple_seq P P' P'' c1 c2 :
  TRIPLE P c1 P' ->
  TRIPLE P' c2 P'' ->
  TRIPLE P (do! c1; c2) P''.
Proof. move => T1 T2. 
move => s H. rewrite /TRIPLE in T1, T2.
destruct (T1 _ H) as [s' [e H']]. 
destruct (T2 _ H') as [s'' [e' H'']]. 
exists s''. by rewrite /= e.  
Qed. 

Definition isClosed (P: SPred) := 
  forall s s', stateIncludedIn s s' -> P s -> P s'.

Lemma isClosed_sepSP_ltrue P:
  isClosed P -> P ** ltrue -|- P.
Proof.
  move=> HClosed. split.
  - move=> s [s1 [s2 [Hs [HPs _]]]]. eapply HClosed; [|eassumption].
    edestruct stateSplitsAsIncludes; eassumption.
  - rewrite <-empSPR at 1. cancel2.
Qed.

(* Set and get registers *)
Lemma triple_letGetReg r v (P Q:SPred) c: 
  (P |-- r~=v ** ltrue) ->
  TRIPLE P (c v) Q -> 
  TRIPLE P (bind (getRegFromProcState r) c) Q.
Proof.
  move => H T s pre. move: (T s pre) => [f [eq H']]. eexists f. 
  rewrite /=. rewrite <-eq. split; last done.
  move/(_ (toPState s) pre): H => [s1 [s2 [Hs [Hs1 _]]]].
  rewrite /regIs in Hs1. rewrite /getRegFromProcState/=. 
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  specialize (Hs Registers r v). rewrite /= in Hs.
  injection Hs; first by move => ->.
  rewrite -Hs1 /=. case H: (r == r); first done.
  by rewrite eqxx in H.
Qed.

Lemma triple_letGetFlag fl (v:bool) (P Q: SPred) c: 
  (P |-- flagIs fl v ** ltrue) ->
  TRIPLE P (c v) Q -> 
  TRIPLE P (bind (getFlagFromProcState fl) c) Q.
Proof.
  move => H T s pre. move: (T s pre) => [f [eq H']]. eexists f. 
  rewrite /=. rewrite <-eq. split; last done.
  move/(_ (toPState s) pre): H => [s1 [s2 [Hs [Hs1 _]]]].
  rewrite /flagIs in Hs1. rewrite /getFlagFromProcState/=. 
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  specialize (Hs Flags fl v). rewrite /= in Hs.
  injection Hs; first by move => ->.
  rewrite -Hs1 /=. case H: (fl == fl); first done.
  by rewrite eqxx in H.
Qed.

Lemma separateSetReg r v w Q s :
  (r~=v ** Q) (toPState s) -> (r~=w ** Q) (toPState (s!r:=w)).
Proof. 
move => [s1 [s2 [H1 [H2 H3]]]].
rewrite /regIs/= in H2. 

exists (addRegToPState s1 r w), s2.

split.
move => fr. specialize (H1 fr). 
destruct fr => //. 
  (* registers *)
rewrite /splitsAs/= in H1. rewrite /splitsAs/=.
move => r'. specialize (H1 r').
case E: (r == r'). 
- rewrite (eqP E).
  rewrite setThenGetSame. 
  destruct H1.  
  * left. split => //. by destruct H. 
  * rewrite (eqP E) in H2. rewrite -H2 in H. case: H => _ H.
    simpl in H. by rewrite eqxx in H.
- rewrite setThenGetDistinct => //. by apply negbT in E. 

split => //. rewrite -H2 /regIs /addRegToPState.
apply: state_extensional => [[]] //. move=> r' /=.
by case E: (r == r').
Qed. 

Lemma separateSetFlag f v w Q s : 
  (flagIs f v ** Q) (toPState s) -> (flagIs f w ** Q) (toPState (s!f:=w)).
Proof. 
move => [s1 [s2 [H1 [H2 H3]]]].
rewrite /flagIs/= in H2. 

exists (addFlagToPState s1 f w), s2.

split. 

move => fr. specialize (H1 fr). 
destruct fr => //. 
(* flags *)
rewrite /splitsAs/= in H1. rewrite /splitsAs/=.
move => f'. specialize (H1 f').
case E: (f == f'). 
- rewrite (eqP E).
  rewrite setFlagThenGetSame. 
  destruct H1.  
  * left. split => //. by destruct H. 
  * rewrite (eqP E) in H2. rewrite -H2 in H. case: H => _ H.
    simpl in H. by rewrite eqxx in H.
- rewrite setFlagThenGetDistinct => //. by apply negbT in E. 

split => //. rewrite -H2 /flagIs /addFlagToPState.
apply: state_extensional => [[]] //. move=> f' /=.
by case E: (f == f').
Qed.       

Lemma separateForgetFlag f v Q s : 
  (flagIs f v ** Q) (toPState s) -> (flagAny f ** Q) (toPState (s!f:=FlagUnspecified)).
Proof. 
 move=> H. apply lentails_eq.
 assert (Hany: flagIs f FlagUnspecified |-- flagAny f).
 - rewrite /flagAny. ssplit. reflexivity.
 rewrite <-Hany => {Hany}. apply-> lentails_eq.
 eapply separateSetFlag. apply H.
Qed.       


Lemma pointsToBYTEdef (p:BITS 32) (v: BYTE) (s:PState) : (p:->v) s -> s Memory p = Some (Some v).
Proof. move => [q H]. 
destruct H as [m [H1 H2]].
simpl getReader in H1. 
rewrite /readBYTE /= /readBYTE_op in H1.  
case e': (m p) => [b |]; rewrite e' in H1; last done. 
rewrite H2. congruence. 
rewrite /inRange leCursor_refl andTb. replace q with (next p) by congruence. 
apply ltNext. 
Qed. 

Lemma triple_setRegSep r v w :
  forall S, TRIPLE (regIs r v ** S) (setRegInProcState r w) (regIs r w ** S).
Proof. 
move => S s pre. eexists _. split. by rewrite /=/setRegInProcState/=/setProcState/=.  
apply: separateSetReg pre. 
Qed. 

Lemma triple_setRegSepGen r v w P R:
  P |-- r~=v ** R ->
  TRIPLE P (setRegInProcState r w) (r~=w ** R).
Proof. move=> HP. rewrite ->HP. apply: triple_setRegSep. Qed. 

Lemma triple_doSetRegSep r v w c Q :
  forall S, 
  TRIPLE (r~=w ** S) c Q ->  
  TRIPLE (r~=v ** S) (do! setRegInProcState r w; c) Q.
Proof. move => S T s pre. apply: T. apply: separateSetReg pre. Qed. 

Lemma triple_doSetFlagSep f v (w:bool) c Q :
  forall S, 
  TRIPLE (flagIs f w ** S) c Q ->  
  TRIPLE (flagIs f v ** S) (do! updateFlagInProcState f w; c) Q.
Proof. move => S T s pre. apply: T. apply: separateSetFlag pre. Qed. 

Lemma triple_doForgetFlagSep f v c Q :
  forall S, 
  TRIPLE (flagAny f ** S) c Q ->  
  TRIPLE (flagIs f v ** S) (do! forgetFlagInProcState f; c) Q.
Proof. move => S T s pre. apply: T. apply: separateForgetFlag pre. Qed.

(*
Lemma letGetReg_ruleIgnore r (P: SPred) c : 
  forall S:Facts,
  (forall v, TRIPLE P (c v) [* regIs r v & S]) -> 
  TRIPLE P (bind (getRegFromProcState r) c) S.
Proof. move => S T s pre. specialize (T (registers s r)). 
simpl. destruct (T s pre) as [f [eq H]]. exists f. intuition. 
apply: separateDrop. apply H. 
Qed. 
*)

Lemma triple_letGetRegSep r v c Q : 
  forall S,
  TRIPLE (r~=v ** S) (c v) Q -> 
  TRIPLE (r~=v ** S) (bind (getRegFromProcState r) c) Q.
Proof. move => S T. apply: triple_letGetReg. cancel2. reflexivity. done. Qed. 

Lemma triple_letGetFlagSep fl (v:bool) c Q : 
  forall S,
  TRIPLE (flagIs fl v ** S) (c v) Q -> 
  TRIPLE (flagIs fl v ** S) (bind (getFlagFromProcState fl) c) Q.
Proof. move => S T. apply: triple_letGetFlag. cancel2. reflexivity. done. Qed. 

Lemma triple_doGetReg r (P Q: SPred) c : 
  TRIPLE P c Q -> 
  TRIPLE P (do! getRegFromProcState r; c) Q.
Proof. move => T s pre. move: (T s pre) => [f [eq H']]. by eexists f. Qed.

Lemma triple_doGetFlag f (v:bool) (Q: SPred) c : 
  forall S, 
  TRIPLE (flagIs f v ** S) c Q -> 
  TRIPLE (flagIs f v ** S) (do! getFlagFromProcState f; c) Q.
Proof. apply (triple_letGetFlagSep (c:=fun _ => c)). Qed.

Lemma pointsto_read {R: readerType} p q (v:R) s s' :
  (p -- q :-> v) s ->
  stateIncludedIn s (toPState s') ->
  read s' p = readerOk v q.
Proof.
  move=> Hpoints Hinc.
  destruct Hpoints as [m [Hread Heqv]].
  have Hgood := readP R m p. rewrite Hread in Hgood.
  move: Hgood => [Hle Hok]. apply: Hok => p' Hp'.
  specialize (Heqv p' Hp'). specialize (Hinc Memory _ _ Heqv).
  rewrite /toPState in Hinc. congruence.
Qed.

(* Set and get readables from memory *)
Lemma triple_letGetSepGen {R:readerType} (p:PTR) (v:R) P c Q : 
  P |-- p:->v ** ltrue ->  
  TRIPLE P (c v) Q -> 
  TRIPLE P (bind (getFromProcState p) c) Q.
Proof. move => PTIS T s pre.
specialize (T _ pre). 
destruct T as [f [H1 H2]]. 
exists f. 
split; last done. clear H2. 
rewrite /getFromProcState. specialize (PTIS _ pre).
rewrite /= -H1.
edestruct PTIS as [s1 [s2 [Hs [[q Hs1] _]]]].
have Hread := pointsto_read Hs1 _.
rewrite /read in Hread. rewrite Hread; first done.
edestruct stateSplitsAsIncludes; eassumption.
Qed.

Lemma triple_letGetSep {R:readerType} (p:PTR) (v:R) c Q : 
  forall S,
  TRIPLE (p:->v ** S) (c v) Q -> 
  TRIPLE (p:->v ** S) (bind (getFromProcState p) c) Q.
Proof. move => S. apply triple_letGetSepGen. by cancel2. Qed.

Lemma triple_letReadSep {R:readerType} (p q:PTR) (v:R) c (P:SPred) Q : 
  P |-- p -- q :-> v ** ltrue ->
  TRIPLE P (c (v,q)) Q -> 
  TRIPLE P (bind (readFromProcState p) c) Q.
Proof. move => PTIS T s pre.
specialize (T _ pre). 
destruct T as [f [H1 H2]]. 
exists f. 
split; last done. clear H2. 
rewrite /readFromProcState. specialize (PTIS _ pre).
rewrite /= -H1.
edestruct PTIS as [s1 [s2 [Hs [Hs1 _]]]].
have Hread := pointsto_read Hs1 _.
rewrite /read in Hread. rewrite Hread; first done.
edestruct stateSplitsAsIncludes; eassumption.
Qed.

(* Set and get DWORDs from memory *)
Lemma triple_letGetDWORDSep (p:PTR) (v:DWORD) c Q : 
  forall S,
  TRIPLE (p:->v ** S) (c v) Q -> 
  TRIPLE (p:->v ** S) (bind (getDWORDFromProcState p) c) Q.
Proof. apply triple_letGetSep. Qed. 

Lemma triple_letGetDWORDSepGen (p:PTR) (v:DWORD) P c Q : 
  P |-- p:->v ** ltrue ->
  TRIPLE P (c v) Q -> 
  TRIPLE P (bind (getDWORDFromProcState p) c) Q.
Proof. apply triple_letGetSepGen. Qed. 

Lemma triple_letGetBYTESep (p:PTR) (v:BYTE) c Q : 
  forall S,
  TRIPLE (p:->v ** S) (c v) Q -> 
  TRIPLE (p:->v ** S) (bind (getBYTEFromProcState p) c) Q.
Proof. apply triple_letGetSep. Qed. 

Require Import bitsops pmapprops. 

(* Sledgehammer proof. Need to factor! *)
Lemma triple_setBYTESep (p:PTR) (v w:BYTE) :
  forall S,
  TRIPLE (p:->v ** S) (setBYTEInProcState p w) (p:->w ** S).
Proof. move => S s pre. 
rewrite /setBYTEInProcState/setInProcState/encode/encodeBYTE/setBYTESInProcState.
rewrite /=/primSetBYTEInProcState/=. 
destruct pre as [s1 [s2 [H1 [H2 H3]]]].
destruct H2 as [q H2]. 
have MIB := memIsBYTE_nextCursor H2. 
rewrite MIB {MIB} in H2.  
destruct H2 as [m [H4 H5]]. 
rewrite /read/= in H4. 
case E: (m p) => [b |]. rewrite E in H4. 
inversion H4. subst. 
have H5' := H5 p. have RANGE: inRange p (next p) p. rewrite /inRange. rewrite leCursor_refl. 
rewrite ltNext. done. specialize (H5' RANGE). rewrite E in H5'. 
rewrite /isMapped. 
rewrite /stateSplitsAs in H1. 
rewrite /splitsAs in H1. 
exists (s ! p := w). 
have H1' := H1 Memory p. 
destruct H1'. destruct H as [Ha Hb].
rewrite H5' in Ha. 
inversion Ha.  
simpl. split; first done. 
exists (addBYTEToPState s1 p w). exists s2. 
split. rewrite /stateSplitsAs.
case. 
+ apply: H1 Registers. 
+ 
rewrite /splitsAs. simpl. move => p'. specialize (H5 p'). 
case E': (p==p'). left. 
split. rewrite (eqP E'). by rewrite updateThenLookup.
rewrite -(eqP E'). apply Hb.
rewrite updateThenLookupDistinct. 
specialize (H1 Memory p').  simpl in H1. apply H1. move => HH. rewrite HH in E'. 
rewrite eq_refl in E'. done. 
apply: H1 Flags. 
apply: H1 Traces. 

split.
exists (next p). 
exists (m!p:=w).  
simpl. rewrite updateThenLookup. split. done. move => p' RANGE'. 
case E': (p==p'). rewrite (eqP E'). by rewrite updateThenLookup. 
rewrite updateThenLookupDistinct. apply H5. apply RANGE'. move => H. rewrite H in E'. 
rewrite eq_refl in E'. done. done.

destruct H. rewrite H5' in H0. 
done. 

rewrite E in H4. done. 
Qed. 


Lemma triple_setBYTESSep (v:seq BYTE) : forall (p:Cursor 32) (w:seq BYTE),
  size v = size w ->
  forall S,
  TRIPLE (p :->v ** S) (setBYTESInProcState p w) (p:->w ** S).
Proof. induction v => p w EQ S.  
(* empty *)
simpl in EQ. 
move => s H.
destruct H as [s1 [s2 [s1s2 [H1 H2]]]].   
rewrite /pointsTo in H1. exists s. split. 
destruct w => //.  
destruct w => //.
exists s1. 
exists s2. split => //. 
(* cons *)
simpl in EQ. 
destruct w => //. 
rewrite /setBYTESInProcState-/setBYTESInProcState.
case p => [p' |]. 
+ have TSS:= @triple_setBYTESep p' t b (next p' :-> v ** S). 
  inversion EQ. 
  apply: triple_seq.
  replace (t::v) with ([::t] ++ v) by done. 
  rewrite pointsTo_consBYTE.
  rewrite /setBYTEInProcState/setInProcState/encode/encodeBYTE/setBYTESInProcState-/setBYTESInProcState in TSS. 
  rewrite sepSPA.
  rewrite doRet in TSS.  
  apply TSS.
  clear TSS. 
  set PB := p':->b.
  specialize (IHv (next p') w H0 (PB ** S)). 
  clear EQ H0.
  rewrite pointsTo_consBYTE sepSPA. rewrite /PB. 
  rewrite /PB in IHv. 
  rewrite -sepSPA. rewrite (sepSPC PB). 
  rewrite -sepSPA. rewrite (sepSPC PB). 
  rewrite 2!sepSPA. rewrite /PB. apply IHv. 
+ simpl. move => ps PRE.
  rewrite /pointsTo in PRE.
  destruct PRE as [s1 [s2 [s1s2 [H1 H2]]]]. 
  destruct H1 as [q H1]. 
  have H:= (cons_BYTE_hwm H1). 
done. 
Qed. 


Lemma roundtripDWORD (p:PTR) (v:DWORD) S :
  p :-> encode v ** S |-- p :->v ** S.
Proof. 
  rewrite /pointsTo. 
  sdestruct => q. rewrite ->seqMemIs_reader.
  move => s H. simpl in H.
  destruct H as [s1 [s2 [s1s2 [H1 H2]]]]. 
  exists s1, s2. split; first done. split; last done. 
  destruct H1 as [m [Hok Hrange]]. 
  exists q. exists m.   split; last done. 
  apply roundtrip. apply Hok. 
Qed. 

(* Converse of this doesn't hold.
   Consider p = 0xfffffffc (or larger) for which p+#4 wraps around, but p :-> d holds *)
(* @TODO: move to cursor-based version *)
Lemma memAnyDWORD (p:DWORD) :
  memAny p (p+#4) |-- Exists d:DWORD, (p :-> d ** empSP). 
Proof. 
rewrite /memAny. 
sdestruct => q.
setoid_rewrite seqMemIsBYTE_addn; last done. sdestruct => EQ. 

destruct q; first done. 
destruct q; first done. 
destruct q; first done. 
destruct q; first done. 
destruct q; last done.  

replace [:: b; b0; b1; b2] with (encode (b2 ## b1 ##b0 ## b)).
apply lexistsR with (b2 ## b1 ## b0 ## b).
rewrite <- roundtripDWORD.
rewrite /pointsTo. sbazooka. 

by rewrite /encode/encodeDWORD/encode/encodeBYTE split4app. 
Qed. 

Lemma roundtripDWORDinv (p:PTR) (v:DWORD) S :
  p :-> v ** S |-- p :-> encode v ** S.
Proof. rewrite /pointsTo. 
  sdestruct => q. 
  move => s H.
  destruct H as [s1 [s2 [s1s2 [H1 H2]]]]. 
  exists s1, s2. split; first done. split; last done.  
  destruct H1 as [m [Hok Hrange]]. 
  exists q.  
  rewrite /encode/encodeDWORD. 
  rewrite /encode/encodeBYTE. simpl (_ ++ _).
  case E: (split4  8 8 8 8 v) => [[[b0 b1] b2] b3].
  rewrite /read/getReader/DWORD_readerType/readDWORD in Hok.  
  (* Proof gets ugly from here *)
  simpl in Hok. rewrite /bindRead_op /readBYTE_op in Hok.
  destruct (m p) as [mp|] _eqn:Hmp => //.
  destruct (next p) as [p1|] _eqn:Hp1 => //.
  destruct (m p1) as [mp1|] _eqn:Hmp1 => //.
  destruct (next p1) as [p2|] _eqn:Hp2 => //.
  destruct (m p2) as [mp2|] _eqn:Hmp2 => //.
  destruct (next p2) as [p3|] _eqn:Hp3 => //.
  destruct (m p3) as [mp3|] _eqn:Hmp3 => //.
  rewrite /bytesToDWORD /unitRead_op in Hok.
  erewrite <-(@split4eta 8 8 8 8 v) in Hok. rewrite E in Hok.
  move: Hok => [Hbytes Hq].
  move/eqP: Hbytes => Hbytes.
  rewrite eqseq_cat in Hbytes; last by rewrite !size_cat !size_tuple.
  move/andP: Hbytes => [Hbytes Hb3].
  rewrite eqseq_cat in Hbytes; last by rewrite !size_cat !size_tuple.
  move/andP: Hbytes => [Hbytes Hb2].
  rewrite eqseq_cat in Hbytes; last by rewrite !size_tuple.
  move/andP: Hbytes => [Hb0 Hb1].
  rewrite val_eqE in Hb0. rewrite val_eqE in Hb1.
  rewrite val_eqE in Hb2. rewrite val_eqE in Hb3.
  move/eqP: Hb0 => Hb0. move/eqP: Hb1 => Hb1.
  move/eqP: Hb2 => Hb2. move/eqP: Hb3 => Hb3.
  subst mp mp1 mp2 mp3.
  pose only := fun (i: DWORD) => fun f =>
    match f return fragDom f -> bool with
    | Memory => fun j => i == j
    | _ => fun _ => false
    end.
  exists p1. eexists. eexists.
  split; [apply (stateSplitsOn _ (only p))|]. split.
  - exists m. split.
    - simpl. by rewrite Hmp Hp1.
    move=> p' Hp'. rewrite -Hrange.
    - rewrite <-Hp1 in Hp'.
      apply inRange_next in Hp'. subst p'.
      rewrite /restrictState /only. by rewrite eqxx.
    move/andP: Hp' => [Hle Hlt]. apply/andP. split => //.
    eapply ltCursor_trans; first apply Hlt.
    rewrite <-leCursor_next. rewrite Hp2. apply: leCursor_weaken.
    rewrite <-leCursor_next. rewrite Hp3. rewrite -Hq.
    apply: leNext.
  exists p2. eexists. eexists.
  split; [apply (stateSplitsOn _ (only p1))|]. split.
  - exists m. split.
    - simpl. by rewrite Hmp1 Hp2.
    move=> p' Hp'. rewrite -Hrange.
    - rewrite <-Hp2 in Hp'.
      apply inRange_next in Hp'. subst p'.
      rewrite /restrictState /only. rewrite eqxx.
      case Hp: (p == p1) => //. move/eqP: Hp => Hp. subst p1.
      by apply neNext in Hp1.
    move/andP: Hp' => [Hle Hlt]. apply/andP. split.
    - eapply leCursor_trans; last apply Hle. apply: leCursor_weaken.
      rewrite <-leCursor_next. rewrite Hp1. exact: leCursor_refl.
    eapply ltCursor_trans; first apply Hlt.
    rewrite <-leCursor_next. rewrite Hp3. rewrite -Hq.
    apply: leNext.
  exists p3. eexists. eexists.
  split; [apply (stateSplitsOn _ (only p2))|]. split.
  - exists m. split.
    - simpl. by rewrite Hmp2 Hp3.
    move=> p' Hp'. rewrite -Hrange.
    - rewrite <-Hp3 in Hp'.
      apply inRange_next in Hp'. subst p'.
      rewrite /restrictState /only. rewrite eqxx.
      case Hp: (p1 == p2).
      - move/eqP: Hp => Hp. subst p2. by apply neNext in Hp2.
      simpl.
      symmetry in Hp1. apply nextIsInc in Hp1. subst p1.
      symmetry in Hp2. apply nextIsInc in Hp2. subst p2.
      rewrite eq_sym. rewrite !addB1. by rewrite incBincBneq.
    move/andP: Hp' => [Hle Hlt]. apply/andP. split.
    - eapply leCursor_trans; last apply Hle. apply: leCursor_weaken.
      rewrite <-leCursor_next. rewrite Hp1. apply: leCursor_weaken.
      rewrite <-leCursor_next. rewrite Hp2. exact: leCursor_refl.
    eapply ltCursor_trans; first apply Hlt.
    rewrite -Hq. rewrite <-leCursor_next. exact: leCursor_refl.
  exists q. eexists. eexists.
  split; [apply stateSplitsAs_s_s_emp|]. split => //.
  - exists m. split.
    - simpl. by rewrite Hmp3 Hq.
    move=> p' Hp'. rewrite -Hrange.
    - rewrite <-Hq in Hp'.
      apply inRange_next in Hp'. subst p'.
      rewrite /restrictState /only.
      symmetry in Hp1. apply nextIsInc in Hp1. subst p1.
      symmetry in Hp2. apply nextIsInc in Hp2. subst p2.
      symmetry in Hp3. apply nextIsInc in Hp3. subst p3. rewrite ->!addB1 in *.
      rewrite eq_sym. rewrite incBneq.
      rewrite eq_sym. rewrite incBincBneq.
      rewrite eq_sym. rewrite incBincBincBneq. done.
    move/andP: Hp' => [Hle Hlt]. apply/andP. split => //.
    eapply leCursor_trans; last apply Hle. apply: leCursor_weaken.
    rewrite <-leCursor_next. rewrite Hp1. apply: leCursor_weaken.
    rewrite <-leCursor_next. rewrite Hp2. apply: leCursor_weaken.
    rewrite <-leCursor_next. rewrite Hp3. exact: leCursor_refl.
Qed. 

(* This isn't as general as we might like, at least for other
   types than DWORDs. What if there are bytes defined at p, but which
   do not represent any value i.e. they are junk? It's enough to 
   have *bytes* there, but not necessarily anything sensible *)
Lemma triple_setDWORDSep (p:PTR) (v w:DWORD) S :
  TRIPLE (p:->v ** S) (setDWORDInProcState p w) (p:->w ** S).
Proof.
rewrite /setDWORDInProcState/setInProcState.
eapply triple_roc_post. apply roundtripDWORD.  
eapply triple_roc_pre. apply roundtripDWORDinv. 
apply triple_setBYTESSep. done. 
Qed. 

Lemma triple_setDWORDorBYTESep dword (p:PTR) (v w: DWORDorBYTE dword) S :
  TRIPLE (p:->v ** S) (setDWORDorBYTEInProcState p w) (p:->w ** S). 
Proof. destruct dword. apply triple_setDWORDSep. apply triple_setBYTESep. Qed.

Lemma triple_doSetDWORDSep (p:PTR) (v w: DWORD) c Q S :
  TRIPLE (p:->w ** S) c Q ->  
  TRIPLE (p:->v ** S) (do! setDWORDInProcState p w; c) Q.
Proof. move => T s pre. 
destruct (triple_setDWORDSep w pre) as [f [H1 H2]]. 
specialize (T _ H2). 
destruct T as [f' H3]. exists f'. by rewrite /= H1. 
Qed. 

Ltac triple_apply lemma :=
  eapply triple_roc; [| |eapply lemma];
    instantiate; [ssimpl; try reflexivity|..];
    instantiate; [try reflexivity; ssimpl; try reflexivity|..].

