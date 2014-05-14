(*===========================================================================
  Hoare triples for reasoning about instruction semantics
  This is architecture-neutral, and assumes only a model that supports 
  registers, flags and memory.
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool ssrnat eqtype tuple seq fintype.
Require Import bitsrep bitsprops bitsops bitsopsprops procstate procstatemonad pmapprops.
Require Import monad monadinst reader SPred septac pointsto pfun cursor writer.

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
    exists f, exists outputs, c s = (outputs, Success _ (f,tt)) /\ Q (toPState f).

Require Import Setoid Program.Basics.

(* Triples behave contravariantly in the precondition and covariantly in the postcondition wrt
   entailment *)
Add Morphism (@TRIPLE) with signature lentails --> eq ==> lentails ==> impl as TRIPLE_mor2.
Proof. move => P P' PP' c Q Q' QQ' H. 
move => s H'. assert (H'' : P (toPState s)) by firstorder. 
specialize (H _ H''). destruct H as [f [o [H1 H2]]]. 
exists f. exists o. 
split; first done. 
firstorder. 
Qed. 

(* Unfortunately we need special case for equivalence *)
Add Morphism (@TRIPLE) with signature lequiv ==> eq ==> lequiv ==> iff as TRIPLE_mor.
Proof. move => P P' PP' c Q Q' QQ'. 
split => H. 
move => s H'. assert (H'' : P (toPState s)) by firstorder. 
specialize (H _ H''). destruct H as [f [o [H1 H2]]]. 
exists f. 
exists o. split; first done. 
firstorder. 

move => s H'. assert (H'' : P' (toPState s)) by firstorder. 
specialize (H _ H''). destruct H as [f [o [H1 H2]]]. 
exists f. 
exists o. 
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
Proof.  move => s pre; exists s; exists nil; intuition. Qed. 

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
destruct TR as [f [o [EQ HH]]]. 
exists f. exists o. split; [done | by left]. 
Qed.

Lemma triple_post_disjR P c Q1 Q2 :
   TRIPLE P c Q2 -> TRIPLE P c (Q1 \\// Q2).
Proof. move => TR s H. 
specialize (TR s H). 
destruct TR as [f [o [EQ HH]]]. 
exists f. exists o. split; [done | by right]. 
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
destruct (T1 _ H) as [s' [o [e H']]]. 
destruct (T2 _ H') as [s'' [o' [e' H'']]]. 
exists s''. exists (o++o'). by rewrite /= e e'.  
Qed. 

Definition isClosed (P: SPred) := 
  forall s s', stateIncludedIn s s' -> P s -> P s'.

Lemma isClosed_sepSP_ltrue P:
  isClosed P -> P ** ltrue -|- P.
Proof.
  move=> HClosed. split.
  - move=> s [s1 [s2 [Hs [HPs _]]]]. eapply HClosed; [|eassumption].
    edestruct stateSplitsAsIncludes; [eapply Hs | assumption].
  - rewrite <-empSPR at 1. cancel2.
Qed.

(* Set and get registers *)
Lemma triple_letGetReg r v (P Q:SPred) c: 
  (P |-- r~=v ** ltrue) ->
  TRIPLE P (c v) Q -> 
  TRIPLE P (bind (getRegFromProcState r) c) Q.
Proof.
  move => H T s pre. move: (T s pre) => [f [o [eq H']]]. eexists f. exists o. 
  rewrite /=. rewrite <-eq. split; last done.
  move/(_ (toPState s) pre): H => [s1 [s2 [Hs [Hs1 _]]]].
  rewrite /regIs in Hs1. rewrite /getRegFromProcState/=. 
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  specialize (Hs Registers r v). rewrite /= in Hs. 
  injection Hs. move => ->. by destruct (c v s).  
  rewrite -Hs1 /=. case H: (r == r); first done.
  by rewrite eqxx in H.
Qed.

Lemma triple_letGetFlag fl (v:bool) (P Q: SPred) c: 
  (P |-- flagIs fl v ** ltrue) ->
  TRIPLE P (c v) Q -> 
  TRIPLE P (bind (getFlagFromProcState fl) c) Q.
Proof.
  move => H T s pre. move: (T s pre) => [f [o [eq H']]]. eexists f. 
  eexists o. 
  rewrite /=. rewrite <-eq. split; last done.
  move/(_ (toPState s) pre): H => [s1 [s2 [Hs [Hs1 _]]]].
  rewrite /flagIs in Hs1. rewrite /getFlagFromProcState/=. 
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  specialize (Hs Flags fl v). rewrite /= in Hs.
  injection Hs. move => ->. simpl. by destruct (c v s). 
  rewrite -Hs1 /=. case H: (fl == fl); first done.
  by rewrite eqxx in H.
Qed.

Local Transparent PStateSepAlgOps.

Lemma separateSetReg r v w Q s :
  (r~=v ** Q) (toPState s) -> (r~=w ** Q) (toPState (s!r:=w)).
Proof.
simpl.
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
simpl.
split; [|assumption].
rewrite -H2 /regIs /addRegToPState.
apply: state_extensional => [[]] //. move=> r' /=.
by case E: (r == r').
Qed. 


(* This is the crucial lemma that relates the *logical* interpretation of a reader 
   (interpReader) with the *operational* interpretation of a reader (readMem) *)
Lemma readMemMemIs R (rt: Reader R) : forall p q (v:R) s s',
  interpReader rt p q v s ->
  stateIncludedIn s (toPState s') ->
  readMem rt s' p = readerOk v q.
Proof. 
induction rt => p q v s s' H1 H2/=. 
(* readerRetn *) 
destruct H1 as [H3 [H4 H5]]. by subst. 
(* readerNext *) 
simpl in H1. 
case E: p => [pp |]. subst.  
destruct H1 as [b [s1 [s2 [H5 [H6 H7]]]]].
rewrite /byteIs in H6.  
rewrite /addBYTEToPState/emptyPState/= in H6.

destruct (stateSplitsAsIncludes H5) as [H8 H9]. 
have H10 := stateIncludedIn_trans H9 H2. 
rewrite <- H6 in H8.
rewrite /includedIn/= in H8.  specialize (H8 Memory pp (Some b)). 
rewrite /=eq_refl in H8. specialize (H8 (refl_equal _)).  
rewrite /stateIncludedIn in H2. 
specialize (H2 Memory pp _ H8).
inversion H2.  
rewrite H1. 
specialize (H b (next pp) q v s2). 
apply (H _ H7 H10).  

by subst. 

(* readerCursor *)
rewrite /interpReader-/interpReader in H1.  
apply: H => //. assumption. 
Qed. 

Corollary pointsto_read R {r: Reader R} p q (v:R) s s' :
  (p -- q :-> v) s ->
  stateIncludedIn s (toPState s') ->
  readMem readNext s' p = readerOk v q.
Proof. apply readMemMemIs. Qed.

Lemma separateSetBYTE p v w Q s :
  (byteIs p v ** Q) (toPState s) -> (byteIs p w ** Q) (toPState (s!p:=w)).
Proof. 
move => [s1 [s2 [H1 [H2 H3]]]].
rewrite /byteIs/= in H2. 

exists (addBYTEToPState s1 p w), s2.

split.
move => fr. specialize (H1 fr). 
destruct fr => //. 
  (* memory *)
rewrite /splitsAs/= in H1. rewrite /splitsAs/=.
move => p'. specialize (H1 p').
case E: (p == p'). 
rewrite (eqP E).
  rewrite updateThenLookup.
  destruct H1.  
  * left. split => //. by destruct H. 
  * rewrite (eqP E) in H2. rewrite -H2 in H. case: H => _ H.
    simpl in H. by rewrite eqxx in H.

rewrite updateThenLookupDistinct => //. 
apply negbT in E. move => H. by rewrite H eq_refl in E.

split => //. 
eapply byteIsEquiv_m; [reflexivity | reflexivity| rewrite <- H2; reflexivity|].
apply: state_extensional => [[]] //. move=> p' /=.
by case E: (p == p').

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

split => //. 
eapply flagIsEquiv_m; [reflexivity | reflexivity | rewrite <- H2; reflexivity|].
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


(*
Lemma pointsToBYTEdef (p:BITS 32) (v: BYTE) (s:PState) : (p:->v) s -> s Memory p = Some (Some v).
Proof. move => [q H].
destruct H as [b [s1 [s2 [H1 [H2 H3]]]]]. 
rewrite /byteIs in H2. rewrite -H2 in H1.
rewrite /addBYTEToPState in H2. simpl in H2. apply f_equal in H2. firstorder. congruence. simpl in H2. rewrite /MemIs in H. 
simpl.  
destruct H as [m [H1 H2]].
simpl getReader in H1. 
rewrite /readBYTE /= /readBYTE_op in H1.  
case e': (m p) => [b |]; rewrite e' in H1; last done. 
rewrite H2. congruence. 
rewrite /inRange leCursor_refl andTb. replace q with (next p) by congruence. 
apply ltNext. 
Qed. 
*)

Lemma triple_setRegSep r v w :
  forall S, TRIPLE (regIs r v ** S) (setRegInProcState r w) (regIs r w ** S).
Proof. 
move => S s pre. eexists _. eexists _. 
split. by rewrite /=/setRegInProcState/=/setProcState/=.  
apply: separateSetReg pre. 
Qed. 

(*
Lemma triple_setBYTERegSep r (v:DWORD) (w:BYTE) :
  forall S, TRIPLE (regIs r v ** S) (setBYTERegInProcState r w) (regIs r (@high 24 8 v ## w) ** S).
Proof. 
move => S s pre. eexists _. split. by rewrite /setBYTERegInProcState/setProcState.  
have SRR := separateSetReg _ pre.
elim pre => [s1 [s2 [Hs [Hs1 _]]]].
rewrite /regIs in Hs1.
specialize (Hs1 Registers r); simpl in Hs1.
assert (r == r) by intuition.
rewrite H in Hs1.
specialize (Hs Registers r); destruct Hs as [[H1 H2] | [H1 H2]]; subst.
rewrite H1 in Hs1. inversion Hs1; subst.
apply SRR.
by congruence.
Qed. 
*)

Lemma triple_setRegSepGen r v w P R:
  P |-- r~=v ** R ->
  TRIPLE P (setRegInProcState r w) (r~=w ** R).
Proof. move=> HP. rewrite ->HP. apply: triple_setRegSep. Qed. 

Lemma triple_doSetRegSep r v w c Q :
  forall S, 
  TRIPLE (r~=w ** S) c Q ->  
  TRIPLE (r~=v ** S) (do! setRegInProcState r w; c) Q.
Proof. move => S T s pre. rewrite /TRIPLE in T. 
simpl. have H:= separateSetReg w pre.  specialize (T _ H). 
destruct T as [f [o [T]]]. exists f, o.
by destruct (c _).  
Qed. 

Lemma triple_doSetFlagSep f v (w:bool) c Q :
  forall S, 
  TRIPLE (flagIs f w ** S) c Q ->  
  TRIPLE (flagIs f v ** S) (do! updateFlagInProcState f w; c) Q.
Proof. move => S T s pre. rewrite /TRIPLE in T. 
simpl. have H:= separateSetFlag w pre. specialize (T _ H). 
destruct T as [fs [o T]]. exists fs, o. 
by destruct (c _). Qed. 

Lemma triple_doForgetFlagSep f v c Q :
  forall S, 
  TRIPLE (flagAny f ** S) c Q ->  
  TRIPLE (flagIs f v ** S) (do! forgetFlagInProcState f; c) Q.
Proof. move => S T s pre. rewrite /TRIPLE in T. 
simpl. have H:=separateForgetFlag pre. specialize (T _ H).  
destruct T as [fs [o T]]. exists fs, o. 
by destruct (c _). Qed.

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
Proof. move => T s pre. move: (T s pre) => [f [o [eq H']]]. eexists f. eexists o. 
simpl. by destruct (c s). Qed.

Lemma triple_doGetFlag f (v:bool) (Q: SPred) c : 
  forall S, 
  TRIPLE (flagIs f v ** S) c Q -> 
  TRIPLE (flagIs f v ** S) (do! getFlagFromProcState f; c) Q.
Proof. apply (triple_letGetFlagSep (c:=fun _ => c)). Qed.

(* Set and get readables from memory *)
Lemma triple_letGetSepGen R {r:Reader R} (p:PTR) (v:R) P c Q : 
  P |-- p:->v ** ltrue ->  
  TRIPLE P (c v) Q -> 
  TRIPLE P (bind (getFromProcState p) c) Q.
Proof. move => PTIS T s pre.
destruct (T _ pre) as [f [o [H1 H2]]]. 
exists f. 
exists o. split; last done.
rewrite /getFromProcState. specialize (PTIS _ pre).
rewrite /= -H1.
destruct PTIS as [s1 [s2 [Hs [[q Hs1] _]]]].
have Hread := pointsto_read Hs1 _. rewrite Hread. by destruct (c v s). 
by edestruct stateSplitsAsIncludes. 
Qed.

Lemma triple_letGetSep R {r:Reader R} (p:PTR) (v:R) c Q : 
  forall S,
  TRIPLE (p:->v ** S) (c v) Q -> 
  TRIPLE (p:->v ** S) (bind (getFromProcState p) c) Q.
Proof. move => S. apply triple_letGetSepGen. by cancel2. Qed.

Lemma triple_letReadSep R {r:Reader R} (p q:PTR) (v:R) c (P:SPred) Q : 
  P |-- p -- q :-> v ** ltrue ->
  TRIPLE P (c (v,q)) Q -> 
  TRIPLE P (bind (readFromProcState p) c) Q.
Proof. move => PTIS T s pre.
specialize (T _ pre). 
destruct T as [f [o [H1 H2]]]. 
exists f. exists o. 
split; last done. clear H2. 
rewrite /readFromProcState. specialize (PTIS _ pre).
rewrite /= -H1.
edestruct PTIS as [s1 [s2 [Hs [Hs1 _]]]].
have Hread := pointsto_read Hs1 _.
rewrite Hread. by destruct (c _ s).  
edestruct stateSplitsAsIncludes; [apply Hs | eassumption].
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

Lemma byteIsMapped (p:PTR) (v: BYTE) S s : 
  (byteIs p v ** S) (toPState s) -> isMapped p s.
Proof. 
move => [s1 [s2 [H1 [H2 H3]]]].
destruct (stateSplitsAsIncludes H1) as [H4 H5].
rewrite /byteIs/addBYTEToPState in H2; simpl in H2.
rewrite <- H2 in H4.
specialize (H4 Memory p). rewrite /= eq_refl/= in H4. 
specialize (H4 (Some v) (refl_equal _)). 
inversion H4. rewrite /isMapped H0. done. 
Qed. 

Lemma triple_setBYTESep (p:PTR) (v w:BYTE) :
  forall S,
  TRIPLE (p:->v ** S) (setBYTEInProcState p w) (p:->w ** S).
Proof. 
move => S. 
rewrite 2!pointsToBYTE_byteIs. 

move => s pre. rewrite /setBYTEInProcState/setInProcState/writeMem/=. 
rewrite (byteIsMapped pre). 
eexists _. eexists _. 
split; last first. apply (separateSetBYTE _ pre). done. 
Qed. 

Lemma triple_setBYTEbind (v w: BYTE) (p: DWORD) Q (W: WriterTm unit) Q' :
  TRIPLE
  (p :-> w ** Q)
  (let!s = getProcState; 
   if writeMemTm W s (next p) is Some(_, m') 
   then setProcState {| registers := s; flags := s; memory := m' |}
   else raiseUnspecified) 
  (p :-> w ** Q') ->
 TRIPLE 
 (p :-> v ** Q) 
  (let!s = getProcState; 
   if writeMemTm (do! writeNext w; W) s p is Some(_, m') 
   then setProcState {| registers := s; flags := s; memory := m' |}
   else raiseUnspecified) 
  (p :-> w ** Q'). 
Proof. 
rewrite 2!pointsToBYTE_byteIs.
move => H. 
move => s pre.   
simpl. 
rewrite (byteIsMapped pre). 
have post := separateSetBYTE w pre. 
specialize (H _ post). 
destruct H as [f' H]. simpl in H. 
exists f'.  
by case E: (writeMemTm W _ _) => [[p' m] |]; rewrite E in H. 
Qed. 

Lemma triple_setDWORDSep (p:PTR) (v w:DWORD) S:
  TRIPLE (p:->v ** S) (setDWORDInProcState p w) (p:->w ** S).
Proof.
elim Ev: (@split4 8 8 8 8 v) => [[[v3 v2] v1] v0]. 
elim Ew: (@split4 8 8 8 8 w) => [[[w3 w2] w1] w0]. 
rewrite /setDWORDInProcState/setInProcState. 
rewrite /writeNext/writeDWORD/writeMem Ew.

have PTv := pointsToDWORD_asBYTES v. 
have PTw := pointsToDWORD_asBYTES w. 
rewrite Ev in PTv. 
rewrite Ew in PTw. 
rewrite -PTv -PTw {PTv PTw}.  

rewrite 2!pointsTo_consBYTE 2!sepSPA. 
apply triple_setBYTEbind. 

destruct (next _).
rewrite [in X in TRIPLE X _ _]sepSPC sepSPA pointsTo_consBYTE sepSPA.
rewrite [in X in TRIPLE _ _ X]sepSPC sepSPA pointsTo_consBYTE sepSPA. 
apply triple_setBYTEbind. 

destruct (next _).  
rewrite [in X in TRIPLE X _ _]sepSPC sepSPA pointsTo_consBYTE !sepSPA.
rewrite [in X in TRIPLE _ _ X]sepSPC sepSPA pointsTo_consBYTE !sepSPA. 
apply triple_setBYTEbind. 

destruct (next _). 
rewrite [in X in TRIPLE X _ _]sepSPC sepSPA pointsTo_consBYTE !sepSPA.
rewrite [in X in TRIPLE _ _ X]sepSPC sepSPA pointsTo_consBYTE !sepSPA. 
apply triple_setBYTEbind. 

(* Naming and direction at odds with pointsTo_consBYTE *)
rewrite <-pointsToNil. 
rewrite /writeMem !empSPL.
move => s pre. exists s. eexists _. by destruct s.  

rewrite hwmPointsTo_consBYTE. eapply triple_roc_pre. instantiate (1:=lfalse); by ssimpl. done. 
rewrite hwmPointsTo_consBYTE. eapply triple_roc_pre. instantiate (1:=lfalse); by ssimpl. done. 
rewrite hwmPointsTo_consBYTE. eapply triple_roc_pre. instantiate (1:=lfalse); by ssimpl. done. 
Qed. 

Lemma triple_setDWORDorBYTESep dword (p:PTR) (v w: DWORDorBYTE dword) S :
  TRIPLE (p:->v ** S) (setDWORDorBYTEInProcState p w) (p:->w ** S). 
Proof. destruct dword. apply triple_setDWORDSep. apply triple_setBYTESep. Qed.

Lemma triple_doSetDWORDSep (p:PTR) (v w: DWORD) c Q S :
  TRIPLE (p:->w ** S) c Q ->  
  TRIPLE (p:->v ** S) (do! setDWORDInProcState p w; c) Q.
Proof. move => T s pre. 
destruct (triple_setDWORDSep w pre) as [f [o [H1 H2]]]. 
specialize (T _ H2). 
destruct T as [f' [o' H3]]. exists f'. rewrite /= H1.
eexists _.  
destruct (c f). destruct H3.  split; last done. by injection H => -> ->. 
Qed. 

Ltac triple_apply lemma :=
 ptsimpl;
 repeat do [try rewrite -> assoc | try rewrite -> id_l];
  eapply triple_roc; [| |eapply lemma];
    instantiate; [ssimpl; try reflexivity|..];
    instantiate; [try reflexivity; ssimpl; try reflexivity|..].


