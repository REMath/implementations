(*===========================================================================
    Predicates over system state: actually predicates over a subset of
    processor state, in order to define separating conjunction nicely.
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype fintype finfun seq tuple.
Require Import bitsrep pfun reg mem flags ioaction.
Require Import pmap pmapprops.
Require Import Setoid CSetoid Morphisms.


(* Importing this file really only makes sense if you also import ilogic, so we
   force that. *)
Require Export ilogic bilogic ilogicss sepalg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import FunctionalExtensionality. 

(*---------------------------------------------------------------------------
    Define partial states and lift definitions and lemmas from partial functions

    A partial state consists of
    - a partial register file
    - a partial memory map
    - a partial flag file
    - trace of actions
  ---------------------------------------------------------------------------*)

Inductive Frag := Registers | Memory | Flags | Traces.
Definition fragDom d :=
  match d with 
  | Registers => AnyReg
  | Memory => PTR
  | Flags => Flag
  | Traces => Chan
  end.

Definition fragTgt d :=
  match d with 
  | Registers => DWORD
    (* None = "memory not mapped" or "memory inaccessible".
       Access to such memory should cause a trap handler to be executed *)
  | Memory => option BYTE

    (* FlagUnspecified = "unspecified", and might not even be stable
       (e.g. two reads of the flag won't necessarily be consistent) *)
  | Flags => FlagVal
  | Traces => seq (bool * BYTE)
  end.

(* None = "not described" for the purposes of separation logic *)
Definition PState := forall f: Frag, fragDom f -> option (fragTgt f).

(*
Structure StateFrag : Type := {frag:Frag; carrier:>Type}.
Canonical Structure RegStateFrag := @Build_StateFrag Registers AnyReg.
Canonical Structure FlagStateFrag := Build_StateFrag Flags Flag.
*)


Definition emptyPState : PState := fun _ => empFun _. 

Definition addRegToPState (s:PState) (r:AnyReg) (v:DWORD) : PState := 
  fun (f:Frag) =>
  match f as f in Frag return fragDom f -> option (fragTgt f) with
  | Registers => fun r' => if r == r' then Some v else s Registers r'
  | Flags => s Flags
  | Memory => s Memory
  | Traces => s Traces
  end.

Definition addFlagToPState (s:PState) f v : PState := 
  fun (fr:Frag) =>
  match fr as fr in Frag return fragDom fr -> option (fragTgt fr) with
  | Registers => s Registers
  | Flags => fun f' => if f == f' then Some v else s Flags f'
  | Memory => s Memory
  | Traces => s Traces
  end.

(*  
Definition undefRegToPState s r := 
  mkPState (fun r' => if r==r' then None else pregisters s r') (pmemory s) (pflags s) (ptrace s).
*) 

(*
Definition addGenRegToPState s r v := 
  mkPState (fun r' => if r==r' then v else pregisters s r') (pmemory s) (pflags s) (ptrace s). 
*)


Definition addBYTEToPState (s:PState) p b : PState := 
  fun (fr:Frag) =>
  match fr as fr in Frag return fragDom fr -> option (fragTgt fr) with
  | Memory => fun p' => if p == p' then Some (Some b) else s Memory p'
  | Registers => s Registers
  | Flags => s Flags
  | Traces => s Traces
  end.

Definition extendState (s1 s2: PState) : PState := fun f => extend (s1 f) (s2 f). 
Definition stateIncludedIn (s1 s2: PState) := forall f, includedIn (s1 f) (s2 f). 

Lemma stateIncludedIn_trans (s1 s2 s3:PState) : 
  stateIncludedIn s1 s2 -> stateIncludedIn s2 s3 -> stateIncludedIn s1 s3.
Proof. move => H1 H2 f. by apply: includedIn_trans. Qed.

(*
Lemma stateIncludedIn_modReg : forall (s1 s2:PState) (r:AnyReg) x, stateIncludedIn s1 s2 ->
stateIncludedIn (addRegToPState s1 r x) (addRegToPState s2 r x).
Proof.
rewrite /stateIncludedIn /addRegToPState /includedIn; simpl; move => s1 s2 r v Hincl.
destruct Hincl.
split. move => r0 y.
assert (r === r0 \/ r != r0).
destruct r; destruct r0; auto.
destruct r; destruct r0; auto.
destruct n; destruct n0; auto.
destruct H1 as [H1 | H1].
rewrite H1; auto.
rewrite (negPf H1). auto.
auto.
Qed.

Lemma stateIncludedIn_modGenReg : forall (s1 s2:PState) (r:AnyReg) v, stateIncludedIn s1 s2 ->
stateIncludedIn (addGenRegToPState s1 r v) (addGenRegToPState s2 r v).
Proof.
rewrite /stateIncludedIn /addGenRegToPState /includedIn; simpl; move => s1 s2 r v Hincl.
destruct Hincl.
split. move => r0.
assert (r === r0 \/ r != r0).
destruct r; destruct r0; auto.
destruct r; destruct r0; auto.
destruct n; destruct n0; auto.
destruct H1 as [H1 | H1].
rewrite H1; auto.
rewrite (negPf H1). auto.
auto.
Qed.
*)

Definition stateSplitsAs (s s1 s2: PState) := forall f, splitsAs (s f) (s1 f) (s2 f).

Lemma stateSplitsAsIncludes s s1 s2 :
  stateSplitsAs s s1 s2 -> stateIncludedIn s1 s /\ stateIncludedIn s2 s. 
Proof. move => H. 
split => f. apply (proj1 (splitsAsIncludes (H f))). apply (proj2 (splitsAsIncludes (H f))).  
Qed. 

Lemma stateSplitsAsExtendL s s1 s2 s3 s4 : stateSplitsAs s s1 s2 -> stateSplitsAs s2 s3 s4 ->
  stateSplitsAs s (extendState s1 s3) s4.
Proof. move => H1 H2 f. by apply: splitsAsExtendL. Qed. 

Lemma stateSplitsAsExtends s s1 s2 : stateSplitsAs s s1 s2 -> s = extendState s1 s2.
Proof.
  move => H.
  extensionality f.
  extensionality x.
  exact: splitsAsExtend.
Qed.

Lemma stateSplitsAs_s_emp_s s : stateSplitsAs s emptyPState s. 
Proof. move => f. apply: splitsAs_f_emp_f. Qed. 

Lemma stateSplitsAs_s_s_emp s : stateSplitsAs s s emptyPState. 
Proof. move => f. apply: splitsAs_f_f_emp. Qed. 

Lemma stateSplitsAs_s_emp_t s t : stateSplitsAs s emptyPState t -> s = t.
Proof. move => H. extensionality f. 
apply: functional_extensionality. apply: splitsAs_f_emp_g. apply: H. 
Qed. 

Lemma stateSplitsAs_s_t_emp s t : stateSplitsAs s t emptyPState -> s = t.
Proof. move => H. extensionality f. 
apply: functional_extensionality. apply: splitsAs_f_g_emp. apply: H. 
Qed. 

Lemma stateSplitsAs_s_t_s s t: stateSplitsAs s t s -> t = emptyPState.
Proof. move => H. extensionality f. 
apply: functional_extensionality. apply: splitsAs_f_g_f. apply H. 
Qed. 

Lemma stateSplitsAs_s_s_t s t: stateSplitsAs s s t -> t = emptyPState.
Proof. move => H. extensionality f. 
apply: functional_extensionality. apply: splitsAs_f_f_g. apply H. 
Qed. 

Lemma stateSplitsAsIncludedInSplitsAs f f1 f2 g :
    stateSplitsAs f f1 f2 -> stateIncludedIn f g -> exists g1, exists g2, 
    stateSplitsAs g g1 g2 /\ stateIncludedIn f1 g1 /\ stateIncludedIn f2 g2.
Proof. move => H1 H2. 
exists f1. 
set g2 := fun fr => fun x => if f1 fr x is Some _ then None else if f2 fr x is Some y then Some y else g fr x. 
exists g2.
split => //.  
move => fr. apply (splitsAsIncludedInSplitsAs (H1 fr) (H2 fr)).  
split => //. 
move => fr. apply (splitsAsIncludedInSplitsAs (H1 fr) (H2 fr)).  
Qed. 

(* a version more faithful to [splitsAsIncludedInSplitsAs] *)
Lemma stateSplitsAsIncludedInSplitsAs' (f f1 f2 g: PState) :
  stateSplitsAs f f1 f2 -> stateIncludedIn f g -> 
  exists g2,
  stateSplitsAs g f1 g2 /\ stateIncludedIn f2 g2.
Proof.
  move=> Hsplit Hinc.
  exists (fun fr => fun x => if f1 fr x is Some _ then None else if f2 fr x is Some y then Some y else g fr x).
  split => fr; by have [? ?] := splitsAsIncludedInSplitsAs (Hsplit fr) (Hinc fr).
Qed.

Lemma stateSplitsAs_functional s1 s2 h i : stateSplitsAs h s1 s2 -> stateSplitsAs i s1 s2 -> h = i.
Proof. move => H1 H2.
extensionality f.
specialize (H1 f). specialize (H2 f).
have H:= splitsAs_functional H1 H2.  
apply: functional_extensionality. 
move => x. by specialize (H x). 
Qed. 

Lemma stateSplitsAs_functionalArg s s1 s2 s3 : stateSplitsAs s s2 s1 -> stateSplitsAs s s3 s1 -> s2 = s3. 
Proof. move => H1 H2. 
extensionality f. 
specialize (H1 f). specialize (H2 f). 
have H := splitsAs_functionalArg H1 H2. 
apply: functional_extensionality. 
move => x. by specialize (H x). 
Qed. 

Lemma stateSplitsAs_commutative s s1 s2 :
  stateSplitsAs s s1 s2 -> stateSplitsAs s s2 s1.
Proof. move => H f. by apply: splitsAs_commutative. Qed. 

Lemma stateSplitsAs_associative s s1 s2 s3 s4 :
  stateSplitsAs s s1 s2 ->
  stateSplitsAs s2 s3 s4 ->
  exists s5, 
  stateSplitsAs s s3 s5 /\
  stateSplitsAs s5 s1 s4.
Proof. move => H1 H2.
set s5 := fun fr => fun x => if s4 fr x is Some y then Some y else s1 fr x. 
exists s5. 
split; move => fr; apply (splitsAs_associative (H1 fr) (H2 fr)). 
Qed. 

Definition restrictState (s: PState) (p: forall f:Frag, fragDom f -> bool) : PState := 
  fun f => fun x => if p f x then s f x else None. 

Lemma stateSplitsOn (s: PState) p :
stateSplitsAs s (restrictState s p) 
                (restrictState s (fun f => fun x => ~~p f x)). 
Proof. move => f x. 
case E: (s f x) => [a |] => //. rewrite /restrictState.
case E': (p f x). rewrite E. left; done. right. by rewrite E.
rewrite /restrictState.  rewrite E. 
by case (p f x). 
Qed. 

(* Builds a total memory with the same mappings as the partial memory s.
   Locations that are not in s will be unmapped in the result. *)
Definition memComplete (s: PState) : Mem :=
  pmap_of (fun p =>
    match s Memory p with
    | Some (Some v) => Some v
    | _ => None
    end).

Lemma memComplete_inverse (s: PState) p v:
  s Memory p = Some v -> (memComplete s) p = v.
Proof.
  move=> Hsp. rewrite /memComplete. rewrite pmap_of_lookup.
  rewrite Hsp. by destruct v.
Qed.


(*---------------------------------------------------------------------------
    State predicates, and logical connectives
    We start without restrictions on predicates, roughly the "assertions" of
    Reynolds' "Introduction to Separation Logic", 2009.
  ---------------------------------------------------------------------------*)

Instance PStateEquiv : Equiv PState := {
   equiv s1 s2 := forall f, s1 f =1 s2 f
}.

Instance PStateType : type PState.
Proof.
  split.
  move => s f x; reflexivity.
  move => s1 s2 Hs f x; specialize (Hs f x); symmetry; assumption.
  move => s1 s2 s3 H12 H23 f x; specialize (H12 f x); specialize (H23 f x).
  transitivity (s2 f x); assumption.
Qed.

Instance addRegToPStateEquiv_m :
  Proper (equiv ==> eq ==> eq ==> equiv) addRegToPState.
Proof.
  move => p q Hpeq r1 r2 Hr1eqr2 w1 w2 Hw1eqw2 f x; subst.
  destruct f; simpl; rewrite Hpeq; reflexivity.
Qed.

Instance addFlagToPStateEquiv_m :
  Proper (equiv ==> eq ==> eq ==> equiv) addFlagToPState.
Proof.
  move => p q Hpeq r1 r2 Hr1eqr2 w1 w2 Hw1eqw2 f x; subst.
  destruct f; simpl; rewrite Hpeq; reflexivity.
Qed.

Instance addBYTEToPStateEquiv_m :
  Proper (equiv ==> eq ==> eq ==> equiv) addBYTEToPState.
Proof.
  move => p q Hpeq r1 r2 Hr1eqr2 w1 w2 Hw1eqw2 f x; subst.
  destruct f; simpl; rewrite Hpeq; reflexivity.
Qed.

Instance extendStateEquiv_m :
  Proper (equiv ==> equiv ==> equiv) extendState.
Proof.
  move => p q Hpeqq r1 r2 Hr1eqr2 f d.
  unfold extendState, extend.
  rewrite Hr1eqr2. destruct (r2 f d); [|rewrite Hpeqq]; reflexivity.
Qed.

Instance stateIncludeInEquiv_m :
  Proper (equiv ==> equiv ==> iff) stateIncludedIn.
Proof.
  move => p q Hpeqq r1 r2 Hr1eqr2.
  split; move => H f d y Heq; specialize (H f d y);
  [rewrite <- Hpeqq in Heq | rewrite Hpeqq in Heq];
  specialize (H Heq); [rewrite <- Hr1eqr2| rewrite Hr1eqr2];
  assumption.
Qed.

Lemma state_extensional (s1 s2: PState) : (forall f, s1 f =1 s2 f) -> s1 === s2.
Proof. unfold equiv, PStateEquiv; move => H f; apply H. Qed.

Program Definition my_sa_mul : (PState -s> PState -s> PState -s> Prop) := 
  lift3s (fun s1 s2 s => forall f, splitsAs (s f) (s1 f) (s2 f)) _ _ _.
Next Obligation.
  intros t1 t2 HEqt; unfold equiv, PStateEquiv in HEqt.
  split; intros; [rewrite <- HEqt | rewrite HEqt]; apply H.
Qed.
Next Obligation.
  intros t1 t2 HEqt; unfold equiv, PStateEquiv in HEqt;
  split; simpl; intros; [rewrite <- HEqt | rewrite HEqt]; apply H.
Qed.
Next Obligation.
  intros t1 t2 HEqt; unfold equiv, PStateEquiv in HEqt.
  split; simpl; intros; [rewrite <- HEqt | rewrite HEqt]; apply H.
Qed.

Instance PStateSepAlgOps: SepAlgOps PState := {
  sa_unit := emptyPState;
  sa_mul s1 s2 s := forall f, splitsAs (s f) (s1 f) (s2 f)
}.

Instance PStateSepAlg : SepAlg PState.
Proof.
  split.
  + move => a b c d Habc Hceqd f; specialize (Hceqd f); rewrite <- Hceqd.
    apply Habc.
  + move => a b c d Habc Habd f.
    eapply splitsAs_functional; [apply Habc | apply Habd].
  + move => a b c Hbc d. split.
    - move => Habd f; specialize (Hbc f); rewrite <- Hbc; apply Habd.
    - move => Hacd f; specialize (Hbc f); rewrite Hbc; apply Hacd.
  + split; intros; by apply stateSplitsAs_commutative.
  + move => a b c bc abc H1 H2. eapply stateSplitsAs_associative. apply H1. apply H2.
  + intros; apply stateSplitsAs_s_s_emp.
Qed.

Definition SPred := ILFunFrm PState Prop. 

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.
Local Existing Instance SABIOps.
Local Existing Instance SABILogic.

Instance sepILogicOps : ILogicOps SPred := _.
Instance sepLogicOps : BILOperators SPred := _.
Instance sepLogic : BILogic SPred := _.

Implicit Arguments mkILFunFrm [[e] [ILOps]].

Definition mkSPred (P : PState -> Prop) 
        (f : forall t t' : PState, t === t' -> P t |-- P t') : SPred :=
  mkILFunFrm PState Prop P f.

Implicit Arguments mkSPred [].


(*---------------------------------------------------------------------------
    Register-is predicate
  ---------------------------------------------------------------------------*)

Program Definition regIs r x : SPred := mkSPred (equiv (addRegToPState emptyPState r x)) _.
Next Obligation.
  rewrite <- H. assumption.
Qed.

Notation "r '~=' x" := (regIs r x) (at level 55, no associativity, format "r '~=' x"): spred_scope.
Definition regAny r : SPred := lexists (regIs r). 
Notation "r '?'" := (regAny r) (at level 2, format "r '?'"): spred_scope.

Open Scope spred_scope.

(*---------------------------------------------------------------------------
    Flag-is predicate
  ---------------------------------------------------------------------------*)
Program Definition flagIs f b : SPred :=
  mkSPred (equiv (addFlagToPState emptyPState f b)) _.
Next Obligation.
  rewrite <- H; assumption.
Qed.

Definition flagAny f : SPred := lexists (flagIs f).

Program Definition byteIs p b : SPred := 
  mkSPred (equiv (addBYTEToPState emptyPState p b)) _.
Next Obligation.
  rewrite <- H; assumption.
Qed.

Definition byteAny p : SPred := lexists (byteIs p). 

Instance flagIsEquiv_m :
  Proper (eq ==> eq ==> CSetoid.equiv ==> iff) flagIs.
Proof.
  intros n m Hneqm f g Hbeqc p q Hpeqq; subst.
  split; simpl; rewrite <- Hpeqq; tauto.
Qed.

Instance byteIsEquiv_m :
  Proper (eq ==> eq ==> CSetoid.equiv ==> iff) byteIs.
Proof.
  intros n m Hneqm b c Hbeqc p q Hpeqq; subst.
  split; simpl; rewrite <- Hpeqq; tauto.
Qed.

(*---------------------------------------------------------------------------
    Iterated separating conjunction
  ---------------------------------------------------------------------------*)
Fixpoint isc {A} (I: seq A) (F: A -> SPred) :=
  match I with
  | nil => empSP
  | i :: I' => F i ** isc I' F
  end.

Lemma isc_cat {A} (I J: seq A) F :
  isc (I ++ J) F -|- isc I F ** isc J F.
Proof.
  elim: I.
  - simpl; rewrite sepSPC. rewrite empSPR. reflexivity.
  - move=> i I IH /=. by rewrite IH sepSPA.
Qed.

Lemma isc_snoc {A} (I: seq A) i F :
  isc (I ++ [:: i]) F -|- isc I F ** F i.
Proof. rewrite isc_cat /=. by rewrite empSPR. Qed.

(*---------------------------------------------------------------------------
    Strictly exact assertions

    See Section 2.3.2 In Reynolds's "Introduction to Separation Logic" online
    lecture notes.
    http://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/cs818A3-11.html
  ---------------------------------------------------------------------------*)

Class StrictlyExact (P: SPred) := strictly_exact:
  forall s s', P s -> P s' -> s === s'.

Instance StrictlyExactRegIs r v: StrictlyExact (regIs r v). 
Proof. move => s s'. simpl. by move ->. Qed. 

Instance StrictlyExactFlagIs f v: StrictlyExact (flagIs f v). 
Proof. move => s s'. simpl. by move ->. Qed. 

Instance StrictlyExactByteIs p v: StrictlyExact (byteIs p v). 
Proof. move => s s'. simpl. by move ->. Qed. 

Instance StrictlyExactSep P Q `{PH: StrictlyExact P} `{QH: StrictlyExact Q}
  : StrictlyExact (P**Q).
Proof. move => s s' [s1 [s2 [H1 [H2 H3]]]] [s1' [s2' [H1' [H2' H3']]]]. 
specialize (PH s1 s1' H2 H2'). 
specialize (QH s2 s2' H3 H3').
rewrite -> PH, QH in H1. 
by rewrite (stateSplitsAsExtends H1) (stateSplitsAsExtends H1'). 
Qed. 

Instance StrictlyExactEmpSP : StrictlyExact empSP. 
Proof. move => s s' H H'. 
destruct H as [H _]. destruct H' as [H' _].
by rewrite -H -H'. 
Qed. 

Instance StrictlyExactConj P Q `{PH: StrictlyExact P} `{QH: StrictlyExact Q}
  : StrictlyExact (P //\\ Q).
Proof. move => s s' [H1 H2] [H1' H2'].  
by apply (PH s s' H1 H1'). 
Qed. 

Class Precise (P: SPred) := precise:
  forall s s1 s2, stateIncludedIn s1 s -> stateIncludedIn s2 s -> P s1 -> P s2 -> s1 === s2. 

Instance PreciseStrictlyExact P `{PH: StrictlyExact P} : Precise P. 
Proof. move => s s1 s2 H1 H2. intuition. Qed. 

Corollary Distributive P0 P1 Q `{QH: Precise Q} :
  (P0 ** Q) //\\ (P1 ** Q) |-- (P0 //\\ P1) ** Q.
Proof. 
unfold "|--". rewrite /sepILogicOps/ILFun_Ops. move => s [H0 H1]. 
destruct H0 as [s0 [s0' [H0a [H0b H0c]]]]. 
destruct H1 as [s1 [s1' [H1a [H1b H1c]]]].
have SSI0 := stateSplitsAsIncludes H0a. 
have SSI1 := stateSplitsAsIncludes H1a. 
destruct SSI0 as [SSI0a SSI0b]. 
destruct SSI1 as [SSI1a SSI1b]. 
have QH1 := (QH _ _ _ SSI0b SSI1b H0c H1c). 
exists s0. exists s1'. 
split. rewrite -> QH1 in H0a. 

exact H0a. 
split. split. exact H0b. rewrite -> QH1 in SSI0b. 
rewrite -> QH1 in H0a.
rewrite <- (stateSplitsAs_functionalArg H1a H0a). exact H1b. 
exact H1c. 
Qed. 

Program Definition eq_pred s := mkSPred (fun s' => s === s') _.
Next Obligation.
  rewrite <- H; assumption.
Qed.

Local Transparent ILFun_Ops.
Instance eq_pred_equiv_lentails :
  Proper (equiv ==> lentails) eq_pred.
Proof.
  move => s t Hseqt u Hsequ; simpl in *.
  rewrite <- Hseqt. assumption.
Qed.

Instance eq_pred_equiv_lequiv :
  Proper (equiv ==> lequiv) eq_pred.
Proof.
  split; apply eq_pred_equiv_lentails; [|symmetry]; assumption.
Qed.

Instance eq_pred_eq_pred_lentails :
  Proper (eq_pred ==> lentails) eq_pred.
Proof.
  move => s t Hseqt u Hsequ; simpl in *.
  rewrite <- Hseqt. assumption.
Qed.

Instance eq_pred_eq_pred_lequiv :
  Proper (eq_pred ==> lequiv) eq_pred.
Proof.
  split; apply eq_pred_equiv_lentails; [|symmetry]; assumption.
Qed.

Lemma lentails_eq (P : SPred) t :
  P t <-> eq_pred t |-- P.
Proof.
  split.
  - simpl. intros H x H1.
    assert (P t |-- P x) as H2 by (eapply ILFunFrm_closed; assumption).
    apply H2; assumption.
  - simpl; intros; firstorder.
Qed.


(*---------------------------------------------------------------------------
    A partial application of [eq] is a predicate
  ---------------------------------------------------------------------------*)

Lemma stateSplitsAs_eq s s1 s2:
  sa_mul s1 s2 s ->
  eq_pred s1 ** eq_pred s2 -|- eq_pred s.
Proof.
  split.
  - move=> s' [s1' [s2' [Hs' [Hs1' Hs2']]]].
    Opaque sa_mul.
    simpl in *.
    rewrite <- Hs1', <- Hs2' in Hs'.
    eapply sa_mul_eqR; eassumption.
  - simpl. move=> s' H1. 
    rewrite -> H1 in H.
    exists s1; exists s2; done.
Qed.

Lemma ILFun_exists_eq (P : SPred) :
  P -|- Exists s, P s /\\ eq_pred s.
Proof.
  split; intros s Hs.
  - exists s. constructor; simpl; intuition.
  - simpl in *; destruct Hs as [x [Hp Hs]].
    assert (P x |-- P s) as H by (eapply ILFunFrm_closed; assumption).
    by apply H.
Qed.

Global Opaque PStateSepAlgOps.