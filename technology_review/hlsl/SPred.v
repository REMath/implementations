(*===========================================================================
    Predicates over system state: actually predicates over a subset of
    processor state, in order to define separating conjunction nicely.
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype fintype finfun seq tuple.
Require Import bitsrep pfun reg mem flags action.
Require Import pmap pmapprops.

(* Importing this file really only makes sense if you also import ilogic, so we
   force that. *)
Require Export ilogic.

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


Lemma state_extensional (s1 s2: PState) : (forall f, s1 f =1 s2 f) -> s1 = s2.
Proof. move => H. extensionality f. apply functional_extensionality. apply H. Qed. 

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
assert (r == r0 \/ r != r0).
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
assert (r == r0 \/ r != r0).
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
Transparent ILFun_Ops.

Definition SPred := PState -> Prop. 
Instance ILSPred: ILogic SPred := _.

(* Spatial connectives *)
Definition empSP                   : SPred := eq emptyPState.
Definition sepSP     (P Q : SPred) : SPred := fun s =>
   exists s1, exists s2, stateSplitsAs s s1 s2 /\ P s1 /\ Q s2. 
Definition wandSP    (P Q : SPred) : SPred := fun s =>
  forall s', forall ss', stateSplitsAs ss' s s' -> P s' -> Q ss'.

Infix "**"     := sepSP (at level 75, right associativity).
Infix "-*"     := wandSP (at level 77, right associativity).

(*---------------------------------------------------------------------------
    Congruence properties of connectives wrt entailment and equivalence
  ---------------------------------------------------------------------------*)

Require Import Setoid Morphisms RelationClasses.

Add Morphism sepSP with signature lequiv ==> lequiv ==> lequiv as sepSP_mor.
Proof. firstorder. Qed. 

Add Morphism wandSP with signature lequiv ==> lequiv ==> lequiv as wandSP_mor.
Proof. firstorder. Qed. 

Add Morphism sepSP with signature lentails ++> lentails ++> lentails as entails_sepSP.
Proof. firstorder. Qed. 

Add Morphism wandSP with signature lentails --> lentails ++> lentails as entails_wandSP.
Proof. firstorder. Qed.

(*---------------------------------------------------------------------------
    SPred is a complete BI algebra
  ---------------------------------------------------------------------------*)

(* sep *)
Lemma sepSPC1 P Q:
  P ** Q |-- Q ** P.
Proof.
  move => s [s1 [s2 [Hsplit [HP HQ]]]].
  do 2 apply: ex_intro.
  eauto using stateSplitsAs_commutative.
Qed.

Lemma sepSPC P Q:
  P ** Q -|- Q ** P.
Proof. split; apply: sepSPC1. Qed.
  
Lemma sepSPA2 P Q R:
  P ** (Q ** R) |-- (P ** Q) ** R.
Proof.
  rewrite [Q ** R]sepSPC -[(P ** Q) ** R]sepSPC.
  move => s [sP [sRQ [HP_RQ [HP HRQ]]]].
  case: HRQ => [sR [sQ [HR_Q [HR HQ]]]].
  have [sPQ [HR_PQ HP_Q]] := stateSplitsAs_associative HP_RQ HR_Q.
  exists sR; exists sPQ.
  split; first done.
  split; first done.
  by exists sP; exists sQ.
Qed.

Lemma sepSPA1 P Q R:
  (P ** Q) ** R |-- P ** (Q ** R).
Proof.
  (* a commutative connective that's associative in one direction is also
     associative in the other. *)
  rewrite [_**R]sepSPC [P**Q]sepSPC.
  rewrite ->sepSPA2.
  rewrite [_**P]sepSPC [R**Q]sepSPC. done.
Qed.

Lemma sepSPA P Q R:
  (P ** Q) ** R -|- P ** (Q ** R).
Proof.
  split; first apply: sepSPA1; apply: sepSPA2.
Qed.

(* emp *)
Lemma empSPR P:
  P ** empSP -|- P.
Proof.
  split => s => [[s1 [s2 [Hsplit [HP Hemp]]]] | HP].
  - rewrite -Hemp in Hsplit.
    erewrite stateSplitsAs_s_t_emp; by eassumption.
  - do 2 apply: ex_intro.
    by split; first apply stateSplitsAs_s_s_emp.
Qed.

Lemma empSPL P:
  empSP ** P -|- P.
Proof.
  rewrite sepSPC. exact: empSPR.
Qed.

(* wand (right adjoint of sep) *)
Lemma wandSPAdj P Q C:
  C ** P |-- Q ->
  C |-- P -* Q.
Proof. firstorder. Qed.

Lemma sepSPAdj P Q C:
  C |-- P -* Q ->
  C ** P |-- Q.
Proof. firstorder. Qed.

(* separating conjunction preserves colimits (existentials, disjunctions, false)
 *)
Lemma sepSP_falseL P: lfalse ** P -|- lfalse.
Proof. firstorder. Qed.

Lemma sepSP_falseR P: P ** lfalse -|- lfalse.
Proof. firstorder. Qed.

(*---------------------------------------------------------------------------
    A partial application of [eq] is a predicate
  ---------------------------------------------------------------------------*)

Lemma stateSplitsAs_eq s s1 s2:
  stateSplitsAs s s1 s2 ->
  eq s1 ** eq s2 -|- eq s.
Proof.
  split.
  - move=> s' [s1' [s2' [Hs' [Hs1' Hs2']]]]. subst s1' s2'.
    rewrite (@stateSplitsAsExtends s s1 s2) => //.
    by rewrite (@stateSplitsAsExtends s' s1 s2).
  - move=> s' <-. exists s1. exists s2. done.
Qed.

(*---------------------------------------------------------------------------
    Register-is predicate
  ---------------------------------------------------------------------------*)

Definition regIs r x := eq (addRegToPState emptyPState r x).

Notation "r '~=' x" := (regIs r x) (at level 55, no associativity, format "r '~=' x").
Definition regAny r := lexists (regIs r). 
Notation "r '?'" := (regAny r) (at level 2, format "r '?'").

(*---------------------------------------------------------------------------
    Flag-is predicate
  ---------------------------------------------------------------------------*)
(*Definition flagIs f v : SPred := fun s => s Flags f = Some v.

Lemma flagIsClosed f v : isClosed (flagIs f v).
Proof. rewrite /isClosed/flagIs. move => s s' ss'. specialize (ss' Flags). intuition. Qed. 

*)
Definition flagIs f b := eq (addFlagToPState emptyPState f b).

Definition flagAny f := lexists (flagIs f).

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
  - rewrite empSPL. reflexivity.
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
  forall s s', P s -> P s' -> s = s'.


