(*===========================================================================
    Specification logic -- step-indexed and with hidden frames

    This is a step-indexed version of the specification logic defined in Chapter
    3 of Krishnaswami's thesis, which is adapted from Birkedal et al.
    A specification S is a predicate on nat and SPred, where it holds for a pair
    (k,P) if it denotes a "desirable" machine execution for up to k steps
    starting from any machine configuration that has a sub-state satisfying P.
    The meaning of "desirable" depends on S; it might, for example, mean "safe
    under certain assumptions". Note the wording "up to" and "sub-state" above:
    they suggest that formally, S must be closed under decreasing k and starring
    on assertions to P.

    The utility of this is to get a higher-order frame rule in the specification
    logic, which is very valuable for a low-level language that does not have
    structured control flow and therefore does not have the structure required
    to define a Hoare triple. When frames cannot be fixed by the symmetry of
    pre- and postconditions, they must float freely around the specification
    logic, which is exactly what the higher-order frame rule allows -- see
    [spec_frame].
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype tuple seq fintype.
Require Import bitsrep procstate procstatemonad SPred septac.
Require Import instr eval monad monadinst reader step cursor.

(* Importing this file really only makes sense if you also import ilogic, so we
   force that. *)
Require Export ilogic later.
Transparent ILPre_Ops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Setoid RelationClasses Morphisms.

(* The ssreflect inequalities on nat are just getting in the way here. They
   don't work with non-Equivalence setoids. *)
Local Open Scope coq_nat_scope.

(* The natural numbers in descending order. *)
(*
Instance ge_Pre: PreOrder ge.
Proof. repeat constructor. hnf. eauto with arith. Qed.
*)
(* SPred, ordered by extension with **. *)
Definition extSP (P Q: SPred) := exists R, (P ** R) -|- Q.
Instance extSP_Pre: PreOrder extSP.
Proof.
  split.
  - exists empSP. apply empSPR.
  - move=> P1 P2 P3 [R1 H1] [R2 H2]. exists (R1 ** R2).
    by rewrite <-H1, sepSPA in H2.
Qed.

Instance extSP_impl_m :
  Proper (extSP --> extSP ++> Basics.impl) extSP.
Proof.
  rewrite /extSP. intros P P' [RP HP] Q Q' [RQ HQ] [R H].
  eexists. rewrite -HQ -H -HP. split; by ssimpl.
Qed.

Instance extSP_iff_m :
  Proper (lequiv ==> lequiv ==> iff) extSP.
Proof.
  rewrite /extSP. intros P P' HP Q Q' HQ.
  setoid_rewrite HP. setoid_rewrite HQ. done.
Qed.

Instance extSP_sepSP_m :
  Proper (extSP ++> extSP ++> extSP) sepSP.
Proof.
  rewrite /extSP. intros P P' [RP HP] Q Q' [RQ HQ].
  eexists. rewrite -HP -HQ. split; by ssimpl.
Qed.

Instance subrelation_equivSP_extSP: subrelation lequiv extSP.
Proof. rewrite /extSP => P P' HP. exists empSP. rewrite HP. apply empSPR. Qed.

Instance subrelation_equivSP_inverse_extSP: subrelation lequiv (inverse extSP).
Proof. rewrite /extSP => P P' HP. exists empSP. rewrite HP. apply empSPR. Qed.

Hint Extern 0 (extSP ?P ?P) => reflexivity.

(*
   Definition of "spec" and properties of it as a logic
*)
Section ILSpecSect.

Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.
Local Existing Instance ILLaterPreOps.
Local Existing Instance ILLaterPre.

Definition spec := ILPreFrm ge (ILPreFrm extSP Prop).
Global Instance ILSpecOps: ILLOperators spec := _.
Global Instance ILOps: ILogicOps spec := _.
Global Instance ILSpec: ILLater spec := _.

End ILSpecSect.

Local Obligation Tactic := try solve [Tactics.program_simpl|auto].

(* This uses 'refine' instead of Program Definition to work around a Coq 8.4
   bug. *)
Definition mkspec (f: nat -> SPred -> Prop)
  (Hnat: forall k P, f (S k) P -> f k P)
  (HSPred: forall k P P', extSP P P' -> f k P -> f k P') : spec.
  refine (mkILPreFrm (fun k => mkILPreFrm (f k) _) _).
Proof.
  have Hnat' : forall k' k P, k' >= k -> f k' P -> f k P.
  - move => k' k P. elim; by auto.
  move=> k' k Hk P /= Hf.
  eapply Hnat'; eassumption. 
Grab Existential Variables.
Proof.
  move=> P P' HP /= Hf. eapply HSPred; eassumption.
Defined.
Implicit Arguments mkspec [].

Definition spec_fun (S: spec) := fun k P => S k P.
Coercion spec_fun: spec >-> Funclass.

Add Parametric Morphism (S: spec) : S with signature
  ge ++> extSP ++> Basics.impl
  as spec_impl_m.
Proof.
  rewrite /spec_fun. move => k k' Hk P P' HP.
  rewrite -[Basics.impl _ _]/(@lentails _ ILogicOps_Prop _ _).
  by rewrite ->HP, ->Hk.
Qed.

Add Parametric Morphism (S: spec) : S with signature
  eq ==> lequiv ==> iff
  as spec_iff_m.
Proof.
  move=> k P P' HP. split => HS.
  - by rewrite ->HP in HS.
  - by rewrite <-HP in HS.
Qed.

(* The default definition of spec equivalence is sometimes inconvenient.
   Here is an alternative one. *)
Lemma spec_equiv (S S': spec):
  (forall k P, S k P <-> S' k P) -> S -|- S'.
Proof. move=> H; split => k P /=; apply H. Qed.

Lemma spec_downwards_closed (S: spec) P k k':
  k <= k' -> S k' P -> S k P.
Proof.
  move=> Hk. have Hk' : k' >= k by auto. by rewrite ->Hk'.
Qed.

(*
   Properties of spec_at
*)

Program Definition spec_at (S: spec) (R: SPred) :=
  mkspec (fun k P => S k (R ** P)) _ _.
Next Obligation.
  move=> S R k P P'. eauto using spec_downwards_closed.
Qed.
Next Obligation.
  move=> S R k P P' HP. by rewrite ->HP.
Qed.

Infix "@" := spec_at (at level 44, left associativity).

Lemma spec_frame (S : spec) (R : SPred) :
  S |-- S @ R.
Proof.
  move => k P H. rewrite /spec_at /=.
  assert (extSP P (P ** R)) as HPR by (exists R; reflexivity).
  rewrite ->sepSPC in HPR. by rewrite <-HPR.
Qed.

(* For variations of this instance with lentails instead of extSP, look at
   [spec_at_covar_m] and [spec_at_contra_m]. *)
Instance spec_at_entails_m:
  Proper (lentails ++> extSP ++> lentails) spec_at.
Proof.
  move=> S S' HS R R' HR k P. rewrite /spec_at /= /spec_fun /=.
  by rewrite <- HR, -> HS.
Qed.

Instance spec_at_equiv_m:
  Proper (lequiv ++> lequiv ++> lequiv) spec_at.
Proof.
  move => S S' HS R R' HR.
  split; cancel2; by (rewrite HS || rewrite HR).
Qed.

Lemma spec_at_emp S: S @ empSP -|- S.
Proof.
  split; last exact: spec_frame.
  move=> k P. rewrite /spec_at /spec_fun /=. by rewrite empSPL.
Qed.

Lemma spec_at_at S R R': S @ R @ R' -|- S @ (R ** R').
Proof.
  apply spec_equiv => k P. rewrite /spec_at /spec_fun /=.
  split; by [rewrite -sepSPA | rewrite sepSPA].
Qed.

Lemma spec_at_forall {T} F R: (Forall x:T, F x) @ R -|- Forall x:T, (F x @ R).
Proof. split; rewrite /= /spec_fun /=; auto. Qed.
  
Lemma spec_at_exists {T} F R: (Exists x:T, F x) @ R -|- Exists x:T, (F x @ R).
Proof. split; rewrite /= /spec_fun /= => k P [x Hx]; eauto. Qed.

Lemma spec_at_true R: ltrue @ R -|- ltrue.
Proof. split; rewrite /= /spec_fun /=; auto. Qed.

Lemma spec_at_false R: lfalse @ R -|- lfalse.
Proof. split; rewrite /= /spec_fun /=; auto. Qed.

Lemma spec_at_and S S' R: (S //\\ S') @ R -|- (S @ R) //\\ (S' @ R).
Proof. split; rewrite /spec_at /= /spec_fun /= => k P H; auto. Qed.

Lemma spec_at_or S S' R: (S \\// S') @ R -|- (S @ R) \\// (S' @ R).
Proof. split; rewrite /spec_at /= /spec_fun /= => k P H; auto. Qed.

Lemma spec_at_propimpl p S R: (p ->> S) @ R -|- p ->> (S @ R).
Proof. split; rewrite /= /spec_fun /=; auto. Qed.

Lemma spec_at_propand p S R: (p /\\ S) @ R -|- p /\\ (S @ R).
Proof. split; rewrite /= /spec_fun /=; auto. Qed.

Lemma spec_at_impl S S' R: (S -->> S') @ R -|- (S @ R) -->> (S' @ R).
Proof.
  split.
  - apply: limplAdj. rewrite <-spec_at_and.
    cancel2. exact: landAdj.
  - rewrite /spec_at /= /spec_fun /= => k P H.
    (* This proof follows the corresponding one (Lemma 25) in Krishnaswami's
       PhD thesis. *)
    intros k' Hk' P' [Pext HPext] HS.
    move/(_ k' Hk' (P ** Pext)): H => H.
    rewrite ->sepSPA in HPext.
    (* The rewriting by using explicit subrelation instances here is a bit
       awkward. *)
    rewrite <-(subrelation_equivSP_extSP HPext).
    apply H; first by exists Pext.
    rewrite ->(subrelation_equivSP_inverse_extSP HPext). done.
Qed.

Hint Rewrite
  spec_at_at
  spec_at_true
  spec_at_false
  spec_at_and
  spec_at_or
  spec_at_impl
  @spec_at_forall
  @spec_at_exists
  spec_at_propimpl
  spec_at_propand
  : push_at.

(* This lemma is what [spec_at_at] really should be in order to be consistent
   with the others in the hint database, but this variant is not suitable for
   autorewrite. *)
Lemma spec_at_swap S R1 R2:
  S @ R1 @ R2 -|- S @ R2 @ R1.
Proof. autorewrite with push_at. by rewrite sepSPC. Qed.

(*
   "Rule of consequence" for spec_at
*)

Class AtCovar S := at_covar: forall P Q, P |-- Q -> S @ P |-- S @ Q.
Class AtContra S := at_contra: forall P Q, P |-- Q -> S @ Q |-- S @ P.

Instance: Proper (lequiv ==> iff) AtCovar.
Proof. move=> S S' HS. rewrite /AtCovar. by setoid_rewrite HS. Qed.

Instance: Proper (lequiv ==> iff) AtContra.
Proof. move=> S S' HS. rewrite /AtContra. by setoid_rewrite HS. Qed.

Instance AtCovar_forall A S {HS: forall a:A, AtCovar (S a)} :
  AtCovar (Forall a, S a).
Proof.
  move=> P Q HPQ. autorewrite with push_at. cancel1 => a.
  by rewrite ->(HS _ _ _ HPQ).
Qed.

Instance AtContra_forall A S {HS: forall a:A, AtContra (S a)} :
  AtContra (Forall a, S a).
Proof.
  move=> P Q HPQ. autorewrite with push_at. cancel1 => a.
  by rewrite ->(HS _ _ _ HPQ).
Qed.

Instance AtCovar_and S1 S2 {H1: AtCovar S1} {H2: AtCovar S2} :
  AtCovar (S1 //\\ S2).
Proof. rewrite land_is_forall. by apply AtCovar_forall => [[]]. Qed.

Instance AtContra_and S1 S2 {H1: AtContra S1} {H2: AtContra S2} :
  AtContra (S1 //\\ S2).
Proof. rewrite land_is_forall. by apply AtContra_forall => [[]]. Qed.

Instance AtCovar_true : AtCovar ltrue.
Proof. rewrite ltrue_is_forall. by apply AtCovar_forall => [[]]. Qed.

Instance AtContra_true : AtContra ltrue.
Proof. rewrite ltrue_is_forall. by apply AtContra_forall => [[]]. Qed.

Instance AtCovar_exists A S {HS: forall a:A, AtCovar (S a)} :
  AtCovar (Exists a, S a).
Proof.
  move=> P Q HPQ. autorewrite with push_at. cancel1 => a.
  by rewrite ->(HS _ _ _ HPQ).
Qed.

Instance AtContra_exists A S {HS: forall a:A, AtContra (S a)} :
  AtContra (Exists a, S a).
Proof.
  move=> P Q HPQ. autorewrite with push_at. cancel1 => a.
  by rewrite ->(HS _ _ _ HPQ).
Qed.

Instance AtCovar_or S1 S2 {H1: AtCovar S1} {H2: AtCovar S2} :
  AtCovar (S1 \\// S2).
Proof. rewrite lor_is_exists. by apply AtCovar_exists => [[]]. Qed.

Instance AtContra_or S1 S2 {H1: AtContra S1} {H2: AtContra S2} :
  AtContra (S1 \\// S2).
Proof. rewrite lor_is_exists. by apply AtContra_exists => [[]]. Qed.

Instance AtCovar_false : AtCovar lfalse.
Proof. rewrite lfalse_is_exists. by apply AtCovar_exists => [[]]. Qed.

Instance AtContra_false : AtContra lfalse.
Proof. rewrite lfalse_is_exists. by apply AtContra_exists => [[]]. Qed.

Instance AtCovar_impl S1 S2 {H1: AtContra S1} {H2: AtCovar S2} :
  AtCovar (S1 -->> S2).
Proof.
  move=> P Q HPQ. autorewrite with push_at.
  by rewrite ->(H1 _ _ HPQ), <-(H2 _ _ HPQ).
Qed.

Instance AtContra_impl S1 S2 {H1: AtCovar S1} {H2: AtContra S2} :
  AtContra (S1 -->> S2).
Proof.
  move=> P Q HPQ. autorewrite with push_at.
  by rewrite ->(H1 _ _ HPQ), <-(H2 _ _ HPQ).
Qed.

Instance AtCovar_at S R {HS: AtCovar S} : AtCovar (S @ R).
Proof.
  move=> P Q HPQ. rewrite [_ @ P]spec_at_swap [_ @ Q]spec_at_swap.
  by rewrite <-(HS _ _ HPQ).
Qed.

Instance AtContra_at S R {HS: AtContra S} : AtContra (S @ R).
Proof.
  move=> P Q HPQ. rewrite [_ @ Q]spec_at_swap [_ @ P]spec_at_swap.
  by rewrite <-(HS _ _ HPQ).
Qed.

Instance spec_at_covar_m S {HS: AtCovar S} :
  Proper (lentails ++> lentails) (spec_at S).
Proof. move=> P Q HPQ. by apply HS. Qed.

Instance spec_at_contra_m S {HS: AtContra S} :
  Proper (lentails --> lentails) (spec_at S).
Proof. move=> P Q HPQ. by apply HS. Qed.

(*
   Rules for pulling existentials from the second argument of spec_at. These
   rules together form a spec-level analogue of the "existential rule" for
   Hoare triples.

   Whether an existential quantifier can be pulled out of the R in [S @ R]
   depends on S. Rewrite by <-at_ex to pull it out from a positive position in
   the goal. Rewrite by ->at_ex' to pull it out from a negative position in the
   goal.
 *)

Class AtEx S := at_ex: forall A f, Forall x:A, S @ f x |-- S @ lexists f.

(* The reverse direction of at_ex. This not only follows from AtContra but is
   actually equivalent to it. The proof is in revision 22259 (spec.v#22). *)
Lemma at_ex' S {HS: AtContra S} :
  forall A f, S @ lexists f |-- Forall x:A, S @ f x.
Proof.
  move=> A f. apply: lforallR => x. apply HS. ssplit. reflexivity.
Qed.

Instance: Proper (lequiv ==> iff) AtEx.
Proof. move=> S S' HS. rewrite /AtEx. by setoid_rewrite HS. Qed.

Lemma spec_at_and_or S R1 R2 {HS: AtEx S}:
  S @ R1 //\\ S @ R2 |-- S @ (R1 \\// R2).
Proof.
  rewrite ->land_is_forall, lor_is_exists.
  transitivity (Forall b, S @ (if b then R1 else R2)).
  - apply: lforallR => [[|]].
    - by apply lforallL with true.
    - by apply lforallL with false.
  apply: at_ex.
Qed.

Lemma spec_at_or_and S R1 R2 {HNeg: AtContra S}:
  S @ (R1 \\// R2) |-- S @ R1 //\\ S @ R2.
Proof.
  rewrite ->land_is_forall, lor_is_exists.
  transitivity (Forall b, S @ (if b then R1 else R2)); last first.
  - apply: lforallR => [[|]].
    - by apply lforallL with true.
    - by apply lforallL with false.
  apply: at_ex'.
Qed.

Instance AtEx_forall A S {HS: forall a:A, AtEx (S a)} :
  AtEx (Forall a, S a).
Proof.
  move=> T f.
  rewrite -> spec_at_forall. apply: lforallR => a.
  rewrite <- at_ex; cancel1 => x.
  rewrite spec_at_forall; by apply lforallL with a.
Qed.

Instance AtEx_and S1 S2 {H1: AtEx S1} {H2: AtEx S2} : AtEx (S1 //\\ S2).
Proof. rewrite land_is_forall. by apply AtEx_forall => [[]]. Qed.

Instance AtEx_true : AtEx ltrue.
Proof. rewrite ltrue_is_forall. by apply AtEx_forall => [[]]. Qed.

Instance AtEx_impl S1 S2 {H1: AtContra S1} {H2: AtEx S2} : AtEx (S1 -->> S2).
Proof.
  move=> A f. setoid_rewrite spec_at_impl.
  rewrite ->at_ex', <-at_ex => //. (*TODO: why does at_ex' leave a subgoal? *)
  apply: limplAdj. apply: lforallR => x. apply: landAdj.
  apply lforallL with x. apply: limplAdj. rewrite landC. apply: landAdj. 
  apply lforallL with x. apply: limplAdj. rewrite landC. apply: landAdj.
  reflexivity.
Qed.

Instance AtEx_at S R {HS: AtEx S} : AtEx (S @ R).
Proof.
  move=> A f. rewrite spec_at_at.
  assert (R ** lexists f -|- Exists x, R ** f x) as Hpull.
  - split; sbazooka.
  rewrite Hpull. rewrite <-at_ex. cancel1 => x. by rewrite spec_at_at.
Qed.

(* The payoff for all this: a tactic for pulling quantifiers *)
Module Export PullQuant.
  Implicit Type S: spec.

  Definition PullQuant {A} S (f: A -> spec) := lforall f |-- S.

  Lemma pq_rhs S {A} S' (f: A -> spec) {HPQ: PullQuant S' f}:
    (forall a:A, S |-- f a) ->
    S |-- S'.
  Proof. move=> H. red in HPQ. rewrite <-HPQ. by apply: lforallR. Qed.

  Lemma PullQuant_forall A (f: A -> spec): PullQuant (lforall f) f.
  Proof. red. reflexivity. Qed.

  (* Hint Resolve worked here in Coq 8.3 but not since 8.4. *)
  Hint Extern 0 (PullQuant (lforall _) _) =>
    apply PullQuant_forall : pullquant.

  Lemma PullQuant_propimpl p S:
    PullQuant (p ->> S) (fun H: p => S).
  Proof. red. reflexivity. Qed.

  (* Hint Resolve worked here in Coq 8.3 but not since 8.4. *)
  Hint Extern 0 (PullQuant (?p ->> ?S) _) =>
    apply (@PullQuant_propimpl p S) : pullquant.

  Lemma pq_at_rec S R A f:
    PullQuant S f ->
    PullQuant (S @ R) (fun a:A => f a @ R).
  Proof.
    rewrite /PullQuant => Hf. rewrite <-Hf. by rewrite spec_at_forall.
  Qed.

  (* If we didn't find anything to pull from the frame itself, recurse under it. *)
  (* Unfortunately, Hint Resolve doesn't work here. For some obscure reason,
     there has to be an underscore for the last argument. *)
  Hint Extern 1 (PullQuant (?S @ ?R) _) =>
    eapply (@pq_at_rec S R _ _) : pullquant.

  Lemma pq_impl S S' A f:
    PullQuant S f ->
    PullQuant (S' -->> S) (fun a:A => S' -->> f a).
  Proof.
    rewrite /PullQuant => Hf. rewrite <-Hf. apply: limplAdj.
    apply: lforallR => a. apply: landAdj. eapply lforallL. reflexivity.
  Qed.

  Hint Extern 1 (PullQuant (?S' -->> ?S) _) =>
    eapply (@pq_impl S S' _ _) : pullquant.

  Import Existentials.

  Lemma pq_at S t:
    match find t with
    | Some (mkf _ f) =>
        AtEx S -> PullQuant (S @ eval t) (fun a => S @ f a)
    | None => True
    end.
  Proof.
    move: (@find_correct t). case: (find t) => [[A f]|]; last done.
    move=> Heval HS. red. rewrite ->Heval. by rewrite <-at_ex.
  Qed.

  Hint Extern 0 (PullQuant (?S @ ?R) _) =>
    let t := quote_term R in
    apply (@pq_at S t); [apply _] : pullquant.
  
  (* It's a slight breach of abstraction to [cbv [eval]] here, but it's easier
     than dealing with it in the hints that use reflection. *)
  (* For some reason, auto sometimes hangs when there are entailments among the
     hypotheses. As a workaround, we clear those first. Another workaround is
     to use [typeclasses eauto], but that sometimes fails. *)
  Ltac specintro :=
    eapply pq_rhs; [
      repeat match goal with H: _ |-- _ |- _ => clear H end;
      solve [auto with pullquant]
    |];
    instantiate;
    cbv [eval].
  
  Ltac specintros :=
    specintro; let x := fresh "x" in move=> x; try specintros; move: x.

End PullQuant.

(*
   The spec_reads connective, [S <@ R].

   It is like spec_at but requires S to not only preserve the validity of R but
   keep the memory in R's footprint unchanged.
*)

Definition spec_reads S R := Forall s : PState, (eq_pred s |-- R) ->> S @ eq_pred s.

Infix "<@" := spec_reads (at level 44, left associativity).

Instance spec_reads_entails:
  Proper (lentails ++> lentails --> lentails) spec_reads.
Proof.
  move=> S S' HS R R' HR. red in HR. rewrite /spec_reads. cancel1 => s.
  by rewrite ->HS, ->HR.
Qed.

Instance spec_reads_equiv:
  Proper (lequiv ==> lequiv ==> lequiv) spec_reads.
Proof.
  move=> S S' HS R R' HR. rewrite /spec_reads. setoid_rewrite HS.
  by setoid_rewrite HR.
Qed.

Lemma spec_reads_alt S R:
  S <@ R -|- Forall s, (eq_pred s |-- R ** ltrue) ->> S @ eq_pred s.
Proof.
  rewrite /spec_reads. split.
  - specintros => s Hs. rewrite <-lentails_eq in Hs.
    case: Hs => sR [sframe [Hs [HsR _]]].
    apply lforallL with sR. apply lpropimplL.
    - by apply-> lentails_eq.
    etransitivity; [apply (spec_frame (eq_pred sframe))|]. autorewrite with push_at.
    rewrite stateSplitsAs_eq; [|eapply Hs]. done.
  - cancel1 => s. apply: lpropimplR => Hs. apply lpropimplL => //.
    rewrite ->Hs. by ssimpl.
Qed.

(* This definition can be more convenient in metatheory. *)
Lemma spec_reads_alt_meta S R : S <@ R -|- Forall s, R s ->> S @ eq_pred s.
Proof. rewrite /spec_reads. by setoid_rewrite <-lentails_eq. Qed.

Lemma spec_reads_ex S T f: Forall x:T, S <@ f x -|- S <@ lexists f.
Proof.
  setoid_rewrite spec_reads_alt_meta. split.
  - specintros => s [x Hx]. apply lforallL with x. apply lforallL with s.
    by apply lpropimplL.
  - specintros => x s Hf.
    apply lforallL with s. apply: lpropimplL => //. econstructor. eassumption.
Qed.

Lemma spec_reads_frame S R:
  S |-- S <@ R.
Proof. rewrite /spec_reads. specintros => s Hs. apply spec_frame. Qed.

Lemma spec_reads_entails_at S {HEx: AtEx S} R:
  S <@ R |-- S @ R.
Proof.
  rewrite spec_reads_alt_meta. rewrite ->(ILFun_exists_eq R).
  specintros => s Hs. apply lforallL with s. by apply: lpropimplL.
Qed.
Local Transparent ILFun_Ops SABIOps.
Lemma emp_unit : empSP -|- eq_pred sa_unit.
  split; simpl; move => x H.
  + destruct H as [H _]; assumption.
  + exists H; tauto.
Qed.

Lemma spec_at_entails_reads S {HContra: AtContra S} R:
  S @ R |-- S <@ R.
Proof. rewrite /spec_reads. specintros => s Hs. by rewrite <-Hs. Qed.

Lemma spec_reads_eq_at S s:
  S <@ eq_pred s -|- S @ eq_pred s.
Proof.
  rewrite /spec_reads. split.
  - apply lforallL with s. exact: lpropimplL.
  - specintros => s' Hs'. rewrite <-lentails_eq in Hs'.
    simpl in Hs'; rewrite -> Hs'; reflexivity.
Qed.

Lemma spec_reads_merge S R1 R2:
  S <@ R1 <@ R2 |-- S <@ (R1 ** R2).
Proof.
  setoid_rewrite spec_reads_alt_meta.
  specintros => s [s1 [s2 [Hs [Hs1 Hs2]]]].
  apply lforallL with s2. apply lpropimplL; first done.
  rewrite spec_reads_alt_meta.
  assert ((Forall s', R1 s' ->> S @ eq_pred s') |-- S @ eq_pred s1) as Htmp.
  - apply lforallL with s1. by apply lpropimplL.
  rewrite ->Htmp => {Htmp}. autorewrite with push_at.
  rewrite stateSplitsAs_eq; [|eapply Hs]. done.
Qed.

Lemma spec_reads_split S {HS: AtEx S} R1 R2:
  S <@ (R1 ** R2) |-- S <@ R1 <@ R2.
Proof.
  rewrite /spec_reads.
  specintros => s2 Hs2 s1 Hs1. autorewrite with push_at.
  rewrite (ILFun_exists_eq (eq_pred s1 ** eq_pred s2)).
  specintros => s Hs. rewrite ->lentails_eq in Hs. apply lforallL with s.
  apply lpropimplL => //. by rewrite <-Hs1, <-Hs2.
Qed.

Lemma spec_reads_swap' S R1 R2:
  S <@ R1 <@ R2 |-- S <@ R2 <@ R1.
Proof.
  rewrite /spec_reads.
  specintros => s1 Hs1 s2 Hs2. rewrite spec_at_swap.
  apply lforallL with s2. apply lpropimplL => //. rewrite spec_at_forall.
  apply lforallL with s1. rewrite spec_at_propimpl. exact: lpropimplL.
Qed.

Lemma spec_reads_swap S R1 R2:
  S <@ R1 <@ R2 -|- S <@ R2 <@ R1.
Proof. split; apply spec_reads_swap'. Qed.

Lemma spec_reads_forall A S R:
  (Forall a:A, S a) <@ R -|- Forall a:A, (S a <@ R).
Proof.
  rewrite /spec_reads. split.
  - specintros => a s' Hs'. apply lforallL with s'. apply: lpropimplL => //.
    autorewrite with push_at. by apply lforallL with a.
  - specintros => s' Hs' a.
    apply lforallL with a. apply lforallL with s'. exact: lpropimplL.
Qed.

Lemma spec_reads_true R: ltrue <@ R -|- ltrue.
Proof.
  rewrite ltrue_is_forall. rewrite spec_reads_forall.
  split; specintro => [[]].
Qed.

Lemma spec_reads_and S1 S2 R:
  (S1 //\\ S2) <@ R -|- (S1 <@ R) //\\ (S2 <@ R).
Proof.
  rewrite !land_is_forall. rewrite spec_reads_forall.
  split; by cancel1 => [[]].
Qed.

Lemma spec_reads_exists A S R:
  Exists a:A, (S a <@ R) |-- (Exists a:A, S a) <@ R.
Proof.
  rewrite /spec_reads. apply: lexistsL => a. specintros => s' Hs'.
  autorewrite with push_at. apply lexistsR with a. apply lforallL with s'.
  exact: lpropimplL.
Qed.

Lemma spec_reads_or S1 S2 R:
  (S1 <@ R) \\// (S2 <@ R) |-- (S1 \\// S2) <@ R.
Proof.
  rewrite !lor_is_exists. rewrite <-spec_reads_exists. by cancel1 => [[]].
Qed.

Lemma spec_reads_impl S1 S2 R:
  (S1 -->> S2) <@ R |-- S1 <@ R -->> S2 <@ R.
Proof.
  rewrite /spec_reads. apply: limplAdj. specintros => s Hs.
  apply: landAdj. apply lforallL with s. apply lpropimplL => //.
  apply: limplAdj. rewrite landC. apply: landAdj.
  apply lforallL with s. apply lpropimplL => //. apply: limplAdj.
  autorewrite with push_at. rewrite landC. apply: landAdj. reflexivity.
Qed.

Lemma spec_at_reads S R1 R:
  S <@ R1 @ R -|- S @ R <@ R1.
Proof.
  rewrite /spec_reads. split.
  - specintros => s Hs. autorewrite with push_at.
    apply lforallL with s. autorewrite with push_at.
    apply lpropimplL => //. by rewrite sepSPC.
  - autorewrite with push_at. specintro => s.
    autorewrite with push_at. specintro => Hs.
    apply lforallL with s. apply: lpropimplL => //.
    autorewrite with push_at. by rewrite sepSPC.
Qed.

Hint Rewrite spec_at_reads : push_at.

Instance AtEx_reads S R {HS: AtEx S}: AtEx (S <@ R) := _.
Instance AtCovar_reads S R {HS: AtCovar S}: AtCovar (S <@ R) := _.
Instance AtContra_reads S R {HS: AtContra S}: AtContra (S <@ R) := _.

Module Export PullQuant_reads.
  Import Existentials.
  
  Lemma pq_reads S t:
    match find t with
    | Some (mkf _ f) =>
        PullQuant (S <@ eval t) (fun a => S <@ f a)
    | None => True
    end.
  Proof.
    move: (@find_correct t). case: (find t) => [[A f]|]; last done.
    move=> Heval. red. rewrite ->Heval. by apply spec_reads_ex.
  Qed.

  Hint Extern 0 (PullQuant (?S <@ ?R) _) =>
    let t := quote_term R in
    apply (@pq_reads S t) : pullquant.

  Lemma pq_reads_rec S R A f:
    PullQuant S f ->
    PullQuant (S <@ R) (fun a:A => f a <@ R).
  Proof.
    rewrite /PullQuant => Hf. rewrite <-Hf. by rewrite spec_reads_forall.
  Qed.

  (* If we didn't find anything to pull from the frame itself, recurse under it. *)
  (* Unfortunately, Hint Resolve doesn't work here. For some obscure reason,
     there has to be an underscore for the last argument. *)
  Hint Extern 1 (PullQuant (?S <@ ?R) _) =>
    eapply (@pq_reads_rec S R _ _) : pullquant.

End PullQuant_reads.

Lemma spec_at_later S R:
  (|> S) @ R  -|- |> (S @ R).
Proof.
  split => k P; reflexivity.
Qed.

Hint Rewrite spec_at_later : push_at.

Local Transparent ILLaterPreOps.

Lemma spec_reads_later S R: (|> S) <@ R  -|- |> (S <@ R).
 split => k P /=; rewrite /spec_fun /=; eauto.
Qed.

Hint Rewrite <-
  spec_at_later
  spec_reads_later
  : push_later.

Hint Rewrite @spec_later_exists_inhabited
  using repeat constructor : push_later.

Lemma spec_lob_context C S: (C //\\ |> S |-- S) -> C |-- S.
Proof.
  etransitivity.
  - apply landR; first apply ltrueR. reflexivity.
  apply: landAdj. apply: spec_lob. rewrite spec_later_impl.
  apply: limplAdj. apply: limplL; last by rewrite landC.
  apply spec_later_weaken.
Qed.

Instance AtEx_later S {HS: AtEx S} : AtEx (|> S).
Proof.
  move=> A f. rewrite spec_at_later.
  red in HS. rewrite <-HS. rewrite spec_later_forall. cancel1 => x.
  by rewrite spec_at_later.
Qed.
  
Instance AtCovar_later S {HS: AtCovar S} : AtCovar (|> S).
Proof.
  move=> P Q HPQ. autorewrite with push_at. by rewrite ->(HS _ _ HPQ).
Qed.

Instance AtContra_later S {HS: AtContra S} : AtContra (|> S).
Proof.
  move=> P Q HPQ. autorewrite with push_at. by rewrite ->(HS _ _ HPQ).
Qed.

