Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe pointsto cursor instr reader decinstr.
Require Import Setoid RelationClasses Morphisms.

Section Basic.
  Context {T} `{MI: MemIs T}.

  (** Basic block of position-independent code *)
  Definition basic P (c:T) Q : spec :=
    Forall i:DWORD, Forall j:DWORD,
    (safe @ (EIP ~= j ** Q) -->> safe @ (EIP ~= i ** P)) <@ (i -- j :-> c).

  Lemma spec_at_basic P c Q R :
    basic P c Q @ R -|- basic (P ** R) c (Q ** R).
  Proof.
    rewrite /basic.
    autorewrite with push_at. cancel1 => i.
    autorewrite with push_at. cancel1 => j.
    autorewrite with push_at. rewrite !sepSPA. reflexivity.
  Qed.

  Lemma basic_frame R S P c Q :
    S |-- basic P c Q ->
    S |-- basic (P ** R) c (Q ** R).
  Proof. by rewrite <-spec_at_basic, <-spec_frame. Qed.

  Lemma basic_roc P' Q' S P c Q:
    P |-- P' ->
    Q' |-- Q ->
    S |-- basic P' c Q' ->
    S |-- basic P c Q.
  Proof.
    move=> HP HQ H. rewrite /basic in H.
    setoid_rewrite <-HP in H. setoid_rewrite ->HQ in H. apply H.
  Qed.

  Global Instance basic_entails_m:
    Proper (lentails --> eq ==> lentails ++> lentails) basic.
  Proof.
    move => P P' HP c _ <- Q Q' HQ. apply: basic_roc; try eassumption.
    done.
  Qed.

  Global Instance basic_equiv_m:
    Proper (lequiv ==> eq ==> lequiv ==> lequiv) basic.
  Proof.
    move => P P' HP c _ <- Q Q' HQ. rewrite {1}/basic.
    setoid_rewrite HQ. setoid_rewrite HP. reflexivity.
  Qed.

  Lemma basic_roc_pre P' S P c Q:
    P |-- P' ->
    S |-- basic P' c Q ->
    S |-- basic P c Q.
  Proof. move=> HP H. by rewrite ->HP. Qed.

  Lemma basic_roc_post Q' S P c Q:
    Q' |-- Q ->
    S |-- basic P c Q' ->
    S |-- basic P c Q.
  Proof. move=> HQ H. by rewrite <-HQ. Qed.

  Lemma basic_exists A S P c Q:
    (forall a:A, S |-- basic (P a) c Q) ->
    S |-- basic (lexists P) c Q.
  Proof. rewrite /basic => H. specintros => i j a. eforalls H. simple apply H. Qed.

  Global Instance AtEx_basic P c Q : AtEx (basic P c Q).
  Proof. apply _. Qed.

  Lemma basic_basic_context R S' P' Q' S P c Q:
    S' |-- basic P' c Q' ->
    S |-- S' ->
    P |-- P' ** R ->
    Q' ** R |-- Q ->
    S |-- basic P c Q.
  Proof. move=> Hc HS HP HQ. rewrite ->HS, ->HP, <-HQ. exact: basic_frame. Qed.

  Lemma basic_basic R P' Q' S P c Q:
    |-- basic P' c Q' ->
    P |-- P' ** R ->
    Q' ** R |-- Q ->
    S |-- basic P c Q.
  Proof.
    move=> Hc HP HQ. apply: basic_basic_context; try eassumption. done.
  Qed.
End Basic.

Hint Rewrite @spec_at_basic : push_at.

Hint Unfold basic : specapply.

Module Export Existentials_basic.
  Import Existentials.
  
  Lemma pq_basic {M} {HM: MemIs M} t c Q:
    match find t with
    | Some (mkf _ f) =>
        PullQuant (basic (eval t) c Q) (fun a => basic (f a) c Q)
    | None => True
    end.
  Proof.
    move: (@find_correct_pull t). case: (find t) => [[A f]|]; last done.
    red. move=> Heval. rewrite ->Heval.
    apply basic_exists => a. by apply lforallL with a.
  Qed.
  
  Hint Extern 0 (PullQuant (@basic ?M ?HM ?P ?c ?Q) _) =>
    let t := quote_term P in
    apply (@pq_basic M HM t c Q) : pullquant.

End Existentials_basic.


Require Import program. 

Global Instance basic_progEq_m:
Proper (lequiv ==> progEq ==> lequiv ==> lequiv) basic.
  Proof.
    move => P P' HP c c' Hc Q Q' HQ. rewrite {1}/basic.
    setoid_rewrite HQ. setoid_rewrite HP. setoid_rewrite Hc. reflexivity. 
  Qed.


Lemma basic_skip P: |-- basic P prog_skip P.
Proof.
  rewrite /basic. specintros => i j.
  rewrite /memIs /=. specintro => <-.
  rewrite emp_unit spec_reads_eq_at; rewrite <- emp_unit. 
  rewrite spec_at_emp. by apply limplValid.
Qed.

Lemma basic_seq (c1 c2: program) S P Q R:
  S |-- basic P c1 Q ->
  S |-- basic Q c2 R ->
  S |-- basic P (c1;; c2) R.
Proof.
  rewrite /basic. move=> Hc1 Hc2. specintros => i j.
  rewrite /memIs /=. specintro => i'.
  specapply Hc1.
  - by ssimpl.
  specapply Hc2.
  - by ssimpl.
  rewrite <-spec_reads_frame. apply: limplAdj. apply: landL2.
  by rewrite spec_at_emp.
Qed.


(* Attempts to apply "basic" lemma on a single command (basic_basic) or
   on the first of a sequence (basic_seq). Note that it attempts to use sbazooka
   to discharge subgoals, so be careful if existentials are exposed in the goal -- 
   they will be instantiated! *)
  Hint Unfold not : basicapply.
  Hint Rewrite eq_refl : basicapply.
  Ltac instRule R H :=
    move: (R) => H;
    repeat (autounfold with basicapply in H);
    eforalls H; 
    autorewrite with push_at in H.


  Ltac  basicapp R :=
  match goal with
    | |- |-- basic ?P (prog_seq ?p1 ?p2) ?Q =>  
             (eapply basic_seq; first (eapply basic_basic; first exact R; ptsimpl; sbazooka))

    | _ => eapply basic_basic; first exact R; ptsimpl; sbazooka
    end.

  Ltac basicapply R :=
    let Hlem := fresh in
    instRule R Hlem;
    repeat (autorewrite with basicapply in Hlem);
    first basicapp Hlem;
    clear Hlem.
  
