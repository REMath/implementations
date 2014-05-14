Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program spectac.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Lemma basic_local S P c Q:
  (forall l, S |-- basic P (c l) Q) ->
  forall g, S |-- basic P (prog_declabel g c) Q.
Proof.
  move=> H g. rewrite /basic. rewrite /memIs /=. specintros => i j l.
  specialize (H l). lforwardR H.
  - apply lforallL with i. apply lforallL with j. reflexivity.
  apply H.
Qed.

Section If.
(*=ifthenelse *)
Definition ifthenelse 
  (cond: Condition) (direction: bool) 
  (pthen pelse: program) : program :=
  LOCAL THEN; LOCAL END;
    JCC cond direction THEN;;
      pelse;; JMP END;;
    THEN:;; 
      pthen;;
    END:;.
(*=End *)

  Lemma if_rule cond (direction:bool) pthen pelse P Q S:
    S |-- basic (P direction ** ConditionIs cond direction) pthen Q ->
    S |-- basic (P (~~direction) ** ConditionIs cond (~~direction)) pelse Q ->
    S |-- basic (Exists b, P b ** ConditionIs cond b)
                (ifthenelse cond direction pthen pelse)
                Q.
  Proof.
    move=> Hthen Helse. apply basic_local => THEN. apply basic_local => END.
    rewrite /basic. specintros => i j b.
    unfold_program.
    specintros => i1 i2 _ _ <- -> _ <- ->.

    (* JCC cond direction THEN *)
    specapply JCC_rule.
    - by ssimpl.

    specsplit.
    - (* THEN branch *)
      rewrite <-spec_later_weaken. specintro. move/eqP => ->.
      specapply Hthen.
      - by ssimpl.
       rewrite <-spec_reads_frame. apply: limplAdj. autorewrite with push_at.
       apply: landL2. cancel1. by ssimpl.

    (* ELSE branch *)
    specintro. move/eqP => ->.
    specapply Helse.
    - by ssimpl.

    (* JMP END *)
    specapply JMP_I_rule.
    - by ssimpl.
    rewrite <-spec_later_weaken.
    rewrite <-spec_reads_frame. apply: limplAdj. autorewrite with push_at.
    apply: landL2. by (cancel1; reflexivity).
  Qed.
End If.

Section While.
  (* A macro for a structured "while" loop with parameters:
     - ptest: code that performs the loop test
     - cond: the Condition to test the flags for when deciding whether to loop
     - direction: whether the test is inverted (usually false)
     - pbody: the loop body
   *)
(*=while *)
Definition while (ptest: program) 
  (cond: Condition) (direction: bool)
  (pbody: program) : program :=
  LOCAL BODY; LOCAL test;
    JMP test;;
  BODY:;;
    pbody;;
  test:;;
    ptest;;
    JCC cond direction BODY.
(*=End *)

  Lemma while_rule ptest cond (direction:bool) pbody (I:bool->_) P S:
    S |-- basic P ptest (Exists b, I b ** ConditionIs cond b) ->
    S |-- basic (I direction ** ConditionIs cond direction) pbody P ->
    S |-- basic P (while ptest cond direction pbody)
                (I (~~direction) ** ConditionIs cond (~~direction)).
  Proof.
    move=> Htest Hbody. apply basic_local => BODY. apply basic_local => test.
    rewrite /basic. specintros => i j. unfold_program.
    specintros => _ _ <- ->  _ _ <- -> i1. rewrite !empSPL.

    (* We need to set up Lob induction but not for this instruction. This is a
       bit awkward. *)
    assert (|> safe @ (EIP ~= test ** P) -->>
        safe @ (EIP~=i ** P) //\\ safe @ (EIP ~= test ** P) |--
            safe @ (EIP~=i ** P)) as Hlob.
    - etransitivity; [|by apply landL1].
      instantiate (1 := safe @ (EIP ~= test ** P)).
      apply spec_lob_context. autorewrite with push_later.
      autorewrite with push_at. apply: limplL; first exact: landL2.
      exact: landL1. apply _.
    rewrite <-Hlob => {Hlob}.

    specsplit.
    (* JMP TEST *)
    - specapply JMP_I_rule.
      - by ssimpl.
      rewrite <-spec_reads_frame. apply: limplAdj.
      apply: landL2. apply: landL2. by (autorewrite with push_at; reflexivity).

    (* ptest *)
    specapply Htest.
    - by ssimpl.

    (* JCC cond direction BODY *)
    specintro => b.
    specapply JCC_rule.
    - by ssimpl.

    (* Now there are two cases. Either we jumped to the loop body, or we fell
       through and exited the loop. *)
    specsplit.
    - autorewrite with push_at. rewrite ->landL2; last reflexivity.
      rewrite <-spec_later_impl, <-spec_later_weaken.
      (* pbody *)
      specapply Hbody.
      - sdestruct. move/eqP => ->. by ssimpl.
      rewrite <-spec_reads_frame. apply: limplAdj.
      apply: landL2. autorewrite with push_at. cancel1. by ssimpl.

    (* End of loop *)
    rewrite <-spec_reads_frame. apply: limplAdj.
    apply: landL2. apply: landL1. autorewrite with push_at.
    cancel1. sdestruct. move/eqP => ->. by ssimpl.
  Qed.
  
  (* Special case if the test is read-only *)
  Lemma while_rule_ro ptest cond (direction:bool) pbody (I:bool->_) S:
    let P := (Exists b, I b) ** (Exists b, ConditionIs cond b) in
    S |-- basic P ptest (Exists b, I b ** ConditionIs cond b) ->
    S |-- basic (I direction ** ConditionIs cond direction) pbody P ->
    S |-- basic P (while ptest cond direction pbody)
                (I (~~direction) ** ConditionIs cond (~~direction)).
  Proof. apply while_rule. Qed.

  Definition whileWithExit (ptest: program) 
      (cond: Condition) (direction: bool)
      (pbody: DWORD -> program) (pcoda: program) : program :=
    LOCAL BODY;
    LOCAL test;
    LOCAL SKIP;
        JMP test;;
      BODY:;;
        pbody SKIP;;
      test:;;
        ptest;;
        JCC cond direction BODY;;
        pcoda;;
      SKIP:;.

  Lemma whileWithExit_rule ptest cond (direction:bool) pbody pcoda (I:bool->_) P Q S:
    S |-- basic P ptest (Exists b, I b ** ConditionIs cond b) ->
    (forall SKIP, S |-- basic (I direction ** ConditionIs cond direction) (pbody SKIP) P) ->
    S |-- basic (I (~~direction) ** ConditionIs cond (~~direction)) pcoda Q ->
    S |-- basic P (whileWithExit ptest cond direction pbody pcoda) Q.
  Proof.
    move=> Htest Hbody Hcoda. apply basic_local => BODY. apply basic_local => test.
    apply basic_local => SKIP.
    rewrite /basic. specintros => i j. unfold_program.
    specintros => _ _ <- ->  _ _ <- -> i1 i2 i3 -> ->. rewrite !empSPL.

    (* We need to set up Lob induction but not for this instruction. This is a
       bit awkward. *)
    assert (|> safe @ (EIP ~= test ** P) -->>
        safe @ (EIP~=i ** P) //\\ safe @ (EIP ~= test ** P) |--
            safe @ (EIP~=i ** P)) as Hlob.
    - etransitivity; [|by apply landL1].
      instantiate (1 := safe @ (EIP ~= test ** P)).
      apply spec_lob_context. autorewrite with push_later.
      autorewrite with push_at. apply: limplL; first exact: landL2.
      exact: landL1. apply _.
    rewrite <-Hlob => {Hlob}.

    specsplit.
    (* JMP TEST *)
    - specapply JMP_I_rule.
      - by ssimpl.
      rewrite <-spec_reads_frame. apply: limplAdj.
      apply: landL2. apply: landL2. by (autorewrite with push_at; reflexivity).

    (* ptest *)
    specapply Htest.
    - by ssimpl.

    (* JCC cond direction BODY *)
    specintro => b.
    specapply JCC_rule.
    - by ssimpl.

    (* Now there are two cases. Either we jumped to the loop body, or we fell
       through and exited the loop. *)
    specsplit.
    - autorewrite with push_at. rewrite ->landL2; last reflexivity.
      rewrite <-spec_later_impl, <-spec_later_weaken.
      (* pbody *)
      specapply (Hbody SKIP).
      - sdestruct. move/eqP => ->. by ssimpl.
      rewrite <-spec_reads_frame. apply: limplAdj.
      apply: landL2. autorewrite with push_at. cancel1. by ssimpl.

    (* End of loop *)
    specapply Hcoda. sdestructs => EQ.  rewrite (eqP EQ). sbazooka. 
    rewrite <-spec_reads_frame. apply: limplAdj.
    apply: landL2. apply: landL1. autorewrite with push_at. 
    cancel1. by ssimpl. 
  Qed.
  


End While.

