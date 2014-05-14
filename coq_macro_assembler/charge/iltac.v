Require Import ilogic.

Set Implicit Arguments.
Unset Strict Implicit.

Section PullQuantifier.
  Context {A} `{IL: ILogic A}.

  Inductive term :=
    | t_atom (P : A)
    | t_and (t1 t2 : term)
    | t_exists T (f : T -> A)
    | t_forall T (f : T -> A)
    | t_propand (P : Prop) (t : term)
    | t_propimpl (P : Prop) (t : term).

  Fixpoint eval (t : term) : A :=
    match t with
      | t_atom P => P
      | t_and t1 t2 => eval t1 //\\ eval t2
      | t_exists _ f => Exists a, f a
      | t_forall _ f => Forall a, f a
      | t_propand p t => p /\\ eval t
      | t_propimpl p t => p ->> eval t
    end.
  
  Record find_res := mkf {
    find_type : Type;
    find_closure : find_type -> A
  }.

  Fixpoint find_exists (t: term) : option find_res :=
    match t with
      | t_and t1 t2 =>
        match find_exists t1 with
          | Some (mkf _ f1) => Some (mkf (fun P' => (f1 P') //\\ eval t2))
          | None =>
            match find_exists t2 with
              | Some (mkf _ f2) => Some (mkf (fun P' => eval t1 //\\ (f2 P')))
              | None => None
            end
        end
      | t_propand P t =>
        match (find_exists t) with
          | Some (mkf _ f) => Some (mkf (fun P' => P /\\ (f P')))
          | None => None
        end
      | t_exists _ f => Some (mkf f)
      | _ => None
    end.

  Fixpoint find_forall (t: term) : option find_res :=
    match t with
      | t_and t1 t2 =>
        match find_forall t1 with
          | Some (mkf _ f1) => Some (mkf (fun P' => (f1 P') //\\ eval t2))
          | None =>
            match find_forall t2 with
              | Some (mkf _ f2) => Some (mkf (fun P' => eval t1 //\\ (f2 P')))
              | None => None
            end
        end
      | t_propand P t =>
        match (find_forall t) with
          | Some (mkf _ f) => Some (mkf (fun P' => P /\\ (f P')))
          | None => None
        end
      | t_forall _ f => Some (mkf f)
      | _ => None
    end.

  Fixpoint find_propand (t: term) : option (Prop * A) :=
    match t with
      | t_and t1 t2 =>
        match find_propand t1 with
          | Some (P, Q) => Some (P, Q //\\ eval t2)
          | None =>
            match find_propand t2 with
              | Some (P, Q) => Some (P, eval t1 //\\ Q)
              | None => None
            end
        end
      | t_propand P t => Some (P, eval t)
      | _ => None
    end.

  Fixpoint find_propimpl (t: term) : option (Prop * A) :=
    match t with
      | t_and t1 t2 =>
        match find_propimpl t1 with
          | Some (P, Q) => Some (P, Q //\\ eval t2)
          | None =>
            match find_propimpl t2 with
              | Some (P, Q) => Some (P, eval t1 //\\ Q)
              | None => None
            end
        end
      | t_propimpl P t => Some (P, eval t)
      | _ => None
    end.

End PullQuantifier.

Section PullExistential.
  Context {A} `{IL: ILogic A}.

  Lemma find_correct_exists_pull t:
    match find_exists t with
    | Some (mkf _ f) => eval t |-- Exists a, f a
    | None => True
    end.
  Proof.
    induction t; simpl; try tauto.
    - destruct (find_exists t1) as [[T f]|].
      + rewrite -> IHt1, landexistsD; reflexivity.
      + destruct (find_exists t2) as [[T f]|]; [|tauto].
        rewrite -> IHt2, landC, landexistsD. 
        setoid_rewrite landC at 1; reflexivity.
    - reflexivity.
    - fold find_exists. destruct (find_exists t) as [[T f]|]; [|tauto].
      rewrite IHt, lpropandexistsD; reflexivity.
  Qed.

  Lemma find_correct_exists_push t:
    match find_exists t with
    | Some (mkf _ f) => Exists a, f a |-- eval t
    | None => True
    end.
  Proof.
    induction t; simpl; try tauto.
    - destruct (find_exists t1) as [[T f]|].
      + rewrite <- IHt1, landexistsD; reflexivity.
      + destruct (find_exists t2) as [[T f]|]; [|tauto].
        rewrite <- IHt2, landC, landexistsD.
        setoid_rewrite landC at 1; reflexivity.
    - reflexivity.
    - destruct (find_exists t) as [[T f]|]; [|tauto].
      rewrite <- IHt, lpropandexistsD; reflexivity.
  Qed.

  Lemma find_correct_exists t:
    match find_exists t with
    | Some (mkf _ f) => eval t -|- Exists a, f a
    | None => True
    end.
  Proof.
    pose proof (find_correct_exists_pull t) as Hpull.
    pose proof (find_correct_exists_push t) as Hpush.
    destruct (find_exists t) as [[T f]|]; [split; assumption|tauto].
  Qed.

  Lemma find_lhs_exists t Q:
    match find_exists t with
    | Some (mkf _ f) => (forall a, f a |-- Q) -> eval t |-- Q
    | None => True
    end.
  Proof.
    pose proof (@find_correct_exists_pull t) as Hpull.
    destruct (find_exists t) as [[T f]|]; [..|tauto].
    intros HQ. rewrite Hpull; apply lexistsL; assumption.
  Qed.

  Lemma find_rhs_exists t P:
    match find_exists t with
    | Some (mkf _ f) => P |-- Exists a, f a -> P |-- eval t
    | None => True
    end.
  Proof.
    pose proof (find_correct_exists_push t) as Hpush.
    destruct (find_exists t) as [[H f]|]; [..|tauto].
    rewrite Hpush; intros; assumption.
  Qed.

End PullExistential.
  
Ltac quote_term_exists P :=
  match P with
    | ?P1 //\\ ?P2 =>
      let t1 := quote_term_exists P1 in
      let t2 := quote_term_exists P2 in
      constr:(t_and t1 t2)
    | lexists ?f => constr:(t_exists f)
    | ?P1 /\\ ?P2 =>
      let t := quote_term_exists P2 in
      constr:(t_propand P1 t)
    | _ => constr:(t_atom P)
  end.

Ltac lexistsL :=
  match goal with
    | |- ?P |-- ?Q =>
      let t := quote_term_exists P in
      apply (find_lhs_exists t Q) || fail 1 "No existential found in" P;
        cbv [eval]
    | |- _ => fail 1 "Goal is not an entailment"
  end.

Ltac lexistsR_aux x :=
  match goal with
    | |- ?P |-- ?Q =>
      let t := quote_term_exists Q in
      apply (find_rhs_exists t P);
        cbv [eval]; apply lexistsR with x || fail 1 "Unable to existentialise" x "in" P
    | |- _ => fail 1 "Goal is not an entailment"
  end.

Tactic Notation "lexistsR" constr(x) := lexistsR_aux x.

Section ExampleExists.
  Context {A} `{IL: ILogic A}.
  Variable f: nat -> A.

  Example ex1 P: P //\\ (Exists x1, 0 = 1 /\\ f x1) //\\ (Exists x2, f (1 + x2)) |-- ltrue.
  Proof.
    lexistsL; intro a; lexistsL; intro b.
    Fail lexistsL. apply ltrueR.
  Qed.
  
  Example ex2 P : lfalse |-- P //\\ (Exists x1, 0 = 0 /\\ f x1) //\\ (Exists x2, f (1 + x2)).
  Proof.
    lexistsR 0.
    lexistsR 0.
    apply (lfalseL).
  Qed.
End ExampleExists.

Section PullUniversal.
  Context {A} `{IL: ILogic A}.

  Lemma find_correct_forall_pull t:
    match find_forall t with
    | Some (mkf _ f) => eval t |-- Forall a, f a
    | None => True
    end.
  Proof.
    induction t; simpl; try tauto.
    - destruct (find_forall t1) as [[T f]|].
      + rewrite -> IHt1, landforallDL; reflexivity.
      + destruct (find_forall t2) as [[B f]|]; [|tauto].
        rewrite -> IHt2, landC, landforallDL. 
        setoid_rewrite landC at 1; reflexivity.
    - reflexivity.
    - fold find_forall. destruct (find_forall t) as [[H f]|]; [|tauto].
      rewrite IHt, lpropandforallDL; reflexivity.
  Qed.

  Lemma find_correct_forall_push t:
    match find_forall t with
    | Some (mkf T f) => Inhabited T -> Forall a, f a |-- eval t
    | None => True
    end.
  Proof.
    induction t; simpl; try tauto.
    - destruct (find_forall t1) as [[T f]|].
      + intro IT. rewrite <- IHt1, landforallDR; [reflexivity | assumption].
      + destruct (find_forall t2) as [[T f]|]; [|tauto].
        intro IT. rewrite <- IHt2, landC, <- landforallDR;
        [setoid_rewrite landC at 1; reflexivity | assumption].
    - reflexivity.
    - destruct (find_forall t) as [[T f]|]; [|tauto].
      intro IT; rewrite <- IHt, lpropandforallDR; [reflexivity | assumption].
  Qed.

  Lemma find_lhs_forall t Q:
    match find_forall t with
    | Some (mkf _ f) => (Forall a, f a |-- Q) -> eval t |-- Q
    | None => True
    end.
  Proof.
    pose proof (@find_correct_forall_pull t) as Hpull.
    destruct (find_forall t) as [[H f]|]; [..|tauto].
    intros HQ. rewrite Hpull; assumption.
  Qed.

  Lemma find_rhs_forall t P:
    match find_forall t with
    | Some (mkf T f) => Inhabited T -> (forall a, P |-- f a) -> P |-- eval t
    | None => True
    end.
  Proof.
    pose proof (find_correct_forall_push t) as Hpush.
    destruct (find_forall t) as [[T f]|]; [..|tauto].
    intros HT. rewrite <- Hpush; [apply lforallR |assumption]. 
  Qed.

End PullUniversal.
  
  Ltac quote_term_forall P :=
    match P with
    | ?P1 //\\ ?P2 =>
        let t1 := quote_term_forall P1 in
        let t2 := quote_term_forall P2 in
        constr:(t_and t1 t2)
    | lforall ?f => constr:(t_forall f)
    | ?P1 /\\ ?P2 =>
      let t := quote_term_forall P2 in
      constr:(t_propand P1 t)
    | _ => constr:(t_atom P)
    end.

  Ltac lforallL_aux x :=
    match goal with
    | |- ?P |-- ?Q =>
        let t := quote_term_forall P in
        apply (find_lhs_forall t Q);
        cbv [eval]; apply lforallL with x || fail 1 "Unable to existentialise" x "in" P
    | |- _ => fail 1 "Goal is not an entailment"
    end.

  Ltac lforallR :=
    first [apply lforallR | 
    match goal with
    | |- ?P |-- ?Q =>
        let t := quote_term_forall Q in
        apply (find_rhs_forall t P);
        cbv [eval]; [apply _ || fail 1 "Not an inhabited type" |]
    | |- _ => fail 1 "Goal is not an entailment"
    end].

  Tactic Notation "lforallL" constr(x) := lforallL_aux x.

  Section ExampleForall.
    Context {A} `{IL: ILogic A}.
    Variable f: nat -> A.

    Example fa1 P: P //\\ (Forall x1, 0 = 1 /\\ f x1) //\\ (Forall x2, f (1 + x2)) |-- ltrue.
    Proof.
      lforallL 0. lforallL 1.
      Fail lforallL 0. apply ltrueR.
    Qed.
    
    Example fa2 P : lfalse |-- P //\\ (Forall x1, 0 = 0 /\\ f x1) //\\ (Forall x2, f (1 + x2)).
    Proof.
      lforallR; intro x.
      lforallR; intro y.
      apply (lfalseL).
    Qed.
  End ExampleForall.

Section PullAndProp.
  Context {A} `{IL: ILogic A}.

  Lemma find_correct_and_pull t:
    match find_propand t with
    | Some (P, Q) => eval t |-- P /\\ Q
    | None => True
    end.
  Proof.
    induction t; simpl; try tauto.
    - destruct (find_propand t1) as [[T f]|].
      + rewrite -> IHt1. unfold lpropand.
        lexistsL; intro a; lexistsR a; reflexivity.
      + destruct (find_propand t2) as [[T f]|]; [|tauto].
        rewrite -> IHt2; unfold lpropand.
        lexistsL; intro a; lexistsR a; rewrite landC; reflexivity.
    - reflexivity.
  Qed.

  Lemma find_correct_and_push t:
    match find_propand t with
    | Some (P, Q) => P /\\ Q |-- eval t
    | None => True
    end.
  Proof.
    induction t; simpl; try tauto.
    - destruct (find_propand t1) as [[T f]|].
      + rewrite <- IHt1; unfold lpropand.
        lexistsL; intro a; lexistsR a; reflexivity.
      + destruct (find_propand t2) as [[T f]|]; [|tauto].
        rewrite <- IHt2; unfold lpropand.
        lexistsL; intro a; lexistsR a; rewrite landC; reflexivity.
    - reflexivity.
  Qed.

  Lemma find_correct_and t:
    match find_propand t with
    | Some (P, Q) => eval t -|- P /\\ Q
    | None => True
    end.
  Proof.
    pose proof (find_correct_and_pull t) as Hpull.
    pose proof (find_correct_and_push t) as Hpush.
    destruct (find_propand t) as [[T f]|]; [split; assumption|tauto].
  Qed.

  Lemma find_lhs_and t R:
    match find_propand t with
    | Some (P, Q) => (P -> Q |-- R) -> eval t |-- R
    | None => True
    end.
  Proof.
    pose proof (@find_correct_and_pull t) as Hpull.
    destruct (find_propand t) as [[T f]|]; [..|tauto].
    intros HR. rewrite Hpull; apply lpropandL; assumption.
  Qed.

  Lemma find_rhs_and t P:
    match find_propand t with
    | Some (Q, R) => (P |-- R) /\ Q -> P |-- eval t
    | None => True
    end.
  Proof.
    pose proof (find_correct_and_push t) as Hpush.
    destruct (find_propand t) as [[Q R]|]; [..|tauto].
    intros [HR HQ].
    rewrite <- Hpush. apply lpropandR; assumption.
  Qed.

End PullAndProp.
  
Ltac quote_term_andprop P :=
  match P with
    | ?P1 //\\ ?P2 =>
      let t1 := quote_term_andprop P1 in
      let t2 := quote_term_andprop P2 in
      constr:(t_and t1 t2)
    | ?P1 /\\ ?P2 => constr:(t_propand P1 (t_atom P2))
    | _ => constr:(t_atom P)
  end.

Ltac lpropandL :=
  match goal with
    | |- ?P |-- ?Q =>
      let t := quote_term_andprop P in
      apply (find_lhs_and t Q) || fail 1 "No propositional found in" P;
        cbv [eval]
    | |- _ => fail 1 "Goal is not an entailment"
  end.

Ltac lpropandR :=
  match goal with
    | |- ?P |-- ?Q =>
      let t := quote_term_andprop Q in
      apply (find_rhs_and t P);
        cbv [eval]; split || fail 1 "No propositional found in" P
    | |- _ => fail 1 "Goal is not an entailment"
  end.

Section ExamplePropAnd.
  Context {A} `{IL: ILogic A}.
  Variable f: nat -> A.

  Example exprop1 P: P //\\ (Exists x1, 0 = 1 /\\ f x1) //\\ (Exists x2, f (1 + x2)) |-- ltrue.
  Proof.
    lexistsL; intro a; lexistsL; intro b.
    lpropandL; intro H.
    Fail lexistsL. apply ltrueR.
  Qed.
  
  Example exprop2 P : lfalse |-- P //\\ (Exists x1, 0 = 0 /\\ f x1) //\\ (Exists x2, f (1 + x2)).
  Proof.
    lexistsR 0.
    lexistsR 0.
    lpropandR.
    apply (lfalseL).
    reflexivity.
  Qed.
End ExamplePropAnd.

Section PullPropImpl.
  Context {A} `{IL: ILogic A}.

  Lemma find_correct_impl_pull t:
    match find_propimpl t with
    | Some (P, Q) => eval t |-- P ->> Q
    | None => True
    end.
  Proof.
    induction t; simpl; try tauto.
    - destruct (find_propimpl t1) as [[T f]|].
      + rewrite -> IHt1. unfold lpropimpl.
        lforallR; intro H; lforallL H; reflexivity.
      + destruct (find_propimpl t2) as [[T f]|]; [|tauto].
        rewrite -> IHt2; unfold lpropimpl.
        lforallR; intro H; lforallL H; reflexivity.
    - reflexivity.
  Qed.

  Lemma find_lhs_impl t R:
    match find_propimpl t with
    | Some (P, Q) => (P /\ Q |-- R) -> eval t |-- R
    | None => True
    end.
  Proof.
    pose proof (@find_correct_impl_pull t) as Hpull.
    destruct (find_propimpl t) as [[T f]|]; [..|tauto].
    intros [HT HR]. rewrite Hpull; apply lpropimplL; assumption.
  Qed.

End PullPropImpl.
  
Ltac quote_term_implprop P :=
  match P with
    | ?P1 //\\ ?P2 =>
      let t1 := quote_term_implprop P1 in
      let t2 := quote_term_implprop P2 in
      constr:(t_and t1 t2)
    | ?P1 ->> ?P2 => constr:(t_propimpl P1 (t_atom P2))
    | _ => constr:(t_atom P)
  end.

Ltac lpropimplL :=
  match goal with
    | |- ?P |-- ?Q =>
      let t := quote_term_implprop P in
      apply (find_lhs_impl t Q) || fail 1 "No propositional found in" P;
        cbv [eval]; split
    | |- _ => fail 1 "Goal is not an entailment"
  end.

Ltac lpropimplR x := apply lpropimplR; intro x.

Section ExamplePropImpl.
  Context {A} `{IL: ILogic A}.
  Variable f: nat -> A.

  Example expropimpl1 P: P //\\ (Exists x1, 0 = 0 ->> f x1) //\\ (Exists x2, f (1 + x2)) |-- ltrue.
  Proof.
    lexistsL; intro a; lexistsL; intro b.
    lpropimplL. reflexivity.
    Fail lpropimplL. apply ltrueR.
  Qed.

End ExamplePropImpl.


