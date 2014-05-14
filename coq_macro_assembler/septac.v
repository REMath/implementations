Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq.
Require Import SPred.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Existentials.
  Inductive term :=
  | t_atom (P: SPred)
  | t_star (t1 t2: term)
  | t_ex A (f: A -> SPred)
  | t_propand (P: Prop) (Q: SPred).

  Fixpoint eval (t: term) : SPred :=
    match t with
    | t_atom P => P
    | t_star t1 t2 => eval t1 ** eval t2
    | t_ex _ f => lexists f
    | t_propand P Q => P /\\ Q
    end.

  Record find_res := mkf {
    find_type: Type;
    find_closure: find_type -> SPred
  }.

  (**
     Given a term t, when this function succeeds, it will return an SPred with
     one existential quantifier removed and the quantified variable free.
     Notice:
     - Recall that [P /\\ Q] is defined at [Exists _: P, Q], so that works too.
     - We do eval as part of this process rather than afterwards. This is
       because as soon as we represent "terms with a free variable" as
       functions, there isn't any structure left to do elimination on anyway.
     - There is no attempt to find multiple existentials. This keeps the code
       simple, and the tactic needs to be iterated in any case as long as we
       don't look under binders to find nested existentials.
     - The [term] type is a bit wasteful since it reflects the whole formula
       despite only needing the path down to the first existential. Optimising
       that may require more Ltac programming, so it is not guaranteed to be
       faster.
  *)
  Fixpoint find (t: term) : option find_res :=
    match t with
    | t_atom _ => None
    | t_star t1 t2 =>
        match find t1 with
        | Some (mkf _ f1) => Some (mkf (fun P' => (f1 P') ** eval t2))
        | None =>
            match find t2 with
            | Some (mkf _ f2) => Some (mkf (fun P' => eval t1 ** (f2 P')))
            | None => None
            end
        end
    | t_ex _ f => Some (mkf f)
    | t_propand P Q => Some (mkf (fun _: P => Q))
    end.

  Lemma find_correct_pull t:
    match find t with
    | Some (mkf _ f) => eval t |-- Exists a, f a
    | None => True
    end.
  Proof.
    elim: t; red => //.

      rewrite -/find /eval -/eval.
      move=> t1 Ht1 t2 Ht2.
      destruct (find t1) as [[A f]|].
      - rewrite ->Ht1. apply: sepSPAdj. apply: lexistsL => a. apply: wandSPAdj.
        by apply lexistsR with a.
      destruct (find t2) as [[A f]|].
      - rewrite ->Ht2. rewrite sepSPC. apply: sepSPAdj. apply: lexistsL => a.
        apply: wandSPAdj. rewrite sepSPC. by apply lexistsR with a.
      done.

      reflexivity.

      reflexivity.
  Qed.

  Lemma find_correct_push t:
    match find t with
    | Some (mkf _ f) => Exists a, f a |-- eval t
    | None => True
    end.
  Proof.
    elim: t; red => //.
    - rewrite -/find /eval -/eval.
      move=> t1 Ht1 t2 Ht2.
      destruct (find t1) as [[A f]|].
      - apply: lexistsL => a. cancel2. rewrite <-Ht1. by apply lexistsR with a.
      destruct (find t2) as [[A f]|].
      - apply: lexistsL => a. cancel2. rewrite <-Ht2. by apply lexistsR with a.
      done.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma find_correct t:
    match find t with
    | Some (mkf _ f) => eval t -|- Exists a, f a
    | None => True
    end.
  Proof.
    move: (@find_correct_push t) (@find_correct_pull t).
    case: (find t); last done. move=> []; by split.
  Qed.

  Lemma find_lhs t Q:
    match find t with
    | Some (mkf _ f) => (forall a, f a |-- Q) -> eval t |-- Q
    | None => True
    end.
  Proof.
    move: (@find_correct_pull t). destruct (find t) as [[A f]|]; last done.
    move=> Heval HQ. rewrite ->Heval. exact: lexistsL.
  Qed.

  Lemma find_rhs t P:
    match find t with
    | Some (mkf _ f) => forall a, P |-- f a -> P |-- eval t
    | None => True
    end.
  Proof.
    move: (@find_correct_push t). destruct (find t) as [[A f]|]; last done.
    move=> Hft a HPf. rewrite <-Hft. by apply lexistsR with a.
  Qed.

  Lemma sdestruct_hyp t s (G: Prop):
    match find t with
    | Some (mkf _ f) => (forall a, (f a) s -> G) -> (eval t) s -> G
    | None => True
    end.
  Proof.
    move: (@find_correct_pull t). destruct (find t) as [[A f]|]; last done.
    move=> Htf HG Ht. specialize (Htf _ Ht). destruct Htf as [a Htf]. eauto.
  Qed.
  
  Ltac quote_term P :=
    match P with
    | ?P1 ** ?P2 =>
        let t1 := quote_term P1 in
        let t2 := quote_term P2 in
        constr:(t_star t1 t2)
    | lexists ?f => constr:(t_ex f)
    | ?P /\\ ?Q => constr:(t_propand P Q)
    | _ => constr:(t_atom P)
    end.

  Ltac sdestruct :=
    match goal with
    | |- ?P |-- ?Q =>
        let t := quote_term P in
        apply: (@find_lhs t Q) || fail 1 "Nothing to destruct";
        cbv [eval]
    | |- _ => fail 1 "Goal is not an entailment"
    end.

  Ltac sdestruct_hyp H :=
    move: H;
    match goal with
    | |- (ILFunFrm_pred ?P) ?s -> ?G =>
        let t := quote_term P in
        apply: (@sdestruct_hyp t s G) || fail 1 "Nothing to destruct";
        cbv [eval]
    | |- _ => fail 1 "Hypothesis not of the expected form"
    end.

  Ltac ssplit :=
    match goal with
    | |- ?P |-- ?Q =>
        let t := quote_term Q in
        (* If you change "eapply" to "apply:", you will get the side side
           condition you just proved in the t_propand case as an extra
           assumption in the main goal. I'm thinking that's not usually what
           you want. *)
        eapply (@find_rhs t P) || fail 1 "Nothing to split";
        cbv [eval]
    | |- _ => fail 1 "Goal is not an entailment"
    end.

  Section Example.
    Variable P: SPred.
    Variable f: nat -> SPred.

    Example ex1: P ** (Exists x1, 0 = 1 /\\ f x1) ** (Exists x2, f (1 + x2)) |-- ltrue.
    Proof.
      sdestruct => a. sdestruct => H. sdestruct => b.
      Fail sdestruct. apply: ltrueR.
    Qed.
    
    Example ex2: lfalse |-- P ** (Exists x1, 0 = 0 /\\ f x1) ** (Exists x2, f (1 + x2)).
    Proof.
      ssplit. ssplit; first done. ssplit. Fail ssplit.
      instantiate (1:=0). instantiate (1:=0). done.
    Qed.
  End Example.
End Existentials.

(* This tactic pulls one existential quantifier or pure proposition out of an
   SPred entailment. It should be syntactically visible, possibly nested under
   stars. *)
Ltac sdestruct := Existentials.sdestruct.

(* This tactic removes one existential quantifier or pure proposition from the
   right-hand side of an entailment goal. Existentials get instantiated by
   metavariables (like eexists), and pure propositions are created as subgoals.
 *)
Ltac ssplit := Existentials.ssplit.

(* Iterated version of sdestruct. *)
Ltac sdestructs :=
  sdestruct; let x := fresh "x" in move=> x; try sdestructs; move: x.

(* Iterated version of ssplit. *)
Ltac ssplits := ssplit; [..|try ssplits].

Tactic Notation "sdestruct" ":" hyp(H) := (Existentials.sdestruct_hyp H).

Module Solving.
  (* We index atoms in the environment with type idx, which is just a wrapper
     for nat. We cannot use any nat-specific functions on it, though, since
     cbv'ing these might cbv parts of the atom if that same function happens
     to be used there. The solution is to redefine such functions under a new
     name. *)
  Section Indexes.
    Definition idx := nat.
    
    Definition eqn' (i j: idx) := Eval red in eqn i j.

    Lemma eqn'P i j : reflect (i = j) (eqn' i j).
    Proof. apply eqnP. Qed.
  End Indexes.
  
  Inductive term :=
  | t_atom (i: idx)
  | t_star (t1 t2: term)
  | t_emp
  | t_false.

  (* Idea: reflect lhs first and choose index for each rhs term with a hole to
     be the first lhs atom that unifies. *)

  Definition alist := seq (idx * SPred).
  Definition env := (idx * alist)%type.

  Fixpoint lookup (a: alist) (i: idx) : SPred :=
    match a with
    | (j,P) :: a' => if eqn' i j then P else lookup a' i
    | [::] => empSP (* default value; shouldn't happen *)
    end.

  Fixpoint eval (e: env) (t: term) : SPred :=
    match t with
    | t_atom i => let (_, a) := e in lookup a i
    | t_star t1 t2 => eval e t1 ** eval e t2
    | t_emp => empSP
    | t_false => lfalse
    end.

  (* Inserts an SPred into an environment. Calls its continuation with the
     updated environment and the index where the predicate was inserted. *)
  Ltac insert_tac e(*:env*) P(*:SPred*) cont(*: env -> idx -> tactic *) :=
    match e with
    | (?i, ?a) => cont (i.+1, (i,P)::a) i
    end.

  (* Quote left-hand side of entailment. Duplicated terms don't get to share
     indices since this should not typically happen. *)
  (* This tactic is in CPS style to be consistent with rquote and because it
     "returns" both an updated environment and a quoted term. Ltac doesn't make
     it easy to return tuples, but CPS is easy. *)
  Ltac lquote e(*:env*) P(*:SPred*) cont(*: env -> term -> tactic *) :=
    match P with
    | ?P1 ** ?P2 =>
        lquote e P1 ltac:(fun e t1 =>
        lquote e P2 ltac:(fun e t2 =>
        cont e (t_star t1 t2)))
    | lfalse => cont e t_false
    | empSP => cont e t_emp
    | _ => insert_tac e P ltac:(fun e i => cont e (t_atom i))
    end.

  (*
  Goal forall P: SPred, True.
    move=> P.
    lquote ((0, [::]) : env) (P ** empSP ** P ** lprop (0 + 0 = 0)) ltac:(fun e t =>
      idtac e; idtac t;
      let P := eval cbv [eval lookup eqn'] in (eval e t) in idtac P
    ).
    apply I. Qed.
  *)

  (* Succeed iff t fails *)
  Tactic Notation "not" tactic1(t) := try (t; fail 1).

  (* This tactic succeeds if its two arguments are equal modulo alpha conversion
     and evars. As a side effect, those evars get instantiated. The power and
     complexity of this tactic falls somewhere between the built-in [constr_eq]
     and [unify] tactics. *)
  (* The programming pattern here with match/first/fail is an attempt to
     emulate if/then/else in Ltac. The first/fail pattern serves to prevent
     automatic back-tracking, analogous to "cut" in Prolog. *)
  Ltac cheap_unify a b :=
    match a with
    | _ => is_evar a; first [unify a b | fail 1]
    | _ => is_evar b; first [unify a b | fail 1]
    | _ => not (has_evar a); not (has_evar b); first [constr_eq a b | fail 1]
    | ?fa ?xa =>
        match b with
        | ?fb ?xb => cheap_unify fa fb; cheap_unify xa xb
        end
    end.

  (* This looks up P in the range of the association list a and calls the
     appropriate continuation. It will look for P modulo instantiation of evars
     inside P and a. *)
  Ltac lookup_tac a(*:alist*) P(*:SPred*)
      found(*: idx -> tactic*) notfound(*: unit -> tactic*) :=
    match a with
    | (?i, ?P') :: _ =>
      (* We don't unify with something that's entirely an evar. This would lead
         to very random behaviour. *)
      not (is_evar P'); cheap_unify P P'; found i
    | _ :: ?a' => lookup_tac a' P found notfound
    | _ => notfound tt
    end.

  (* Quote right-hand side of entailment. Any atoms that are already in the env
     will be re-used. Existential metavariables will be instantiated greedily
     to match atoms in env. *)
  (* This tactic has to be in CPS because it refers to lookup_tac, which calls
     the [unify] tactic (https://github.com/coq/coq/commit/18e6108339aaf18499).
   *)
  Ltac rquote e(*:env*) P(*:SPred*) cont(*: env -> term -> tactic *) :=
    match P with
    | ?P1 ** ?P2 =>
        rquote e P1 ltac:(fun e t1 =>
        rquote e P2 ltac:(fun e t2 =>
        cont e (t_star t1 t2)))
    | empSP => cont e t_emp
    | lfalse => cont e t_false
    | ltrue =>
          (* We don't match up ltrue. We leave it untouched on the right-hand
             side and let the user decide what to do with it. *)
           insert_tac e P ltac:(fun e i => cont e (t_atom i))
    | ?dummy_name => is_evar P;
          (* If an atom is entirely an evar, we don't touch it. Otherwise, it
             would unify with the first thing it saw on the left, which is
             probably not what the user expects. *)
           insert_tac e P ltac:(fun e i => cont e (t_atom i))
    | _ =>
        match e with
        | (_, ?a) =>
          lookup_tac a P
            ltac:(fun j => cont e (t_atom j))
            ltac:(fun _ => insert_tac e P ltac:(fun e i => cont e (t_atom i)))
        end
    end.

  Fixpoint remove_atom t i : option term :=
    match t with
    | t_atom i' => if eqn' i' i then Some t_emp else None
    | t_star t1 t2 =>
        match remove_atom t1 i with
        | Some t1' => Some (t_star t1' t2)
        | None =>
            match remove_atom t2 i with
            | Some t2' => Some (t_star t1 t2')
            | None => None
            end
        end
    | t_emp => None
    | t_false => None
    end.

  Fixpoint remove (tP tQ: term) : option term :=
    match tQ with
    | t_atom i => remove_atom tP i
    | t_star t1 t2 =>
        match remove tP t1 with
        | Some tP' => remove tP' t2
        | None => None
        end
    | t_emp => Some tP
    | t_false => None
    end.
  
  Lemma remove_atom_correct e t i tR:
    remove_atom t i = Some tR ->
    eval e t |-- eval e (t_atom i) ** eval e tR.
  Proof.
    move: tR. elim: t; try done.
    - move=> i' tR /=. case: eqn'P => // [->] [<-].
      by rewrite empSPR.
    - move=> t1 IHt1 t2 IHt2 tR /=.
      destruct (remove_atom t1 i) as [t1'|].
      - move=> [<-]. rewrite ->IHt1; last reflexivity. rewrite sepSPA.
        reflexivity.
      destruct (remove_atom t2 i) as [t1'|]; last done.
      move=> [<-]. rewrite ->IHt2; last reflexivity.
      rewrite -sepSPA [_ ** eval e (t_atom i)]sepSPC sepSPA. reflexivity.
  Qed.
    
  Lemma remove_correct e tP tQ tR:
    remove tP tQ = Some tR ->
    eval e tP |-- eval e tQ ** eval e tR.
  Proof.
    move: tP tR. elim: tQ.
      move=> i tP tR /= HtR. exact: remove_atom_correct.

      move=> t1 IHt1 t2 IHt2 tP tR /=.
      specialize (IHt1 tP).
      destruct (remove tP t1) as [tP'|]; last done.
      move=> HtR. move/(_ _ _ HtR): IHt2 => Ht2.
      rewrite sepSPA. rewrite <-Ht2. exact: IHt1.

      move=> tP tR /= [<-]. by rewrite empSPL.

      move=> tP tR /=. done. 
  Qed.

  Fixpoint simplify (tP tQ: term) : (term * term) :=
    match tQ with
    | t_atom i =>
        match remove_atom tP i with
        | Some tP' => (tP', t_emp)
        | None => (tP, tQ)
        end
    | t_star t1 t2 =>
        let (tP', t1')  := simplify tP t1 in
        let (tP'', t2') := simplify tP' t2 in
        (tP'', t_star t1' t2')
    | t_emp => (tP, tQ)
    | t_false => (tP, tQ)
    end.

  (* Correctness theorem strong enough for induction. *)
  (* This theorem could probably be strengthened to biimplication if that
     seems useful at some point. *)
  Lemma simplify_correct e tP tQ tP' tQ' :
    simplify tP tQ = (tP', tQ') -> exists tR,
    (eval e tP |-- eval e tP' ** eval e tR)  /\
    (eval e tQ' ** eval e tR |-- eval e tQ).
  Proof.
    move: tP tP' tQ'. elim: tQ.
    - move=> i tP tP' tQ' /=.
      have Hatom := @remove_atom_correct e tP i.
      destruct (remove_atom tP i).
      - move=> [<- <-]. exists (t_atom i). rewrite ->Hatom; last reflexivity.
        rewrite empSPL. split; last reflexivity. by rewrite sepSPC.
      - move=> [<- <-]. exists t_emp. rewrite !empSPR. split; reflexivity.
    - move=> t1 IHt1 t2 IHt2 tP tP'' tQ' /=.
      specialize (IHt1 tP). destruct (simplify tP t1) as [tP' t1'].
      specialize (IHt2 tP'). destruct (simplify tP' t2) as [ttmp t2'].
      move=> [Htmp <-] /=. subst ttmp.
      edestruct IHt1 as [tR1 [Hpre1 Hpost1]]; first reflexivity.
      edestruct IHt2 as [tR2 [Hpre2 Hpost2]]; first reflexivity.
      clear IHt1 IHt2. exists (t_star tR1 tR2) => /=. split.
      - rewrite ->Hpre1, Hpre2. by rewrite sepSPA [eval e tR2 ** _]sepSPC.
      - rewrite <-Hpost1. rewrite <-Hpost2. rewrite -sepSPA.
        rewrite [_ ** eval e tR1]sepSPA [_ ** eval e tR1]sepSPC.
        by rewrite !sepSPA.
    - move=> tP tP' tQ' /= [<- <-]. exists t_emp.
      rewrite !empSPR. split; reflexivity.
    - move=> tP tP' tQ' /= [<- <-]. exists t_emp.
      rewrite !empSPR. split; reflexivity.
  Qed.
  
  (* Weaker version of correctness theorem. *)
  Corollary simplify_sufficient e tP tQ tP' tQ' :
    simplify tP tQ = (tP', tQ') ->
    eval e tP' |-- eval e tQ'  ->  eval e tP |-- eval e tQ.
  Proof.
    move=> Heq H. have [tR [H1 H2]] := simplify_correct e Heq.
    rewrite ->H1, <-H2. cancel2.
  Qed.

  (* remove emp *)
  Fixpoint clean t :=
    match t with
    | t_star t1 t2 =>
        let t1' := clean t1 in
        let t2' := clean t2 in
        match t1', t2' with
        | t_false, t' => t_false
        | t', t_false => t_false
        | t_emp, t' => t'
        | t', t_emp => t'
        | _, _ => t_star t1' t2'
        end
    | _ => t
    end.

  Lemma clean_correct e t : eval e (clean t) -|- eval e t.
  Proof.
    induction t; try reflexivity; []. rewrite /=.
    destruct (clean t1); destruct (clean t2); rewrite -IHt1 -IHt2;
      try rewrite empSPL; try rewrite empSPR; 
      try rewrite sepSP_falseL; try rewrite sepSP_falseR; reflexivity.
  Qed.

  Lemma do_simplify e tP tQ tP' tQ':
    simplify tP tQ = (tP', tQ') ->
    eval e (clean tP') |-- eval e (clean tQ')  ->  eval e tP |-- eval e tQ.
  Proof. rewrite !clean_correct. apply simplify_sufficient. Qed.

  (* If speed is an issue at some point, we could make rquote take two
     environments: one to insert into and one to lookup in. Our decision
     procedures never care about duplicated atoms on either side -- only atoms
     in common between left and right. *)
  Ltac ssimpl :=
    match goal with
    |- ?P |-- ?Q =>
        lquote ((0, [::]) : env) P ltac:(fun e tP =>
          rquote e Q ltac:(fun e tQ =>
            eapply (@do_simplify e tP tQ);
            [ cbv; reflexivity
            | cbv [eval lookup eqn' clean]
            ]
          )
        )
    end.

  Example ex0: forall P Q: SPred, exists n,
        ltrue ** (1 = 1 /\\ empSP) ** P ** Q |-- (Q ** (n = 1 /\\ empSP)) ** ltrue.
  Proof. move=> P Q. eexists. ssimpl. done. Qed.

  (* TODO: probably subsumed by do_simplify, but this should be faster *)
  Lemma solve_uc e tP tQ:
    if remove tP tQ is Some _
    then eval e tP |-- eval e tQ ** ltrue
    else True.
  Proof.
    move Hresult: (remove tP tQ) => result.
    destruct result; last done.
    have Hcorrect := remove_correct Hresult.
    etransitivity; [apply Hcorrect|]. cancel2.
  Qed.

  Ltac solve_uc :=
    match goal with
    |- ?P |-- ?Q ** ltrue =>
        lquote ((0, [::]) : env) P ltac:(fun e tP =>
          rquote e Q ltac:(fun e tQ =>
            apply (@solve_uc e tP tQ)
          )
        )
    end.

  Example ex1: forall P Q: SPred, exists n,
        (1 = 1 /\\ empSP) ** P ** Q |-- (Q ** (n = 1 /\\ empSP)) ** ltrue.
  Proof. move=> P Q. eexists. solve_uc. Qed.
End Solving.

Ltac ssimpl := Solving.ssimpl.

(** Overpowered super-tactic *)
Ltac sbazooka :=
  try sdestructs => * //; (* leaves 0 or 1 subgoal *)
  try ssplits; (* last subgoal is the entailment *)
  [..| done || (try ssimpl)] => //.

