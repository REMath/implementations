(*===========================================================================
    In order to formalize memory ranges, and reading the very last byte in 
    memory, we introduce a type of Cursor, which is either an actual
    address or the address beyond the top of memory. In other words, this is
    just [0..2^n] where n is the number of bits in an address.
  ===========================================================================*)
Require Import ssreflect ssrfun ssrnat ssrbool finfun eqtype fintype tuple seq.
Require Import choice tuple.
Require Import bitsrep bitsprops bitsops bitsopsprops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Cursors.

Variable n:nat.

Inductive Cursor := 
| mkCursor : BITS n -> Cursor
| hwm.

(* Order relation on Cursor *)
Definition ltCursor (pos1 pos2: Cursor) := 
  match pos1, pos2 with
  | hwm, _ => false
  | mkCursor p1, mkCursor p2 => ltB p1 p2
  | mkCursor _, hwm => true
  end.
Definition leCursor (pos1 pos2: Cursor) := 
  match pos1, pos2 with
  | _, hwm => true
  | hwm, mkCursor _ => false
  | mkCursor p1, mkCursor p2 => leB p1 p2
  end.
Definition next (p:BITS n) := if p == ones _ then hwm else mkCursor (incB p).

Definition nextCursor (p:Cursor) :=
  if p is mkCursor pos then next pos else hwm.

(* Embedding into nat *)
Definition cursorToNat pos := if pos is mkCursor p then toNat p else 2^n.

Lemma ltCursor_nat pos1 pos2 : ltCursor pos1 pos2 = (cursorToNat pos1 < cursorToNat pos2).
Proof. destruct pos1 => //. destruct pos2 => //. by rewrite /=ltB_nat.  
simpl. by rewrite toNatBounded.
destruct pos2 => //.  
simpl. symmetry. apply negbTE. rewrite -leqNgt. apply ltnW. apply toNatBounded.
simpl. by rewrite ltnn.  
Qed. 

Lemma leCursor_nat pos1 pos2 : leCursor pos1 pos2 = (cursorToNat pos1 <= cursorToNat pos2).
Proof. destruct pos1 => //. destruct pos2 => //. by rewrite /=leB_nat.  
simpl. symmetry. apply ltnW. apply toNatBounded.
destruct pos2 => //.  
simpl. symmetry. apply negbTE. rewrite -ltnNge. apply toNatBounded. 
simpl. by rewrite leqnn. 
Qed.

Lemma next_nat pos : cursorToNat (next pos) = (toNat pos).+1. 
Proof. rewrite /next. case TOP: (pos == ones _).
+ simpl. rewrite (eqP TOP). rewrite toNat_ones. rewrite prednK => //. apply expn_gt0. 
+ rewrite /cursorToNat. rewrite toNat_incB. by rewrite TOP. 
Qed. 

Lemma ltNext (p:BITS n) : ltCursor (mkCursor p) (next p).
Proof. by rewrite ltCursor_nat next_nat. Qed. 

Lemma leNext (p:BITS n) : leCursor (mkCursor p) (next p).
Proof. by rewrite leCursor_nat next_nat. Qed.

Lemma leCursor_next (p: BITS n) q: leCursor (next p) q = ltCursor (mkCursor p) q.
Proof. by rewrite leCursor_nat ltCursor_nat next_nat. Qed.

Lemma leCursor_refl pos : leCursor pos pos. 
Proof. by rewrite leCursor_nat. Qed.

Lemma leCursor_weaken pos1 pos2 : ltCursor pos1 pos2 -> leCursor pos1 pos2. 
Proof. rewrite ltCursor_nat leCursor_nat. apply ltnW. Qed.

Lemma leCursor_trans pos1 pos2 pos3 : leCursor pos1 pos2 -> leCursor pos2 pos3 -> leCursor pos1 pos3.
Proof. rewrite !leCursor_nat. apply leq_trans. Qed.

Lemma ltCursor_trans pos1 pos2 pos3 : ltCursor pos1 pos2 -> ltCursor pos2 pos3 -> ltCursor pos1 pos3.
Proof. rewrite !ltCursor_nat. apply ltn_trans. Qed. 

Lemma ltCursor_leCursor_trans pos1 pos2 pos3 : ltCursor pos1 pos2 -> leCursor pos2 pos3 -> ltCursor pos1 pos3.
Proof. move => H1 H2.
case E1: pos1 => [p1 |]; subst.
case E2: pos2 => [p2 |]; subst.
case E3: pos3 => [p3 |]; last done; subst. 
rewrite /ltCursor in H1. rewrite /leCursor in H2. 
apply: ltB_leB_trans H1 H2.
case E3: pos3 => [p3 |]; subst; done. 
case E2: pos2 => [p2 |]; subst; done. 
Qed.

Lemma leCursor_ltCursor_trans pos1 pos2 pos3 : leCursor pos1 pos2 -> ltCursor pos2 pos3 -> ltCursor pos1 pos3.
Proof. rewrite !ltCursor_nat !leCursor_nat. apply leq_ltn_trans. Qed.

Lemma leCursor_Ngt pos1 pos2 : leCursor pos1 pos2 = ~~ (ltCursor pos2 pos1).
Proof. rewrite leCursor_nat ltCursor_nat. apply leqNgt. Qed. 

Definition inRange p q := fun p' => leCursor p p' && ltCursor p' q.
Definition outRange p q := fun p' => ltCursor p' p && leCursor q p'.

Lemma inRange_next (p p': BITS n) :
  inRange (mkCursor p) (next p) (mkCursor p') -> p' = p.
Proof.
  rewrite /inRange.
  rewrite leCursor_nat ltCursor_nat next_nat /= ltnS.
  move=> H. symmetry. apply: toNat_inj. exact: anti_leq.
Qed.

(* If there's a range [p;q[ divided up by a p', then any p'' in that
   range will be either on the left of p' or on the right of p'. *)
Lemma inRange_case (p' p q p'': Cursor):
  inRange p q p'' ->
  leCursor p p' ->
  leCursor p' q ->
  inRange p p' p'' \/ inRange p' q p''.
Proof.
  move/andP => [Hpp'' Hp''q] Hpp' Hp'q.
  case H: (ltCursor p'' p').
  - left. rewrite /inRange. by rewrite H Hpp''.
  - right. rewrite /inRange. by rewrite Hp''q leCursor_Ngt H.
Qed.

Lemma cursorToNatI: injective cursorToNat.
Proof.
  move => [p|] [q|] /= H.
  - f_equal. exact: toNat_inj.
  - have Hlt := toNatBounded p. rewrite H in Hlt.
    move/ltP: Hlt. intros. exfalso. omega.
  - have Hlt := toNatBounded q. rewrite -H in Hlt.
    move/ltP: Hlt. intros. exfalso. omega.
  - done.
Qed.

(* Together with lemma LeCursorP, this allows doing induction over leCursor.
 *)
Inductive LeCursor p: Cursor -> Prop :=
| LeCursor_refl: LeCursor p p
| LeCursor_next q: LeCursor p (mkCursor q) -> LeCursor p (next q).

(* Only one direction proved for now
Lemma LeCursorP (p q: Cursor n): reflect (LeCursor p q) (leCursor p q).
*)
Lemma LeCursorP p q: leCursor p q -> LeCursor p q.
Proof.
  rewrite leCursor_nat.
  move Hpq: (cursorToNat p <= cursorToNat q) => pq.
  destruct pq (*; constructor *) => [_|H].
  - move/leP: Hpq. move Hp: (cursorToNat p) => np.
    move Hq: (cursorToNat q) => nq. move=> Hpq.
    move: q Hq. induction Hpq as [|nq] => q Hq.
    - have ->: p = q; last by constructor.
      subst. exact: cursorToNatI.
    - have [q' Hq']: exists q': BITS n, next q' = q.
      - move: Hq. clear. case: q => /=.
        - move=> q Hq. exists (decB q). rewrite /next.
          rewrite decBK. move HisOnes: (decB q == ones _) => b.
          destruct b; last done. (* now the impossible case *)
          have HdecB: decB q = ones n by apply (eqP HisOnes).  
          rewrite -decB_zero in HdecB.
          eapply can_inj in HdecB; last by apply decBK. subst.
          rewrite toNat_zero in Hq. done.
        - move=> _. exists (ones n). unfold next.
          rewrite eq_refl; by [|apply: zero (* TODO: fix the lemma *)].
      subst q. constructor. apply IHHpq. rewrite next_nat in Hq.
      by injection Hq.
  - done.
Qed.
End Cursors.

Coercion mkCursor : BITS >-> Cursor.

Lemma nextIsInc n (p q: BITS n) : mkCursor q = next p -> q = p+#1. 
Proof. rewrite /next. move => EQ. 
case E: (p == ones n). rewrite E in EQ. done. 
rewrite E in EQ. rewrite addB1. congruence. 
Qed. 

Lemma neNext n (p:BITS n) : next p <> p. 
Proof. rewrite /next.
destruct n. 
+ by rewrite (tuple0 p)/=. 
+ case E: (p == ones _) => //. have IB:= @incBDistinct _ p. congruence. 
Qed. 

(* Because Cursor is essentially isomorphic to option, we can inherit
   many canonical structures. *)
Section CursorCanonicals.
  Variable n: nat.
  
  Definition cursor_option (p: Cursor n) : option (BITS n) :=
    if p is mkCursor p' then Some p' else None.

  Definition option_cursor (o: option (BITS n)) : Cursor n :=
    if o is Some p' then mkCursor p' else hwm n.

  Lemma cursor_optionC: cancel cursor_option option_cursor.
  Proof. by move=> [p|] /=. Qed.

  Definition Cursor_eqMixin := CanEqMixin cursor_optionC.
  Canonical Structure Cursor_eqType :=
    Eval hnf in EqType (Cursor n) Cursor_eqMixin.

  Definition Cursor_countMixin := CanCountMixin cursor_optionC.
  Definition Cursor_choiceMixin := CountChoiceMixin Cursor_countMixin.
  Canonical Structure Cursor_choiceType :=
    Eval hnf in ChoiceType _ Cursor_choiceMixin.
  Canonical Structure Cursor_countType :=
    Eval hnf in CountType _ Cursor_countMixin.
  
  Definition Cursor_finMixin := Eval hnf in CanFinMixin cursor_optionC.
  Canonical Structure Cursor_finType := Eval hnf in FinType _ Cursor_finMixin.
End CursorCanonicals.


Section CursorSeq.
  Variable n: nat. 

  (* Cursor_seq p q s: sequence of memory addresses s represents the
     memory between cursor p inclusive and q exclusive *)
  Inductive Cursor_seq: Cursor n -> Cursor n -> seq (BITS n) -> Prop :=
  | CS_nil p: Cursor_seq p p nil
  | CS_cons p q s (HCS_next: Cursor_seq (next p) q s): Cursor_seq p q (p::s).

  Lemma Cursor_seq_merge p q r s1 s2:
    Cursor_seq p q s1 -> Cursor_seq q r s2 ->
    Cursor_seq p r (s1 ++ s2).
  Proof. elim; first done. constructor; auto. Qed.

  Lemma Cursor_seq_snoc p (q: BITS _) s:
    Cursor_seq p q s -> Cursor_seq p (next q) (s ++ [:: q]).
  Proof.
    move=> Hpq. eapply Cursor_seq_merge. eassumption. 
    constructor; constructor.
  Qed.

  Lemma Cursor_seq_le p q s: Cursor_seq p q s -> leCursor p q.
  Proof.
    elim; first exact: leCursor_refl.
    move=> {p q s} p q s _. rewrite leCursor_next. apply: leCursor_weaken.
  Qed.

  Lemma Cursor_seq_cons_lt s : forall p q p1, Cursor_seq p q (p1::s) -> p = p1 /\ ltCursor p1 q.
  Proof. induction s => p q p1 CS. inversion CS. subst. 
  inversion HCS_next. subst. split; first done. apply ltNext.  
  inversion CS. subst. specialize (IHs _ _ _ HCS_next). 
  destruct IHs as [H1 H2]. split; first done.   
  have CSL := Cursor_seq_le CS. 
  have H3 := ltNext p1. 
  rewrite H1 in H3. 
  apply (ltCursor_trans H3 H2). 
  Qed. 

  Lemma Cursor_seq_id s : forall p, Cursor_seq p p s -> s=nil. 
  Proof. move => p CS. destruct s; first done. 
  have CSNE := Cursor_seq_cons_lt CS. destruct CSNE as [H1 H2]. rewrite H1 in H2. 
  rewrite /ltCursor in H2. rewrite ltB_nat in H2. by rewrite ltnn in H2. Qed. 

  Lemma Cursor_seq_next (p:BITS n) s : Cursor_seq p (next p) s -> s = [::p]. 
  Proof. move => CS. destruct s. inversion CS. subst. have LTN:= ltNext p. 
  rewrite H1 in LTN. rewrite /ltCursor in LTN. destruct (next p). rewrite ltB_nat in LTN.  
  by rewrite ltnn in LTN. done. 
  inversion CS. subst. apply Cursor_seq_id in HCS_next. by rewrite HCS_next. 
  Qed. 

End CursorSeq.

Lemma Cursor_seq_BYTE n (p:BITS n.+1) s m : Cursor_seq (p +# m) (p +# m.+1) s -> s = [::p+#m]. 
Proof. rewrite -(addn1 m). rewrite addB_addn. move => CS.
apply Cursor_seq_next. 
case E: (next (p +# m)) => [q |]. 
- rewrite /next in E. 
  case E': (p +# m == ones _). 
  + by rewrite E' in E. 
  + rewrite E' in E. rewrite -addB1 in E. by rewrite E in CS. 
- rewrite /next in E. 
  case E': (p +# m == ones _).
  + rewrite E' in E. rewrite (eqP E') in CS. 
  have CSL := Cursor_seq_le CS. rewrite /leCursor addB1 incB_ones in CSL.
  rewrite leB_nat toNat_ones toNat_zero in CSL.
  rewrite expnS in CSL. rewrite leqn0 in CSL. 
  case E'': (2^n) => [| n']. have HH:= expn_gt0 2 n. by rewrite E'' in HH. 
  rewrite E'' in CSL. by rewrite mul2n doubleS in CSL. 
rewrite E' in E. done. 
Qed. 


