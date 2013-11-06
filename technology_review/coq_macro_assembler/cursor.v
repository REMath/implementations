(*===========================================================================
    In order to formalize memory ranges, and reading the very last byte in 
    memory, we introduce a type of Cursor, which is either an actual
    address or the address beyond the top of memory. In other words, this is
    just [0..2^n] where n is the number of bits in an address.
  ===========================================================================*)
Require Import ssreflect ssrfun ssrnat ssrbool finfun eqtype fintype tuple seq.
Require Import choice tuple.
Require Import bitsrep bitsprops bitsops bitsopsprops nathelp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Cursors.

(*=Cursor *)
Variable n:nat.
Inductive Cursor := 
| mkCursor : BITS n -> Cursor
| hwm.
(*=End *)

(* Embedding into nat -- for proofs only! *)
Definition cursorToNat pos := if pos is mkCursor p then toNat p else 2^n.

(*---------------------------------------------------------------------------
    next: BITS n -> Cursor n
    and its properties
  ---------------------------------------------------------------------------*)
Definition next (p:BITS n) := if p == ones _ then hwm else mkCursor (incB p).

Definition nextCursor (p:Cursor) :=
  if p is mkCursor pos then next pos else hwm.

Lemma nextIsInc (p q: BITS n) : next p = mkCursor q -> p+#1 = q. 
Proof. rewrite /next. move => EQ. 
case E: (p == ones n). rewrite E in EQ. done. 
rewrite E in EQ. rewrite addB1. congruence. 
Qed. 

Lemma nextIsHwm (p: BITS n) : next p = hwm -> p+#1 = #0.
Proof. rewrite /next. move => EQ. 
case E: (p == ones n). rewrite E in EQ. rewrite (eqP E). 
rewrite addB1. rewrite incB_ones. by rewrite fromNat0.
by rewrite E in EQ. 
Qed. 

Lemma cursorToNat_next pos : cursorToNat (next pos) = (toNat pos).+1. 
Proof. rewrite /next. case TOP: (pos == ones _).
+ simpl. rewrite (eqP TOP). rewrite toNat_ones. rewrite prednK => //. apply expn_gt0. 
+ rewrite /cursorToNat. rewrite toNat_incB. by rewrite TOP. 
Qed. 

Lemma cursorToNat_inj: injective cursorToNat.
Proof.
  move => [p|] [q|] /= H.
  - f_equal. exact: toNat_inj.
  - have Hlt := toNatBounded p. rewrite H in Hlt.
    move/ltP: Hlt. intros. exfalso. omega.
  - have Hlt := toNatBounded q. rewrite -H in Hlt.
    move/ltP: Hlt. intros. exfalso. omega.
  - done.
Qed.

(*---------------------------------------------------------------------------
    Order relations on Cursor
  ---------------------------------------------------------------------------*)
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

Lemma ltNext (p:BITS n) : ltCursor (mkCursor p) (next p).
Proof. by rewrite ltCursor_nat cursorToNat_next. Qed. 

Lemma leNext (p:BITS n) : leCursor (mkCursor p) (next p).
Proof. by rewrite leCursor_nat cursorToNat_next. Qed.

Lemma leCursor_next (p: BITS n) q: leCursor (next p) q = ltCursor (mkCursor p) q.
Proof. by rewrite leCursor_nat ltCursor_nat cursorToNat_next. Qed.

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


Fixpoint nexts k (c: Cursor) : option (Cursor) :=
  match k , c with
  | 0 , _ => Some c
  | k'.+1 , mkCursor p => nexts k' (next p)
  | k'.+1 , hwm => None
  end.

(*---------------------------------------------------------------------------
    Subtraction
  ---------------------------------------------------------------------------*)
Definition subCursor (p q: Cursor) : Cursor :=
  match p, q with
  | _, hwm => mkCursor (zero _)
  | mkCursor p', mkCursor q' => 
    if leB p' q' then mkCursor (zero _) else mkCursor (subB p' q')
  | hwm, mkCursor p' => 
    if p' == zero _ then hwm else mkCursor (negB p')
  end.


Lemma cursorToNat_sub (p q: Cursor) : 
  cursorToNat (subCursor p q) = cursorToNat p - cursorToNat q. 
Proof. 
elim: p => [p' |] /=. 
elim: q => [q' |] /=. 
case LE: (leB p' q'). 
rewrite leB_nat in LE. rewrite /= toNat_zero. 
have H := subn_eq0 (toNat p') (toNat q') . 
rewrite LE in H. by rewrite (eqP H). simpl. apply toNat_subB.
rewrite leB_nat.  
rewrite leB_nat in LE. 
have L:= @leq_total (toNat p') (toNat q'). rewrite LE in L. apply L. 

have B := toNatBounded p'. rewrite toNat_zero. have H:= subn_eq0 (toNat p') (2^n). 
suff: (0 == (toNat p' - 2^n)). move => H'. by rewrite -(eqP H'). 
rewrite eq_sym H. apply: ltnW B. 

elim: q => [q' |] /=.  
case E: (q' == zero _). 
by rewrite /= (eqP E) toNat_zero subn0. 
rewrite /= toNat_negB. 
have H1: (0 = (toNat (zero n))). by rewrite toNat_zero. 
rewrite {1}H1. 
by rewrite -bitsEq_nat E. 
by rewrite toNat_zero subnn. 
Qed. 

(*---------------------------------------------------------------------------
    Range testing
  ---------------------------------------------------------------------------*)
Definition inRange p q := fun p' => leCursor p p' && ltCursor p' q.
Definition outRange p q := fun p' => ltCursor p' p && leCursor q p'.

Lemma inRange_next (p p': BITS n) :
  inRange (mkCursor p) (next p) (mkCursor p') -> p' = p.
Proof.
  rewrite /inRange.
  rewrite leCursor_nat ltCursor_nat cursorToNat_next /= ltnS.
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
      subst. exact: cursorToNat_inj.
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
      subst q. constructor. apply IHHpq. rewrite cursorToNat_next in Hq.
      by injection Hq.
  - done.
Qed.

End Cursors.

Coercion mkCursor : BITS >-> Cursor.

Lemma subCursor_next n (p: BITS n.+1) : 
  subCursor (next p) p = fromNat 1.
Proof. apply cursorToNat_inj.  
rewrite cursorToNat_sub. rewrite cursorToNat_next.
rewrite /cursorToNat. rewrite subSn => //. rewrite subnn. rewrite toNat_fromNatBounded => //. 
apply pow2_gt1. 
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

