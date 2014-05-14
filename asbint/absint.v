(* This file was tested successfully with coq-8.2beta4.
  It will not run with coq-8.1. *)

Require Import String ZArith Bool List.
Open Scope Z_scope.

Inductive aexpr : Type :=
  anum (x:Z) | avar (s:string) | aplus (e1 e2:aexpr).

Inductive bexpr : Type :=
 blt (e1 e2 : aexpr).

Inductive instr : Type := 
  assign (x:string)(e:aexpr)
| seq (i1 i2:instr)
| while (b:bexpr)(i:instr).

Fixpoint af (g:string->Z)(e:aexpr) : Z :=
  match e with
    anum x => x
  | avar n => g n
  | aplus e1 e2 => af g e1 + af g e2
  end.

Definition bf (g:string->Z)(b:bexpr) : bool :=
  match b with
    blt e1 e2 => 
    if Z_lt_dec (af g e1) (af g e2) then true else false
  end.

Inductive assert : Type :=
  pred (p:string)(l:list aexpr)
| a_b (b:bexpr)
| a_conj (a1 a2:assert)
| a_not (a: assert)
| a_true
| a_false.

Fixpoint ia (m:string->list Z->Prop)(g:string->Z)
   (a:assert) : Prop :=
  match a with
    pred s l => m s (map (af g) l)
  | a_b b => bf g b = true
  | a_conj a1 a2 => (ia m g a1) /\ (ia m g a2)
  | a_not a => not (ia m g a)
  | a_true => True
  | a_false => False
  end.

Inductive a_instr : Type :=
  pre (a : assert) (i: a_instr)
| a_assign (x:string)(e:aexpr)
| a_seq (i1 i2:a_instr)
| a_while (b:bexpr)(a:assert)(i:a_instr).

Fixpoint asubst (x:string) (s:aexpr) (e:aexpr) : aexpr :=
  match e with
    anum n => anum n
  | avar x1 => if string_dec x x1 then s else e
  | aplus e1 e2 => aplus (asubst x s e1) (asubst x s e2)
  end.

Definition bsubst (x:string) (s:aexpr) (b:bexpr) : bexpr :=
  match b with
    blt e1 e2 => blt (asubst x s e1) (asubst x s e2)
  end.

Fixpoint subst (x:string) (s:aexpr) (a:assert) : assert :=
  match a with
    pred p l => pred p (map (asubst x s) l)
  | a_b b => a_b (bsubst x s b)
  | a_conj a1 a2 => a_conj (subst x s a1) (subst x s a2)
  | a_not a => a_not (subst x s a)
  | any => any
  end.

Fixpoint pc (i:a_instr) (post : assert) : assert :=
  match i with
    pre a i => a
  | a_assign x e => subst x e post
  | a_seq i1 i2 => pc i1 (pc i2 post)
  | a_while b a i => a
  end.

Inductive cond : Type := imp (a1 a2:assert).

Fixpoint vc (i:a_instr)(post : assert) : list cond :=
  match i with
    pre a i => (imp a (pc i post))::vc i post
  | a_assign _ _ => nil
  | a_seq i1 i2 => vc i1 (pc i2 post)++vc i2 post
  | a_while b a i =>
    (imp (a_conj a (a_b b)) (pc i a))::
    (imp (a_conj a (a_not (a_b b))) post)::
    vc i a
  end.

Fixpoint valid (m:string->list Z ->Prop) (l : list cond) :
  Prop :=
  match l with
    nil => True
  | c::tl =>
    (let (a1, a2) := c in forall g, ia m g a1 -> ia m g a2)
      /\ valid m tl
  end.

Lemma subst_sound_a :
  forall g e x e',
   af g (asubst x e' e) =
   af (fun y => if string_dec x y then af g e' else g y) e.
intros g e x e'; induction e; simpl; auto.
case (string_dec x s); auto.
rewrite IHe1, IHe2; auto.
Qed.

Lemma subst_sound_b :
  forall g b x e',
    bf g (bsubst x e' b) =
    bf (fun y => if string_dec x y then af g e' else g y) b.
intros g b x e'; destruct b as [e1 e2]; simpl; auto.
repeat rewrite subst_sound_a; auto.
Qed.

Lemma subst_sound_l :
  forall g l x e',
    map (af g) (map (asubst x e') l) =
    map (af (fun y => if string_dec x y then af g e' else g y)) l.
intros g l x e'; induction l; simpl; auto.
rewrite subst_sound_a, IHl; auto.
Qed.

Lemma subst_sound :
  forall m g a x e',
    ia m g (subst x e' a) =
    ia m (fun y => if string_dec x y then af g e' else g y) a.
intros m g a x e'; induction a; simpl; auto.
rewrite subst_sound_l; solve[auto].
rewrite subst_sound_b; solve[auto].
rewrite IHa1, IHa2; solve[auto].
rewrite IHa; solve[auto].
Qed.

Lemma valid_app :
  forall m l1 l2, valid m l1 -> valid m l2 -> valid m (l1++l2).
intros m l1 l2; induction l1; simpl; auto; destruct a; intuition.
Qed.

Lemma valid_app_decompose :
  forall m l1 l2, valid m (l1++l2) -> valid m l1 /\ valid m l2.
intros m l1 l2; induction l1; simpl; auto.
intros [v1 v2]; destruct (IHl1 v2) as [v3 v4]; auto.
Qed.

Lemma vc_monotonic :
  forall m i p1 p2, (forall g, ia m g p1 -> ia m g p2) ->
   valid m (vc i p1) ->
   valid m (vc i p2) /\
   (forall g, ia m g (pc i p1) -> ia m g (pc i p2)).
intros m; induction i; intros p1 p2 p1p2 vc1.
   simpl in vc1; destruct vc1 as [vca vc1];
   destruct (IHi p1 p2 p1p2 vc1) as [IHi' IHi'']; simpl; auto.
  simpl; split; auto.
  intros g; repeat rewrite subst_sound; auto.
 simpl in vc1; destruct (valid_app_decompose _ _ _ vc1) as [vc2 vc3].
 simpl; split; auto.
 apply valid_app.
 elim (IHi1 (pc i2 p1) (pc i2 p2)); auto.
 elim (IHi2 p1 p2);auto.
 elim (IHi2 p1 p2);auto.
 elim (IHi1 (pc i2 p1) (pc i2 p2)); auto.
 elim (IHi2 p1 p2);auto.
simpl in vc1; destruct vc1 as [vc1 [vc2 vc3]].
simpl; split; auto.
Qed. 

Fixpoint cleanup (i: a_instr) : instr :=
  match i with
    pre a i => cleanup i
  | a_assign x e => assign x e
  | a_seq i1 i2 => seq (cleanup i1) (cleanup i2)
  | a_while b a i => while b (cleanup i)
  end.

Section absint.

Variables (A : Type) (from_Z : Z -> A)
  (top : A) (a_add : A -> A -> A).

Variables (to_pred : A -> aexpr -> assert)
  (m : string->list Z ->Prop).
Hypothesis top_sem : forall e,  (to_pred top e) = a_true.
Hypothesis to_pred_sem :
  forall g v e, ia m g (to_pred v e) =
     ia m g (to_pred v (anum (af g e))).
Hypothesis subst_to_pred :
  forall v x e e', subst x e' (to_pred v e) =
     to_pred v (asubst x e' e).
Hypothesis from_Z_sem :
  forall g x, ia m g (to_pred (from_Z x) (anum x)).
Hypothesis a_add_sem : forall g v1 v2 x1 x2,
  ia m g (to_pred v1 (anum x1)) ->
  ia m g (to_pred v2 (anum x2)) ->
  ia m g (to_pred (a_add v1 v2) (anum (x1+x2))).

Definition state := list (string*A).

Fixpoint lookup (s:state) (x:string) : A :=
  match s with
    nil => top
  | (y,v)::tl => if string_dec x y then v else lookup tl x
  end.

Fixpoint a_upd(x:string)(v:A)(l:state) : state :=
  match l with
    nil => (x,v)::nil
  | (y,v')::tl =>
    if string_dec x y then (y, v)::tl else (y,v')::a_upd x v tl
  end.

Fixpoint a_af (s:state)(e:aexpr) : A :=
  match e with
    avar x => lookup s x
  | anum n => from_Z n
  | aplus e1 e2 => a_add (a_af s e1) (a_af s e2)
  end.

Fixpoint s_to_a (s:state) : assert :=
  match s with
    nil => a_true
  | (x,a)::tl => a_conj (to_pred a (avar x)) (s_to_a tl)
  end.
(* keep this comment for consistency with the paper absint.tex *)

Fixpoint ab1 (i:instr)(s:state) : a_instr*state :=
  match i with
    assign x e =>
    (pre (s_to_a s) (a_assign x e), a_upd x (a_af s e) s)
  | seq i1 i2 => 
    let (a_i1, s1) := ab1 i1 s in
    let (a_i2, s2) := ab1 i2 s1 in
      (a_seq a_i1 a_i2, s2)
  | while b i =>
    let (a_i, _) := ab1 i nil in
        (a_while b (s_to_a nil) a_i, nil)
  end.

Fixpoint mem (s:string)(l:list string): bool :=
 match l with
   nil => false
 | x::l => if string_dec x s then true else mem s l
 end.

Fixpoint no_dups (s:state)(l:list string) :bool :=
 match s with
   nil => true
 | (s,_)::tl => if mem s l then false else no_dups tl (s::l)
 end.

Definition consistent (s:state) := no_dups s nil = true.

Lemma consistent_nil : consistent nil.
unfold consistent; simpl; auto.
Qed.

Hint Resolve consistent_nil.

Lemma no_dups_update :
  forall s l x v, mem x l = false ->
   no_dups s l = true -> no_dups (a_upd x v s) l = true.
induction s; simpl; auto.
intros l x v q _; rewrite q; auto.
destruct a as [y v'].
intros l x v qm; simpl; case (string_dec x y); simpl; auto.
intros xy q; destruct (mem y l); auto.
rewrite IHs; auto.
simpl; case (string_dec y x); simpl; auto.
intros abs; case xy; rewrite abs; auto.
Qed.

Lemma consistent_update :
  forall s x v, consistent s -> consistent (a_upd x v s).
intros s x v; exact (no_dups_update s nil x v (refl_equal _)).
Qed.

Lemma lookup_sem : forall s g, ia m g (s_to_a s) -> 
  forall x, ia m g (to_pred (lookup s x) (anum (g x))).
induction s; intros g; simpl.
intros; rewrite top_sem; auto.
destruct a as [x v].
simpl.
intros [i1 i2] y; case (string_dec y x).
rewrite to_pred_sem in i1; simpl in i1.
intros; subst; auto.
intros; apply IHs; auto.
Qed.

Lemma mem_transpose :
  forall l z x y l', mem z (l++x::y::l')=mem z (l++y::x::l').
induction l; simpl; intros z x y l'.
case (string_dec x z); case (string_dec y z); auto.
case (string_dec a z); auto.
Qed.

Lemma no_dups_transpose :
  forall s l l' x y, no_dups s (l++x::y::l') = no_dups s (l++y::x::l').
induction s; simpl; intros l l' x y; auto.
destruct a as [z v]; rewrite mem_transpose.
assert (IHs' := IHs (z::l) l' x y); simpl in IHs'; rewrite IHs'; auto.
Qed.

Lemma no_dups_transpose_head :
  forall s l' x y, no_dups s (x::y::l') = no_dups s (y::x::l').
intros; apply (no_dups_transpose s nil).
Qed.

Lemma subst_no_occur :
  forall s x l e,
   no_dups s (x::l) = true -> subst x e (s_to_a s) = (s_to_a s).
induction s; simpl; auto.
destruct a as [y v]; intros x l e .
destruct (string_dec x y); simpl; try (intros; discriminate).
case_eq (mem y l); simpl; try (intros; discriminate).
intros my d; rewrite subst_to_pred; simpl.
destruct (string_dec x y); try solve[case n; auto].
rewrite (IHs x (y::l) e); auto; rewrite (no_dups_transpose_head); auto.
Qed.

Lemma subst_no_dups :
   forall s g v x e l, no_dups s l = true -> ia m g (s_to_a s) ->
     ia m g (to_pred v (anum (af g e))) ->
     ia m g (subst x e (s_to_a (a_upd x v s))).
induction s; simpl.
intros g v x e _ _ _ p; split; auto.
rewrite subst_to_pred; simpl.
destruct (string_dec x x) as [_ | nxx]; try case nxx; auto.
rewrite to_pred_sem; auto.
destruct a as [y v']; simpl; intros g v x e l d [p1 p2] ve.
destruct (string_dec x y) as [xy | nxy].
subst y; simpl; split.
rewrite subst_to_pred; simpl; destruct (string_dec x x) as [_ | nxx]; 
 try case nxx; auto.
rewrite to_pred_sem; auto.
rewrite (subst_no_occur s x l e); auto.
destruct (mem x l); solve[discriminate | auto].
simpl; split.
rewrite subst_to_pred; simpl.
destruct (string_dec x y); solve[case nxy; auto | auto].
apply IHs with (l:=y::l); auto.
destruct (mem y l); solve[discriminate | auto].
Qed.

Lemma subst_consistent :
  forall s g v x e, consistent s -> ia m g (s_to_a s) ->
    ia m g (to_pred v (anum (af g e))) ->
    ia m g (subst x e (s_to_a (a_upd x v s))).
intros s g v x e; exact (subst_no_dups s g v x e nil).
Qed.

Lemma ab1_pc :
  forall  i i' s s', ab1 i s = (i', s') ->
    forall g a, ia m g (s_to_a s) -> ia m g (pc i' a).
induction i; simpl; intros i' s s' q g a is.
injection q; intros q' q''; subst s' i'; simpl; auto.
case_eq (ab1 i1 s); intros a_i1 s1 q1.
case_eq (ab1 i2 s1); intros a_i2 s2 q2.
rewrite q1, q2 in q; injection q; intros q' q''; subst s' i'; simpl.
apply (IHi1 a_i1 s s1); auto.
destruct (ab1 i nil); injection q; intros; subst i'.
simpl; auto.
Qed.

Lemma a_af_sound : 
  forall s g e, ia m g (s_to_a s) ->
    ia m g (to_pred (a_af s e) (anum (af g e))).
intros s g e i; induction e.
simpl; apply from_Z_sem.
simpl; apply lookup_sem; auto.
simpl; apply a_add_sem; auto.
Qed.

Theorem ab1_correct : forall i i' s s', 
  consistent s ->
  ab1 i s = (i', s') ->
   valid m (vc i' (s_to_a s')) /\ consistent s'.
induction i; simpl.
intros i' s s' c q; injection q; clear q; intros q q'.
rewrite <- q', <- q; simpl; clear q' q.
split;try apply consistent_update; auto; split; auto.
intros g gs; apply subst_consistent; auto.
apply a_af_sound; auto.

intros i' s s' c q; case_eq (ab1 i1 s).
intros a_i1 s1 q1; rewrite q1 in q.
case_eq (ab1 i2 s1); intros a_i2 s2 q2; rewrite q2 in q.
injection q; clear q; intros s's2 i'seq; subst s' i'.
destruct (IHi1 a_i1 s s1 c q1) as [IHi1' IHi1''].
destruct (IHi2 a_i2 s1 s2 IHi1'' q2) as [IHi2' IHi2''].
split; auto.
simpl; apply valid_app; try assumption.
destruct (vc_monotonic m a_i1 (s_to_a s1) (pc a_i2 (s_to_a s2))) as
 [vcm1 vcm2]; auto.
intros g ps1; apply ab1_pc with (1:=q2); auto.
intros i' s s' c; case_eq (ab1 i nil); intros a_i si q1 q; injection q;
intros; subst i' s'.
split; simpl; auto.
split.
intros g _; apply (ab1_pc i a_i nil si); auto.
split; auto.
destruct (IHi a_i nil si) as [v1 c']; auto.
destruct (vc_monotonic m a_i (s_to_a si) a_true); simpl; auto.
Qed.

Theorem ab1_clean : forall i i' s s',
   ab1 i s = (i', s') -> cleanup i' = i.
induction i; simpl; intros i' s s' q; try (injection q; do 2 intro; subst).
simpl; auto.
case_eq (ab1 i1 s); intros ai1 s1 q1; assert (IHi1':= IHi1 ai1 s s1 q1).
case_eq (ab1 i2 s1); intros ai2 s2 q2; assert (IHi2' := IHi2 ai2 s1 s2 q2).
rewrite q1, q2 in q; injection q; do 2 intro; subst; simpl; auto.
case_eq (ab1 i nil); intros s1 i1 q1; rewrite q1 in q; injection q;
do 2 intro; subst; simpl; auto.
apply IHi in q1; rewrite q1; auto.
Qed.


Lemma lookup_sem2 : forall s g l, 
    no_dups s l = true -> 
    (forall x, mem x l = false -> ia m g (to_pred (lookup s x) (avar x))) ->
               ia m g (s_to_a s).
induction s; simpl; intros g l d p; auto.
destruct a as [x v]; simpl; split.
assert (px := p x); simpl in px; destruct (string_dec x x) as [q | nq].
apply px; destruct (mem x l); auto; simpl in d; discriminate.
case nq; auto.
apply (IHs g (x::l)).
destruct (mem x l); solve[discriminate | auto].
simpl; intros y my.
assert (py := p y); destruct (string_dec x y) as [xy | nxy].
destruct (string_dec y x) as [yx | nyx].
discriminate.
case nyx; subst y; auto.
destruct (string_dec y x) as [yx | nyx]; auto.
case nxy; auto.
Qed.

Variables (learn_from_success : state -> bexpr -> option state)
  (learn_from_failure : state -> bexpr -> option state)
  (join : A -> A -> A)
  (thinner : A -> A -> bool)
  (over_approx : nat -> state -> state -> state)
  (choose_1 : state -> instr -> nat)
  (choose_2 : state -> instr -> nat).

Definition s_to_a' (s':option state) : assert :=
  match s' with Some s => s_to_a s | None => a_false end.

Hypothesis learn_from_success_sem :
 forall s b g, consistent s ->
      ia m g (s_to_a s) -> ia m g (a_b b) ->
      ia m g (s_to_a' (learn_from_success s b)).

Hypothesis learn_from_failure_sem :
 forall s b g, consistent s -> ia m g (s_to_a s) -> ~ia m g (a_b b) ->
      ia m g (s_to_a' (learn_from_failure s b)).

Hypothesis over_approx_sem :
  forall g n s s', ia m g (s_to_a s) -> ia m g (s_to_a (over_approx n s s')).

Fixpoint join_state (s1 s2:state) : state :=
  match s1 with
    nil => nil
  | (x,v)::tl => a_upd x (join v (lookup s2 x)) (join_state tl s2)
  end.

Hypothesis join_thinner_1 :  forall a b, thinner a (join a b) = true.

Hypothesis join_thinner_2 :  forall a b, thinner b (join a b) = true.

Hypothesis thinner_sem : forall a1 a2, thinner a1 a2 = true ->
  forall g e, ia m g (to_pred a1 e) -> ia m g (to_pred a2 e).

Lemma join_safe_1 :
  forall g a b x, ia m g (to_pred a x) -> ia m g (to_pred (join a b) x).
intros g a b x iax; apply thinner_sem with (2:= iax); apply join_thinner_1.
Qed.

Lemma join_safe_2 :
  forall g a b x, ia m g (to_pred b x) -> ia m g (to_pred (join a b) x).
intros g a b x iax; apply thinner_sem with (2:= iax); apply join_thinner_2.
Qed.

Lemma upd_x :
  forall g s x e, ia m g (s_to_a (a_upd x e s)) -> ia m g (to_pred e (avar x)).
intros g s; induction s; intros x e; simpl.
intuition.
destruct a as [y v']; simpl; destruct (string_dec x y).
subst y; simpl; intuition.
simpl; intros [_ h]; apply IHs; auto.
Qed.

Lemma upd_others :
  forall g s x e, ia m g (s_to_a (a_upd x e s)) -> forall y, x <> y ->
       ia m g (to_pred (lookup s y) (avar y)).
intros g s; induction s; intros x e; simpl.
intros; rewrite top_sem; simpl; auto.

destruct a as [y v']; destruct (string_dec x y); simpl.
intros [h1 h2] z xnz; destruct (string_dec z y).
subst z; contradiction.
rewrite to_pred_sem; simpl; apply lookup_sem; auto.
intros [iay iau] z xnz; destruct (string_dec z y).
subst; auto.
apply (IHs x e); auto.
Qed.

Lemma mem_more : forall l x a, mem x (a::l) = false -> mem x l = false.
induction l; simpl; auto.
intros x b; destruct (string_dec b x); simpl; intros; discriminate || auto.
Qed.

Lemma no_dups_more_excluded :
  forall s l a, no_dups s (a::l) = true -> no_dups s l = true.
induction s; simpl; auto.
destruct a as [x _].
intros l b; case (string_dec b x).
intros; discriminate.
rewrite no_dups_transpose_head.
intros bnx nd.
assert (main: no_dups s (x::l) = true).
case_eq (no_dups s (b::x::l)); intros h'; rewrite h' in nd; simpl in nd.
apply IHs with (a:=b); auto.
destruct (mem x l); discriminate.
rewrite main; destruct (mem x l); solve [discriminate | auto].
Qed.

Lemma consistent_tail : forall s a, consistent (a::s) -> consistent s.
intros s a c; destruct a as [x v].
apply no_dups_more_excluded with (a:=x); auto.
Qed.

Lemma a_upd_ia_all :
   forall g s l x e, no_dups s l = true ->
      (forall y, y <> x -> mem y l = false ->
            ia m g (to_pred (lookup s y) (avar y))) ->
      ia m g (to_pred e (avar x)) ->
      ia m g (s_to_a (a_upd x e s)).
intros g s; induction s; intros l x e cs; simpl.
intuition.
destruct a as (y, v); simpl.
intros ias iae; destruct (string_dec x y); simpl.
subst x; split; auto.
apply lookup_sem2 with (l:=(y::l)).
simpl in cs; destruct (mem y l); solve[discriminate | auto].

intros x mx; generalize (ias x).
case_eq (mem y l); intros my.
simpl in cs; rewrite my in cs; discriminate.

destruct (string_dec x y); auto.
subst y; simpl in mx; destruct (string_dec x x); simpl in mx.
discriminate mx.
elim n; auto.
assert (mem x l = false).
simpl in mx; destruct (string_dec y x); discriminate || auto.
auto.
split.
generalize (ias y); destruct (string_dec y y);
 try (assert (abs: y<>y) by auto; case abs; auto).
simpl in cs; destruct (mem y l); solve[auto].


apply IHs with (l:= (y::l)).
simpl in cs.
destruct (mem y l); solve [discriminate | auto].
intros z zx mz.
simpl in mz.
generalize (ias z).
destruct (string_dec z y).
destruct (string_dec y z); try discriminate.
elim n0; auto.
destruct (string_dec y z); try discriminate.
auto.
auto.
Qed.

Lemma a_upd_ia_all' :
   forall g s x e, consistent s ->
      (forall y, y <> x -> ia m g (to_pred (lookup s y) (avar y))) ->
      ia m g (to_pred e (avar x)) ->
      ia m g (s_to_a (a_upd x e s)).
intros g s x e cs all iaex; apply a_upd_ia_all with (1:=cs)
  (l:=@nil string); auto.
Qed.


Lemma join_state_consistent :
  forall s1 s2, consistent (join_state s1 s2).
intros s1 s2; induction s1 as [ | [x v] s1 IHs1]; simpl; auto.
apply consistent_update. auto.
Qed.

Lemma join_state_safe_1 :
  forall g s1 s2, ia m g (s_to_a s1) -> ia m g (s_to_a (join_state s1 s2)).
intros g s1 s2; induction s1; simpl; auto.
destruct a as [x v]; simpl; intros [px ias1].
apply a_upd_ia_all'.
apply join_state_consistent.
intros y ynx; rewrite to_pred_sem; simpl.
apply lookup_sem; apply IHs1; auto.
apply join_safe_1; auto.
Qed.

Lemma join_state_safe_2 :
  forall g s1 s2, ia m g (s_to_a s2) -> ia m g (s_to_a (join_state s1 s2)).
intros g s1 s2; induction s1; simpl; auto.
destruct a as [x v]; simpl; intros ias2.
apply a_upd_ia_all'.
apply join_state_consistent.
intros y ynx; rewrite to_pred_sem; simpl.
apply lookup_sem; apply IHs1; auto.
apply join_safe_2.
rewrite to_pred_sem; simpl; apply lookup_sem; auto.
Qed.

Fixpoint mark (i:instr) : a_instr :=
  match i with
    assign x e => pre a_false (a_assign x e)
  | seq i1 i2 => a_seq (mark i1) (mark i2)
  | while b i => a_while b a_false (mark i)
  end.

Definition join_state' (s: state)(s':option state) : state :=
   match s' with
     Some s' => join_state s s'
   | None => s
   end.

Definition step1 (ab: state -> a_instr * option state)
  (b:bexpr) (init s:state) : state :=
  match learn_from_success s b with
    Some s1 => let (_, s2) := ab s1 in join_state' init s2
  | None => s
  end.

Fixpoint step2 (ab: state ->  a_instr * option state)
 (b:bexpr) (init s:state) (n:nat) : state :=
 match n with
   0%nat => s
 | S p => step2 ab b init (step1 ab b init s) p
 end.

Fixpoint s_stable (s1 s2 : state) : bool :=
  match s1 with
    nil => true
  | (x,v)::tl => thinner (lookup s2 x) v && s_stable tl s2
  end.

Definition is_inv (ab:state-> a_instr * option state)
  (s:state)(b:bexpr):bool := s_stable s (step1 ab b s s).

Fixpoint find_inv ab b init s i n : state :=
  let s' := step2 ab b init s (choose_1 s i) in
  if is_inv ab s' b then s' else
    match n with 
      0%nat => nil
    | S p => find_inv ab b init (over_approx p s s') i p
    end.

Definition do_annot (ab:state-> a_instr * option state)
  (b:bexpr) (s:state) (i:instr) : a_instr :=
  match learn_from_success s b with
    Some s' => let (ai, _) := ab s' in ai
  | None => mark i
  end.

Fixpoint ab2 (i:instr)(s:state) : a_instr*option state :=
  match i with
    assign x e =>
    (pre (s_to_a s) (a_assign x e), Some (a_upd x (a_af s e) s))
  | seq i1 i2 => 
    let (a_i1, s1) := ab2 i1 s in
      match s1 with
        Some s1' =>
        let (a_i2, s2) := ab2 i2 s1' in
          (a_seq a_i1 a_i2, s2)
      | None => (a_seq a_i1 (mark i2), None)
      end
  | while b i =>
    let inv := find_inv (ab2 i) b s s i (choose_2 s i) in
        (a_while b (s_to_a inv)
              (do_annot (ab2 i) b inv i),
         learn_from_failure inv b) 
  end.

Lemma step1_pc : forall g ab b s s', 
  ia m g (s_to_a s) -> ia m g (s_to_a s') -> 
  ia m g (s_to_a (step1 ab b s s')).
intros g ab b s s' ias ias'.
unfold step1; destruct (learn_from_success s' b) as [s2 | ]; auto.
destruct (ab s2) as [i2 [s2' | ]]; unfold join_state'; auto.
apply join_state_safe_1; auto.
Qed.


Lemma step2_pc : forall g ab b n s s',
  ia m g (s_to_a s) -> ia m g (s_to_a s') ->
  ia m g (s_to_a (step2 ab b s s' n)).
intros g ab b n; induction n; simpl; try solve[intuition].
intros s s' ias ias'; apply IHn; auto.
intros; apply step1_pc; auto.
Qed.
   
Lemma find_inv_pc : 
   forall g ab n init s b i, 
   ia m g (s_to_a s) -> ia m g (s_to_a init) ->
   ia m g (s_to_a (find_inv ab b init s i n)).
intros g ab n; induction n; simpl; intros init s b i ias iai.
case (is_inv ab (step2 ab b init s
                  (choose_1 s i)) b); simpl; auto.
apply step2_pc; simpl; auto.
case (is_inv ab (step2 ab b init s (choose_1 s i)) b).
apply step2_pc; auto.
apply IHn; auto; apply over_approx_sem1; auto.
Qed.

Lemma ab2_pc :
  forall  i i' s s', ab2 i s = (i', s') ->
    forall g a, ia m g (s_to_a s) -> ia m g (pc i' a).
induction i; simpl; intros i' s s' q g a is.
injection q; intros q' q''; subst s' i'; simpl; auto.
case_eq (ab2 i1 s); intros a_i1 [s1 | ] q1.
case_eq (ab2 i2 s1); intros a_i2 s2 q2.
rewrite q1, q2 in q; injection q; intros q' q''; subst s' i'; simpl.
apply (IHi1 a_i1 s (Some s1)); auto.
rewrite q1 in q; injection q; intros q' q''; subst s' i'; simpl.
apply (IHi1 a_i1 s None); auto.
injection q; intros _ di; subst i'; simpl; apply find_inv_pc; auto.
Qed.

Lemma vc_mark : forall i, valid m (vc (mark i) a_false).
induction i; simpl.

split; auto; intros g iaf; rewrite subst_a_false; exact iaf.
apply valid_app; auto.
assert (strong : forall g, ia m g a_false ->
         ia m g (pc (mark i2) a_false)).
simpl; intuition.
destruct (vc_monotonic m (mark i1) a_false _ strong); auto.
intuition.
Qed.

Lemma step1_consistent :
  forall ab b s s', 
    (forall s s' i, consistent s -> ab s = (i, Some s') -> consistent s') ->
    consistent s -> consistent s' -> consistent (step1 ab b s s').
intros ab b s s' cab cs cs'; unfold step1.
case_eq (learn_from_success s' b); [intros s1 ql | intros ql]; auto.
case (ab s1); intros _ [s2 | ]; unfold join_state'; auto; 
 apply join_state_consistent.
Qed.

Lemma step2_consistent :
  forall ab b s n s',
    (forall s s' i, consistent s -> ab s = (i, Some s') -> consistent s') ->
    consistent s -> consistent s' ->
    consistent (step2 ab b s s' n).
intros a b s n; induction n; simpl; intros s' cab cs cs'; auto.
apply IHn; auto; apply step1_consistent; auto.
Qed.

Hypothesis over_approx_consistent :
  forall n s s', consistent s -> consistent s' -> 
     consistent (over_approx n s s').


Lemma find_inv_consistent :
  forall ab b n init s i,
  (forall s s' i, consistent s -> ab s = (i, Some s') -> consistent s') ->
  consistent s -> consistent init ->
  consistent (find_inv ab b init s i n).
intros ab b n; induction n; simpl; intros init s i cab cs ci.
case (is_inv ab (step2 ab b init s (choose_1 s i))); auto.
apply step2_consistent; auto.
case (is_inv ab (step2 ab b init s (choose_1 s i)) b).
apply step2_consistent; auto.
apply IHn.
 exact cab.
 apply over_approx_consistent; auto ;apply step2_consistent; auto.
 auto.
Qed.

Hypothesis learn_from_success_consistent :
  forall s b s', consistent s ->
     learn_from_success s b = Some s' -> consistent s'.

Hypothesis learn_from_failure_consistent :
  forall s b s', consistent s ->
     learn_from_failure s b = Some s' -> consistent s'.

Lemma ab2_consistent :
  forall i s s' i', consistent s -> ab2 i s = (i', Some s') -> consistent s'.
induction i; simpl.
intros s s' i' cs q; injection q; simpl; intros;
  subst s';apply consistent_update; auto.
intros s s' i' cs; assert (IHi1' := IHi1 s); 
  destruct (ab2 i1 s) as [ i1' [s1' | ]].
assert (IHi2' := IHi2 s1'); destruct (ab2 i2 s1') as [i2' [s2' | ]].
intros q; injection q; intros; subst.
apply IHi2' with i2'; auto; apply IHi1' with i1'; auto.
intros; discriminate.
intros; discriminate.
intros s s' i' cs q; injection q; intros; subst.
case_eq (learn_from_failure (find_inv (ab2 i) b s s i (choose_2 s i)) b);
 [intros s2 ql | intros ql]; rewrite ql in q; try discriminate.
 injection q; intros; subst s';
 apply learn_from_failure_consistent with (2:=ql);
 apply find_inv_consistent; auto.
Qed.

Lemma mark_pc : forall i, pc (mark i) a_false = a_false.
induction i; simpl; auto.
rewrite IHi2; rewrite IHi1; auto.
Qed.

Lemma do_annot_pc :
  forall b g i a s,
   ia m g (s_to_a' (learn_from_success s b)) ->
   ia m g (pc (do_annot (ab2 i) b s i) a).
intros b g i a s; unfold do_annot; case (learn_from_success s b); simpl.
intros s' ias'; case_eq (ab2 i s'); intros s2 ai qab.
apply ab2_pc with (1:= qab); solve[auto].
intuition.
Qed.

Lemma s_stable_correct :
  forall g s s', s_stable s s' = true ->
    ia m g (s_to_a s') -> ia m g (s_to_a s).
intros g s s'; induction s.
simpl; auto.
destruct a as [x v]; simpl.
intros qst ias';
assert (qst' : thinner (lookup s' x) v = true /\ s_stable s s' = true).
destruct (thinner (lookup s' x) v); try discriminate.
destruct (s_stable s s'); discriminate || auto.
destruct qst' as [qst1 qst2].
simpl;split.
apply thinner_sem with (1:= qst1).
rewrite to_pred_sem; simpl; apply lookup_sem; auto.
apply IHs;auto.
Qed.

Lemma is_inv_correct :
   forall ab b g s s' s2 ai,
     is_inv ab s b = true -> learn_from_success s b = Some s' ->
     ab s' = (ai, s2) -> ia m g (s_to_a' s2) -> ia m g (s_to_a s).
unfold is_inv; intros ab b g s s' s2 ai.
intros st ql qab ias2.
unfold step1 in st; rewrite ql, qab in st.
apply s_stable_correct with (1:=st).
destruct s2 as [s2 | ]; simpl in ias2; unfold join_state'.
 apply join_state_safe_2; solve[auto].
contradiction.
Qed.

Lemma find_inv_correct :
  forall ab b g i n init s s' s2 ai,
     learn_from_success (find_inv ab b init s i n) b = Some s' ->
     ab s' = (ai, s2) -> ia m g (s_to_a' s2) ->
     ia m g (s_to_a (find_inv ab b init s i n)).
intros ab b g i n; induction n; intros init s s' s2 ai; simpl.
case_eq (is_inv ab (step2 ab b init s (choose_1 s i)) b);
intros qii ql qab ias2.
apply is_inv_correct with (1:=qii) (2:=ql)(3:=qab); solve[auto].
simpl; solve[auto].
case_eq (is_inv ab (step2 ab b init s (choose_1 s i)) b).
intros qii ql qab ias2.
apply is_inv_correct with (1:= qii)(2:=ql)(3:=qab); solve[auto].
intros _ ql qab ias2; apply IHn with (1:= ql)(2:=qab)(3:=ias2).
Qed.

Theorem ab2_correct : forall i i' s s', consistent s ->
  ab2 i s = (i', s') -> valid m (vc i' (s_to_a' s')).
induction i; simpl; intros i' s s' cs.
intros q; injection q; do 2 intro; subst; simpl; split; auto.
intros g ias; apply subst_consistent; auto.
apply a_af_sound; auto.

case_eq (ab2 i1 s); intros a_i1 [s1 | ] q1.
case_eq (ab2 i2 s1); intros a_i2 s2 q2.
intros q; injection q; clear q; intros s's2 i'seq; subst s' i'.
simpl; apply valid_app.
destruct (vc_monotonic m a_i1 (s_to_a s1) (pc a_i2 (s_to_a' s2))) as
 [vcm1 vcm2]; auto.
intros g ias1; apply ab2_pc with (1:=q2); solve[auto].
apply IHi1 with (2:= q1); solve[auto].
assert (consistent s1) by (apply ab2_consistent with (2:=q1); auto).
apply IHi2 with (2:= q2); solve[auto].
intros q; injection q; clear q; intros s's2 i'seq; subst s' i'.
simpl; apply valid_app.
rewrite mark_pc; apply IHi1 with (2:=q1); solve[auto].
apply vc_mark.

intros q; injection q; do 2 intro; subst i' s'.
simpl; split.
intros g [iaf gb]; apply do_annot_pc.
apply learn_from_success_sem; auto.
apply find_inv_consistent; auto; apply ab2_consistent.
split.
intros g [iaf ngb]; apply learn_from_failure_sem; auto.
apply find_inv_consistent; auto.
apply ab2_consistent;auto.
unfold do_annot.
case_eq (learn_from_success (find_inv (ab2 i) b s s i (choose_2 s i)) b).
 intros s' ql; case_eq (ab2 i s'); intros ai s2 qab.
 destruct (vc_monotonic m ai (s_to_a' s2)
   (s_to_a (find_inv (ab2 i) b s s i (choose_2 s i)))) as [vcm1 vcm2]; auto.
  intros g ias2; apply find_inv_correct with (1:=ql)(2:=qab)(3:=ias2).
 apply IHi with (2:=qab).
 apply learn_from_success_consistent with (2:=ql). 
 apply find_inv_consistent; auto.
 apply ab2_consistent.
intros ql; simpl.
assert (tmp: forall g, ia m g a_false ->
             ia m g (s_to_a (find_inv (ab2 i) b s s i (choose_2 s i)))).
simpl; intuition.
destruct (vc_monotonic m (mark i) a_false _ tmp); auto.
apply vc_mark.
Qed.

Lemma mark_clean : forall i, cleanup (mark i) = i.
induction i; simpl; auto.
 rewrite IHi1, IHi2; auto.
rewrite IHi; auto.
Qed.

Theorem ab2_clean : forall i i' s s',
   ab2 i s = (i', s') -> cleanup i' = i.
induction i; simpl; intros i' s s' q.
  injection q; intros; subst; simpl; auto.
 case_eq (ab2 i1 s); intros a_i1 [s1 | ] q1; rewrite q1 in q.
  case_eq (ab2 i2 s1); intros a_i2 s2 q2; rewrite q2 in q;
   injection q; intros; subst; simpl; auto; clear q;
   rewrite (IHi1 _ _ _ q1), (IHi2 _ _ _ q2); auto.
 injection q; intros; subst; simpl; auto; clear q;
  rewrite (IHi1 _ _ _ q1), mark_clean; auto.
injection q; intros; subst; unfold do_annot; simpl.
case (learn_from_success (find_inv (ab2 i) b s s i (choose_2 s i)) b).
 intros s'; case_eq (ab2 i s'); intros s'' ai q1.
 rewrite (IHi _ _ _ q1); auto.
rewrite mark_clean; auto.
Qed.

End absint.

Inductive interval : Type :=
  above : Z -> interval
| below : Z -> interval
| between : Z -> Z -> interval
| all_Z : interval.

Definition i_from_Z (x:Z) := between x x.

Definition i_add (x y:interval) :=
  match x, y with 
    above x, above y => above (x+y)
  | above x, between y z => above (x+y)
  | below x, below y => below (x+y)
  | below x, between y z => below (x+z)
  | between x y, above z => above (x+z)
  | between x y, below z => below (y+z)
  | between x y, between z t => between (x+z) (y+t)
  | _, _ => all_Z
  end.

Definition i_learn_from_success (s: list (string*interval)) (b:bexpr) :=
  match b with
    blt (avar name) e =>
      match a_af _ i_from_Z all_Z i_add s e, lookup _ all_Z s name with
        below n, below m => 
           Some (if Z_le_dec n m then a_upd _ name (below (n-1)) s else s)
      | below n, above m =>
           if Z_le_dec n m then None else
             Some (a_upd _ name (between m (n-1)) s)
      | below n, between m p =>
           if Z_le_dec n m then None else
             Some (a_upd _ name 
                   (if Z_le_dec (n-1) p then between m (n-1)
                    else between m p) s)
      | below n, all_Z => Some (a_upd _ name (below (n-1)) s)
      | between _ n, below m => 
           Some (if Z_le_dec n m then a_upd _ name (below (n-1)) s else s)
      | between _ n, above m =>
           if Z_le_dec n m then None
           else Some (a_upd _ name (between m (n-1)) s)
      | between _ n, between m p =>
           if Z_le_dec n m then None else
           if Z_le_dec n p then Some (a_upd _ name (between m (n-1)) s)
           else Some s
      | between _ n, all_Z => Some (a_upd _ name (below (n-1)) s)
      | _, _ => Some s
      end
   | _ => Some s
   end.

Definition i_learn_from_failure (s: list (string*interval)) (b:bexpr) :=
  match b with
    blt (avar name) e =>
      match a_af _ i_from_Z all_Z i_add s e, lookup _ all_Z s name with
        above x, below y => 
           if Z_le_dec x y then Some (a_upd _ name (between x y) s) else None
      | above x, above y =>
           if Z_le_dec x y then Some s
           else Some (a_upd _ name (above x) s)
      | above x, between y z =>
           if Z_lt_dec z x then None else
           if Z_le_dec x y then Some s
           else Some (a_upd _ name (between x z) s)
      | above x, all_Z => Some(a_upd _ name (above x) s)
      | between x _, below y => 
           if Z_le_dec x y then Some (a_upd _ name (between x y) s) else None
      | between x _, above y =>
           if Z_le_dec x y then Some s
           else Some (a_upd _ name (above x) s)
      | between x _, between y z =>
           if Z_lt_dec z x then None else
           if Z_le_dec x y then Some s
           else Some (a_upd _ name (between x z) s)
      | between x _, all_Z => Some (a_upd _ name (above x) s)
      | _, _ => Some s
      end
   | _ => Some s
   end.

Definition i_to_pred (x:interval) (e:aexpr) : assert :=
  match x with
    above a => pred "leq" (anum a::e::nil)
  | below a => pred "leq" (e::anum a::nil)
  | between a b => a_conj (pred "leq" (anum a::e::nil))
                      (pred "leq" (e::anum b::nil))
  | all_Z => a_true
  end.

Definition i_join (i1 i2:interval) : interval :=
  match i1, i2 with
    above x, above y =>
      if Z_le_dec x y then above x else above y
  | above x, between y _ =>
      if Z_le_dec x y then above x else above y
  | below x, below y =>
      if Z_le_dec x y then below y else below x
  | below x, between _ y =>
      if Z_le_dec x y then below y else below x
  | between x _, above y =>
      if Z_le_dec x y then above x else above y
  | between _ x, below y =>
      if Z_le_dec x y then below y else below x
  | between x y, between z t =>
      let lower := if Z_le_dec x z then x else z in
      let upper := if Z_le_dec y t then t else y in
      between lower upper
  | _, _ => all_Z
  end.

Definition i_thinner (i1 i2:interval) : bool :=
  match i1, i2 with
    above x, above y => if Z_le_dec y x then true else false
  | above _, all_Z => true
  | below x, below y => if Z_le_dec x y then true else false
  | below _, all_Z => true
  | between x y, between z t =>
    if Z_le_dec z x then if Z_le_dec y t then true else false else false
  | between x _, above y => if Z_le_dec y x then true else false
  | between _ x, below y => if Z_le_dec x y then true else false
  | _, all_Z => true
  | _, _ => false
  end.

Definition open_interval (i1 i2:interval) : interval :=
  match i1, i2 with
    below x, below y => if Z_le_dec y x then i1 else all_Z
  | above x, above y => if Z_le_dec x y then i1 else all_Z
  | between x y, between z t =>
    if Z_le_dec x z then if Z_le_dec t y then i1 else above x
    else if Z_le_dec t y then below y else all_Z
  | _, _ => all_Z
  end.

Definition open_intervals (s s':state interval) : state interval :=
  map (fun p:string*interval => 
         let (name, v) := p in 
           (name, open_interval v (lookup _ all_Z s' name))) s.

Definition i_over_approx n s s' :=
  match n with
    S _ => open_intervals s s'
  | _ => nil
  end.

Definition i_m (s : string) (l: list Z) : Prop :=
  if string_dec s "leq" then
    match l with x::y::nil => x <= y | _ => False end
  else False.
  
(* The properties *)

Lemma i_top_sem : forall e, i_to_pred all_Z e = a_true.
auto.
Qed.

Lemma i_to_pred_sem : forall g v e, ia i_m g (i_to_pred v e) =
   ia i_m g (i_to_pred v (anum (af g e))).
intros g v e; unfold i_to_pred; case v; simpl; auto.
Qed.

Lemma i_subst_to_pred : forall v x e e',
  subst x e' (i_to_pred v e) = i_to_pred v (asubst x e' e).
intros v; case v; simpl; auto.
Qed.

Lemma i_from_Z_sem : forall g x, ia i_m g (i_to_pred (i_from_Z x) (anum x)).
intros g x; unfold i_from_Z, i_to_pred, i_m; simpl; omega.
Qed.

Lemma i_add_sem : forall g v1 v2 x1 x2,
  ia i_m g (i_to_pred v1 (anum x1)) -> ia i_m g (i_to_pred v2 (anum x2)) ->
  ia i_m g (i_to_pred (i_add v1 v2) (anum (x1+x2))).
intros g [z1 | z1 | l1 u1 | ] [ z2 | z2 | l2 u2 | ];
  unfold i_m; simpl; intros; try solve [auto | omega].
Qed.


Lemma i_learn_from_success_sem :
 forall s b g, consistent _ s -> ia i_m g (s_to_a _ i_to_pred s) ->
      ia i_m g (a_b b) ->
      ia i_m g (s_to_a' _ i_to_pred (i_learn_from_success s b)).
Proof with
  (try solve [intros; discriminate | unfold i_m; simpl; omega |
          assert False by omega; contradiction |
          intro ; intros; rewrite i_to_pred_sem; simpl; apply lookup_sem;
          auto; exact i_to_pred_sem]).
intros s b g cs ias.
destruct b as [e1 e2].
destruct e1 as [ n | x | a1 a2]; try solve [simpl; auto].
unfold i_learn_from_success.
assert (te2 := a_af_sound _ _ _ _ _ _ i_top_sem i_to_pred_sem i_from_Z_sem
           i_add_sem _ _ e2 ias). 
case_eq (a_af interval i_from_Z all_Z i_add s e2); try solve [simpl; auto];
  ((intros z afz; rewrite afz in te2) ||
   (intros ze1 ze2 afz; rewrite afz in te2)); unfold i_m in te2; simpl in te2;
assert (tx:= lookup_sem _ _ _ i_m i_top_sem i_to_pred_sem _ _ ias x);
case_eq (lookup _ all_Z s x);
((intros z' lk; rewrite lk in tx) ||
 (intros z0 z1 lk; rewrite lk in tx) ||
 (intros lk; rewrite lk in tx)); unfold i_m in tx; simpl in tx;
 (simpl (ia i_m g (a_b (blt (avar x) e2))); destruct (Z_lt_dec (g x) (af g e2));
  try (intros; discriminate)). 
       intros _; destruct (Z_le_dec z z'); auto...
       simpl; apply a_upd_ia_all' with (top := all_Z); auto...
      intros _; destruct (Z_le_dec z z'); simpl; auto.
      simpl; apply a_upd_ia_all' with (top := all_Z); auto...
     intros _; destruct (Z_le_dec z z0); 
     destruct (Z_le_dec (z-1) z1); simpl; 
       try (apply a_upd_ia_all' with (top:= all_Z); auto)...
    intros _; unfold s_to_a';
       apply a_upd_ia_all' with (top:=all_Z);
       auto...
   intros _; destruct (Z_le_dec ze2 z'); simpl;
     try(apply a_upd_ia_all' with (top:=all_Z)); auto...
  intros _; destruct (Z_le_dec ze2 z'); simpl; auto;
  apply a_upd_ia_all' with (top:=all_Z);
     auto...
 intros _; destruct (Z_le_dec ze2 z0)...
 destruct (Z_le_dec ze2 z1); simpl; auto.
  apply a_upd_ia_all' with (top:=all_Z); auto...
intros _; simpl; apply a_upd_ia_all' with (top:=all_Z); auto...
Qed.

Lemma i_learn_from_failure_sem :
 forall s b g, consistent _ s -> ia i_m g (s_to_a _ i_to_pred s) ->
      ~ia i_m g (a_b b) ->
      ia i_m g (s_to_a' _ i_to_pred          (i_learn_from_failure s b)).
Proof with
  (try solve [intros; discriminate | unfold i_m; simpl; omega |
          assert False by omega; contradiction |
          intro ; intros; rewrite i_to_pred_sem; simpl; apply lookup_sem;
          auto; exact i_to_pred_sem]).
intros s b g cs ias.
destruct b as [e1 e2].
destruct e1 as [ n | x | a1 a2]; try solve [simpl; auto].
simpl; destruct (Z_lt_dec (g x) (af g e2)); try (solve[intros abs; case abs; auto]).
assert (te2 := a_af_sound _ _ _ _  _ _ i_top_sem i_to_pred_sem i_from_Z_sem
           i_add_sem _ _ e2 ias). 
intros _; case_eq (a_af _ i_from_Z all_Z i_add s e2).
   intros low qlow; rewrite qlow in te2; unfold i_m in te2; simpl in te2.
   case_eq (lookup _ all_Z s x).
      intros z' xeqz'; case (Z_le_dec low z'); simpl; auto.
      intros nlow; apply a_upd_ia_all' with (top:=all_Z); auto...
     intros z' xdeqz'.
     assert (xz:ia i_m g (i_to_pred (lookup _ all_Z s x)(anum (g x)))).
      apply lookup_sem; auto...
      solve[apply i_to_pred_sem].
     rewrite xdeqz' in xz; unfold i_m in xz; simpl in xz.
     case (Z_le_dec low z'); simpl.
      intros lowz; apply a_upd_ia_all' with (top:=all_Z); auto...
     intros nlowz; unfold i_m; simpl; omega.
    intros z z' xeqzz'; simpl.
    assert (xz:ia i_m g (i_to_pred (lookup _ all_Z s x)(anum (g x)))).
     apply lookup_sem; auto...
     solve[apply i_to_pred_sem].
    rewrite xeqzz' in xz; unfold i_m in xz; simpl in xz.
    case (Z_lt_dec z' low).
     intros zlow; unfold i_m; simpl; omega.
    intros lowz; case (Z_le_dec low z); auto.
    intros zlow; unfold s_to_a'; apply a_upd_ia_all' with (top:=all_Z); auto...
   intros _; unfold s_to_a'; apply a_upd_ia_all' with (top:=all_Z); auto...
  intros up qe2; rewrite qe2 in te2; unfold i_m in te2; simpl in te2.
  solve[auto].
 intros low high' qe2; rewrite qe2 in te2; unfold i_m in te2; simpl in te2.
 assert (px:ia i_m g (i_to_pred (lookup _ all_Z s x)(anum (g x)))).
  apply lookup_sem; auto...
 solve[apply i_to_pred_sem].
 case_eq (lookup _ all_Z s x).
    intros z xeqz; rewrite xeqz in px; unfold i_m in px; simpl in px.
    case (Z_le_dec low z); auto...
    intros zlow; unfold s_to_a'; apply a_upd_ia_all' with (top:=all_Z); auto...
   intros z xeqz; rewrite xeqz in px; unfold i_m in px; simpl in px.
   case (Z_le_dec low z).
    intros lowz; unfold s_to_a'; apply a_upd_ia_all' with (top:=all_Z); auto...
   intros...
  intros z z' xeqzz'; rewrite xeqzz' in px; unfold i_m in px; simpl in px.
  case (Z_lt_dec z' low).
   intros zlow...
  intros lowz'; case (Z_le_dec low z); auto...
  intros zlow;  unfold s_to_a'; apply a_upd_ia_all' with (top:=all_Z); auto...
 intros _; unfold s_to_a'; apply a_upd_ia_all' with (top:=all_Z); auto...
solve[auto].
Qed.

Lemma open_intervals_sem :
  forall g s s', ia i_m g (s_to_a _ i_to_pred s) ->
     ia i_m g (s_to_a _ i_to_pred (open_intervals s s')).
intros g s s'; induction s as [| [x v] s IHs]; simpl; auto.
intros [iax ias]; split; auto.
unfold open_interval; destruct v as [n | n | n1 n2 | ];
destruct (lookup _ all_Z s' x) as [n' | n' | n'1 n'2 | ]; try solve[simpl;auto].
  destruct (Z_le_dec n n'); simpl; solve[auto].
 destruct (Z_le_dec n' n); simpl; solve[auto].
destruct (Z_le_dec n1 n'1); destruct (Z_le_dec n'2 n2);
  unfold i_m in iax |- * ; simpl in iax |- * ; auto; omega.
Qed.

Lemma i_over_approx_sem1 :
  forall g n s s', ia i_m g (s_to_a _ i_to_pred s) ->
     ia i_m g (s_to_a _ i_to_pred (i_over_approx n s s')).
intros g n s s' ias; unfold i_over_approx; case n; simpl; auto.
intros _; apply open_intervals_sem; auto.
Qed.

Definition i_choose_1 (s:state interval) (i:instr) := 2%nat.
Definition i_choose_2 (s:state interval) (i:instr) := 3%nat.

Lemma i_join_thinner_1 :  forall a b, i_thinner a (i_join a b) = true.
intros [n | n | n1 n2| ] [n' | n' | n'1 n'2 | ]; unfold i_join, i_thinner; auto.
destruct (Z_le_dec n n').
destruct (Z_le_dec n n) as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n' n) as [_ | abs]; auto; case abs; omega.
destruct (Z_le_dec n n'1).
destruct (Z_le_dec n n) as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n'1 n) as [_ | abs]; auto; case abs; omega.
destruct (Z_le_dec n n').
destruct (Z_le_dec n n'); try contradiction; auto.
destruct (Z_le_dec n n) as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n n'2).
destruct (Z_le_dec n n'2); auto; contradiction.
destruct (Z_le_dec n n) as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n1 n').
destruct (Z_le_dec n1 n1) as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n' n1) as [_ | abs]; auto; case abs; omega.
destruct (Z_le_dec n2 n').
destruct (Z_le_dec n2 n') as [_ | abs]; auto; case abs; omega.
destruct (Z_le_dec n2 n2) as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n1 n'1).
destruct (Z_le_dec n1 n1) as [_ | abs]; auto; try solve[case abs; auto with zarith].
destruct (Z_le_dec n2 n'2).
destruct (Z_le_dec n2 n'2); auto; contradiction.
destruct (Z_le_dec n2 n2) as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n'1 n1).
destruct (Z_le_dec n2 n'2).
destruct (Z_le_dec n2 n'2); auto; contradiction.
destruct (Z_le_dec n2 n2) as [_ | abs]; auto; case abs; auto with zarith.
assert False by omega; contradiction.
Qed.

Lemma i_join_thinner_2 :  forall a b, i_thinner b (i_join a b) = true.
intros [n | n | n1 n2| ] [n' | n' | n'1 n'2 | ]; unfold i_join, i_thinner; auto.
destruct (Z_le_dec n n').
destruct (Z_le_dec n n') as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n' n') as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n n'1).
destruct (Z_le_dec n n'1) as [_ | abs]; auto; contradiction.
destruct (Z_le_dec n'1 n'1) as [_ | abs]; auto; case abs; omega.
destruct (Z_le_dec n n').
destruct (Z_le_dec n' n') as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n' n) as [_ | abs]; auto; case abs; omega.
destruct (Z_le_dec n n'2).
destruct (Z_le_dec n'2 n'2) as [_ | abs]; auto; case abs; omega.
destruct (Z_le_dec n'2 n) as [_ | abs]; auto; case abs; omega.
destruct (Z_le_dec n1 n').
destruct (Z_le_dec n1 n') as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n' n') as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n2 n').
destruct (Z_le_dec n' n') as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n' n2) as [_ | abs]; auto; case abs; omega.

destruct (Z_le_dec n1 n'1).
destruct (Z_le_dec n1 n'1); try contradiction.
destruct (Z_le_dec n2 n'2).
destruct (Z_le_dec n'2 n'2) as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n'2 n2) as [_ | abs]; auto; case abs; omega.
destruct (Z_le_dec n'1 n'1) as [_ | abs]; try solve[case abs; auto with zarith].
destruct (Z_le_dec n2 n'2).
destruct (Z_le_dec n'2 n'2) as [_ | abs]; auto; case abs; auto with zarith.
destruct (Z_le_dec n'2 n2); auto; assert False by omega; contradiction.
Qed.

Lemma i_thinner_sem : forall a1 a2, i_thinner a1 a2 = true ->
  forall g e, ia i_m g (i_to_pred a1 e) -> ia i_m g (i_to_pred a2 e).
intros i1 [n' | n' | n'1 n'2 | ];
  [idtac | idtac | idtac | simpl; solve[auto]];
 destruct i1 as [n | n | n1 n2 | ]; unfold i_m; match goal with
   |- context [Z_le_dec ?a ?b] => destruct (Z_le_dec a b)
 | _ => idtac
 end; simpl;  try (intros;discriminate);
 match goal with |- context [Z_le_dec ?a ?b] => destruct (Z_le_dec a b)
 | _ => idtac
 end; simpl; try solve [intros; discriminate | intros; omega].
destruct (Z_le_dec n2 n'2); intros; solve[discriminate | omega]. 
Qed.


Lemma i_over_approx_consistent :
  forall n s s', consistent _ s -> consistent _ s' -> 
    consistent _ (i_over_approx n s s').
intros n; destruct n; try solve[unfold consistent; simpl; auto].
simpl.
unfold consistent; intros s s' nds nds'; generalize (@nil string) nds;
 clear nds nds'.
 induction s as [ | [x v] s IHs]; simpl; auto.
intros l ndsx; assert (nds : no_dups _ s (x::l) = true).
destruct (no_dups _ s (x::l)); try (simpl; intros; discriminate); auto.
destruct (mem x l); auto.
 destruct (mem x l); solve[discriminate | auto].
Qed.

Lemma i_learn_from_success_consistent :
forall s b s',
        consistent interval s ->
        i_learn_from_success s b = Some s' -> consistent interval s'.
Proof with
  try (solve[intros q; injection q; intro; subst; assumption
            | intros; discriminate | 
              intro q; injection q; intro; 
               subst; apply consistent_update; auto]).
intros s [[n | x | e1' e2'] e2] s' cs; simpl...
destruct (a_af _ i_from_Z all_Z i_add s e2) as [low | high | low high | ]...
 destruct (lookup _ all_Z s x) as [ z | z | z z' | ]...
    case (Z_le_dec high z); intros _ ...
   case (Z_le_dec high z); intros _...
  case (Z_le_dec high z); intro...
destruct (lookup _ all_Z s x) as [ z | z | z z' | ]...
  case (Z_le_dec high z); intros _...
 case (Z_le_dec high z); intros _...
case (Z_le_dec high z); intro...
case (Z_le_dec high z'); intro...
Qed. 

Lemma i_learn_from_failure_consistent :
forall s b s',
        consistent interval s ->
        i_learn_from_failure s b = Some s' -> consistent interval s'.
Proof with
  try (solve[intros q; injection q; intro; subst; assumption
            | intros; discriminate | 
              intro q; injection q; intro; 
               subst; apply consistent_update; auto]).
intros s [[n | x | e1' e2'] e2] s' cs; simpl...
destruct (a_af _ i_from_Z all_Z i_add s e2) as [low | high | low high | ]...
 destruct (lookup _ all_Z s x) as [ z | z | z z' | ]...
   case (Z_le_dec low z); intro ...
  case (Z_le_dec low z); intro ...
 case (Z_lt_dec z' low); intro...
 case (Z_le_dec low z); intro...
destruct (lookup _ all_Z s x) as [ z | z | z z' | ]...
  case (Z_le_dec low z); intro ...
 case (Z_le_dec low z); intro ...
case (Z_lt_dec z' low); intro...
case (Z_le_dec low z); intro...
Qed. 

Definition abi :=
 ab2 interval i_from_Z all_Z i_add i_to_pred 
   i_learn_from_success i_learn_from_failure
   i_join i_thinner i_over_approx i_choose_1 i_choose_2.

Lemma abi_correct : forall i i' s s', consistent _ s ->
  abi i s = (i', s') ->  valid i_m (vc i' (s_to_a' _ i_to_pred s')).
exact (ab2_correct _ _ _ _ _ _ i_top_sem  
  i_to_pred_sem i_subst_to_pred i_from_Z_sem
  i_add_sem _ _ _ _ _ i_choose_1 i_choose_2 i_learn_from_success_sem
  i_learn_from_failure_sem 
  i_over_approx_sem1 i_join_thinner_1 i_join_thinner_2 i_thinner_sem
  i_over_approx_consistent i_learn_from_success_consistent
  i_learn_from_failure_consistent).
Qed.

Open Scope string_scope.
Definition i1 :=
  while (blt (avar "x") (anum 10)) (assign "x" (aplus (avar "x") (anum 1))).
Definition i2 := assign "x" (aplus (avar "x") (anum 1)).
Definition b1 := blt (avar "x") (anum 10).

Eval vm_compute in abi i1 (("x", between 0 0)::nil).

Definition i3 := 
  while (blt (avar "x")(anum 10))
     (seq (while (blt (avar "y")(avar "x"))
          (assign "y" (aplus (avar "y") (anum 1))))
      (seq (assign "y" (anum 0)) i2)).

Eval vm_compute in abi i3 (("x", i_from_Z 0)::("y",i_from_Z 0)::nil).

(* Starting another instantiation: even and odd. *)

Inductive oe : Type := even | odd | oe_top.

Definition oe_from_Z (n:Z) : oe :=
  if Z_eq_dec (Zmod n 2) 0 then even else odd.

Definition oe_add (v1 v2:oe) : oe :=
  match v1,v2 with
    odd, odd => even
  | even, even => even
  | odd, even => odd
  | even, odd => odd
  | _, _ => oe_top
  end.

Definition oe_to_pred (v:oe)(e:aexpr) : assert :=
  match v with
    even => pred "even" (e::nil)
  | odd => pred "odd" (e::nil)
  | oe_top => a_true
  end.

Definition ab1oe := ab1 oe oe_from_Z oe_top oe_add oe_to_pred.

Eval vm_compute in ab1oe (seq (assign "x" (aplus (avar "x") (avar "y")))
                            (assign "y" (aplus (avar "y") (anum 1))) )
  (("x",even)::("y",odd)::nil).

(* 
*** Local Variables: ***
*** coq-prog-name: "~/exp/coq-8.2beta4/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)