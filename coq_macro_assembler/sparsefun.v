Require Import List.

(* If n>=m return difference otherwise return None *)
Fixpoint diff n m := 
  match n, m with
  | _, O     => Some n
  | S n, S m => diff n m
  | O, m     => None
  end.

Lemma diffZeroImpliesEqual x : forall y, diff x y = Some 0 -> x=y.
Proof. induction x. destruct y. auto. simpl. intros. inversion H.  
intros y. destruct y.  simpl.  intros. inversion H. 
simpl. auto. 
Qed. 

Lemma diffWithZero : forall d, diff d 0 = Some d. intros. destruct d; auto. Qed. 

Lemma diffDiff : forall c a b d e, diff a c = Some d -> diff b c = Some e -> a<>b -> d<>e.
Proof.  induction c. 
intros. 
(* c = 0 *) rewrite diffWithZero in H. rewrite diffWithZero in H0. congruence. 
(* c <> 0 *) intros.
destruct a. destruct b. congruence. 
simpl in H. congruence. 
destruct b. inversion H0. 
simpl in H0. apply (IHc _ _ _ _ H H0);  intuition. 
Qed. 

Lemma diffSame : forall c, diff c c = Some 0.
Proof. induction c; auto. Qed.

(* Sparse functions from nat to A, finite domain *) 
Definition SFun A := list (nat*A).

(* The empty map *)
Definition empty {A}: SFun A := nil.

(* Lookup *)
Fixpoint get {A} (f: SFun A) (x: nat) : option A :=
  match f with
  | nil => None
  | (gap,val)::f' => 
    match diff x gap with
    | None        => None
    | Some O      => Some val
    | Some (S x') => get f' x'
    end
  end.

(* Update; return function unchanged if l is not in its domain *)
Fixpoint put {A} (f: SFun A) (l: nat) (newval: A) : SFun A :=
  match f with
  | nil => nil
  | (oldgap,oldval)::f' => 
    match diff l oldgap with
    | None         => f
    | Some O      => (oldgap,newval)::f'
    | Some (S l') => (oldgap,oldval)::put f' l' newval
    end
  end.

Notation "f [ l := v ]" := (put f l v) (at level 1, left associativity, l at level 40). 

(* Allocate: use first available location *)
Fixpoint alloc {A} (f: SFun A) (val: A) : SFun A * nat :=
  match f with
  | nil => ((0,val)::nil,0)
  | (O,val')::f' => let (f'',loc) := alloc f' val in ((O,val')::f'',S loc)
  | (S gap,val')::f' => ((O,val)::(gap,val')::f', O)
  end.

(* Identify get with function application *)
Coercion get : SFun >-> Funclass.

Definition disjoint {A} (f g: SFun A) := forall x, f x = None \/ g x = None.
Notation "f # g" := (disjoint f g) (at level 70). 

Definition dom {A} (f: SFun A) : nat -> Prop := fun x => f x <> None.
Definition sub {A} (f g: SFun A) := forall l x, f l = Some x -> g l = Some x.
Definition equiv {A} (f g: SFun A) := forall x, f x = g x. 
Definition equivExcept {A} loc (f g: SFun A) := forall x, x<>loc -> f x = g x.

Lemma nonEmpty {A} gapval (f: SFun A) : exists y,  exists z, get ((gapval::f)) y = Some z.
Proof. 
destruct gapval as [gap val]. 
induction gap. 
exists 0. simpl. exists val. reflexivity. 
destruct IHgap as [y H]. 
destruct H as [z H]. 
exists (S y). exists z. auto.
Qed. 

Lemma emptyness {A} (f: SFun A) : (forall x, f x = None) <-> f = nil.
Proof. split. induction f. auto. 
intros H.
destruct (nonEmpty a f) as [y [z H0]].
congruence.
intros EQ x. subst. intuition.  
Qed. 

Lemma getSucc {A} gap val (f: SFun A) x : get ((S gap, val) :: f) (S x) = get ((gap, val)::f) x. 
Proof. 
induction gap; destruct x; auto. 
Qed. 


Lemma extAux {A} gap : 
  forall val gap' val' (f f': SFun A), (forall x, get ((gap,val)::f) x = get ((gap',val')::f') x) -> 
  gap = gap' /\ val = val' /\ equiv f f'. 
Proof. induction gap.
(* gap = 0 *)
intros. destruct gap'. 
split; auto. 
split. specialize (H 0). inversion H. auto. 
intros x. specialize (H (S x)). auto.  
specialize (H 0). 
inversion H. 

(* gap <> 0 *)
intros. 
destruct gap'. specialize (H 0). inversion H.  
assert (gap = gap' /\ val = val' /\ equiv f f'). 
apply IHgap.
intros x. specialize (H (S x)). rewrite 2 getSucc in H. auto. intuition. 
Qed. 

(* Extensionality *)
Lemma ext {A} : forall (g f: SFun A),  equiv f g -> f = g.
induction g.
(* g is nil *) intros f H. apply (proj1 (emptyness _) H). 
(* g is not nil *)
intros f H.
destruct f.
(* f is nil *)
destruct (nonEmpty a g) as [x' [z H']]. 
specialize (H x'). rewrite H' in H. 
rewrite ((proj2 (emptyness nil) (refl_equal _))) in H. inversion H. 
(* f is not nil *)
destruct a as [gap val]. 
destruct p as [gap' val'].
destruct (extAux _ _ _ _ _ _ H) as [H1 [H2 H3]]. rewrite H1. rewrite H2. rewrite (IHg f). 
auto. auto. 
Qed. 

Lemma allocSpec {A} (f: SFun A) (val: A) : 
  forall f' loc, 
  alloc f val = (f',loc) -> 
  equivExcept loc f f' /\ 
  f' loc = Some val /\
  f  loc = None.
Proof. 
induction f.
(* f = nil *) 
intros.
inversion H. subst. simpl. split.  
unfold equivExcept. intros l NEQ. destruct l; intuition. 
auto. 
(* f <> nil *)
intros. destruct a as [gap val'].  
simpl in H. 
destruct gap.
(* gap = 0 *)
destruct (alloc f val).
inversion H.  
subst. 
 specialize (IHf s n (refl_equal _)). destruct IHf. split.
unfold equivExcept.   
intros. destruct x. auto. unfold equivExcept in H0. assert (x <> n) by intuition. specialize (H0 _ H3). auto.  
auto. 
(* gap <> 0 *)
destruct (alloc f val).
inversion H.  
subst. 
split. 
unfold equivExcept.
intros x NEQ. destruct x. intuition. auto.  
auto. 
Qed. 


(* All that we need to know about update *)
Lemma putSpec {A} (f: SFun A) : 
  forall l v, 
  equivExcept l f[l:=v] f /\ 
  (dom f l -> f[l:=v] l = Some v).
Proof. 
induction f.
(* f = nil *) 
intros. unfold equivExcept. split.  intuition. simpl. intros. 
unfold dom in H. simpl in H. intuition. 
(* f <> nil *)
intros l v. destruct a as [gap val']. 

case_eq (diff l gap). 
(* loc >= gap, so we will use induction hypothesis if loc > gap *)
intros d deq. simpl.  
rewrite deq. destruct d. 
(* d = 0, so we're updating the first cons cell *)
assert (D0 := diffZeroImpliesEqual _ _ deq). subst. unfold equivExcept.

split. intros x neq.  
simpl. case_eq (diff x gap). intros y yeq. destruct y. 
assert (D1 := diffZeroImpliesEqual _ _ yeq). intuition. auto. auto. 
simpl. rewrite diffSame. auto. 
(* d <> 0, so we're beyond the first cons cell *)
unfold equivExcept. 
split. intros x neq. 
simpl. 
case_eq (diff x gap). intros y yeq. destruct y. auto. 
apply IHf. assert (DD := diffDiff _ _ _ _ _ yeq deq neq). intuition. 
auto.
simpl.  
rewrite deq. unfold dom. simpl.  rewrite deq. apply IHf. 
(* loc < gap *)
intros neq. 
unfold equivExcept. 
split. intros x xneq. simpl. rewrite neq. auto.
simpl.
unfold dom.    
rewrite neq. simpl. rewrite neq. intros. intuition. 
Qed. 

(* Update then lookup from same location *)
Corollary putGetSame {A} (f: SFun A) l v : 
  dom f l -> f[l:=v] l = Some v. 
Proof. 
intros D. 
apply (proj2 (putSpec _ _ v) D). 
Qed. 

(* Update then lookup from different location *)
Corollary putGetDistinct {A} (f: SFun A) l l' v : 
  dom f l -> l'<>l -> f[l:=v] l' = f l'. 
Proof.
intros D NEQ. 
assert (PS := putSpec f l v). 
destruct PS as [PS1 PS2]. 
unfold equivExcept in PS1. 
specialize (PS1 l'). 
intuition. 
Qed.

(* Allocate then lookup *)
Corollary allocGet {A} (f: SFun A) v f' l : 
  alloc f v = (f',l) -> f' l = Some v.
Proof. 
intros EQ. 
assert (AS := allocSpec f v f'  l). 
intuition. 
Qed. 

(* Allocate then lookup different location *)
Corollary allocGetDistinct {A} (f: SFun A) v f' l l' : 
  alloc f v = (f',l) -> l'<>l -> f' l' = f l'.
Proof.
intros EQ NEQ. 
assert (AS := allocSpec f v f' l EQ). 
destruct AS as [AS1 AS2]. unfold equivExcept in AS1. specialize (AS1 l' NEQ). intuition. 
Qed. 

(* Allocated location is not in original domain *)
Corollary allocFresh {A} (f: SFun A) v f' l : 
  alloc f v = (f',l) -> ~ dom f l.
intros EQ.
assert (AS := allocSpec f v f'  l EQ). 
destruct AS as [AS1 AS2].
intuition. 
Qed. 

(* Excluded middle for equality on naturals. Isn't this built in? *)
Lemma exclMiddleNat : forall x y:nat, x=y \/ x<>y.
Proof. induction x. destruct y; auto. 
intros. destruct (IHx y). subst. right. auto. 
induction y. auto. destruct (IHx y). subst. auto. right. auto. 
Qed. 

Lemma putPreservesDom {A} (f: SFun A) l l' v : dom f l -> dom f[l':=v] l.
Proof.
intros D. 
destruct (exclMiddleNat l l'). 
subst. 
destruct (putSpec f l' v) as [PS1 PS2].
specialize (PS2 D).
unfold dom.
rewrite PS2. discriminate.   
destruct (putSpec f l' v) as [PS1 PS2].
unfold equivExcept in PS1. 
specialize (PS1 l H). 
unfold dom. rewrite PS1. 
intuition. 
Qed. 
 
(* Update the same location *)
Corollary putPutSame {A} (f: SFun A) l v v' : dom f l -> 
  (f[l:=v])[l:=v'] = f[l:=v'].
Proof. intros D.
apply ext. 
unfold equiv. 
intros x. 
assert (D' : dom f[l:=v] l) by (apply putPreservesDom; auto). 
destruct (exclMiddleNat x l). 
subst. 
rewrite putGetSame by auto. 
rewrite putGetSame by auto. 
reflexivity. 

rewrite putGetDistinct by auto. 
rewrite putGetDistinct by auto. 
rewrite putGetDistinct by auto. 
reflexivity. 
Qed. 

(* Update different locations *)
Corollary putPutDistinct {A} (f: SFun A) l l' v v' : dom f l -> dom f l' -> l<>l' ->
  f[l:=v][l':=v'] = f[l':=v'][l:=v].
Proof. intros D D' NEQ. 
apply ext. 
unfold equiv. 
intros x. 
assert (D'' : dom f[l:=v] l') by (apply putPreservesDom; auto). 
assert (D''' : dom f[l':=v'] l) by (apply putPreservesDom; auto). 

destruct (exclMiddleNat x l). 
subst. 
rewrite putGetDistinct by auto. 
rewrite 2 putGetSame by auto. 
reflexivity. 

destruct (exclMiddleNat x l'). 
subst. 
rewrite putGetSame by auto. 
rewrite putGetDistinct by auto. 
rewrite putGetSame by auto. 
reflexivity. 

rewrite 4 putGetDistinct by auto. 
reflexivity. 
Qed. 

Inductive SplitsAs {A} : SFun A -> SFun A -> SFun A -> Prop :=
| SplitsAsLeftNil : forall f, SplitsAs f nil f
| SplitsAsSwap    : forall f f1 f2, SplitsAs f f1 f2 -> SplitsAs f f2 f1
| SplitsAsLeftZ   : 
  forall f f1 f2 gap v v', 
  SplitsAs f f1 ((gap,v')::f2) ->
  SplitsAs ((O,v)::f) ((O,v)::f1) ((S gap,v')::f2)
| SplitsAsLeftS   : 
  forall f f1 f2 gap gap' v v', 
  SplitsAs ((gap,v)::f) ((gap,v)::f1) ((gap',v')::f2) ->
  SplitsAs ((S gap,v)::f) ((S gap,v)::f1) ((S gap',v')::f2).

Notation "f 'is' g ++ h" := (SplitsAs f g h) (at level 60, g at next level, h at next level). 

Lemma SplitsAsDisjoint {A} (f f1 f2: SFun A) : 
  f is f1 ++ f2 -> f1 # f2.
Proof. intros SA. unfold disjoint. induction SA.

intros x. auto. 

intros x. destruct (IHSA x); auto. 

intros x. simpl.
destruct x. simpl. auto. 
simpl. specialize (IHSA x). intuition. 

intros x. simpl. 
destruct x. auto. simpl. specialize (IHSA x). simpl in IHSA. auto. 
Qed. 

Lemma SplitsAsUnion {A} (f f1 f2: SFun A) : 
  f is f1 ++ f2 -> forall x, f x = f1 x \/ f x = f2 x.
Proof. intros SA. induction SA. 

intros x. auto. 

intros x. destruct (IHSA x); auto. 

intros x. simpl.
destruct x. auto. 
simpl. specialize (IHSA x). intuition. 

intros x. simpl. 
destruct x. auto. simpl. specialize (IHSA x). simpl in IHSA. auto. 
Qed. 

Fixpoint fromFunAux {A} n start (g: nat -> option A) :SFun A :=
  match n with
  | O => nil
  | S n' =>
    match g start, fromFunAux n' (S start) g with
    | Some v, l => (0,v)::l
    | None, nil => nil
    | None, (gap,v)::l => (S gap,v)::l
    end
  end.

Definition fromFun {A} n (g: nat -> option A) := fromFunAux n 0 g.

Require Import Omega. 
Lemma fromFunAuxCorrect {A} n : 
  forall start (g: nat -> option A), 
  forall x, (x < n -> fromFunAux n start g x = g (start+x))
         /\ (x >= n -> fromFunAux n start g x = None).
Proof.
induction n. 
(* n = 0 *)
intros start g x. 
split. 
intros lt.
inversion lt. 
auto. 
(* n <> 0 *)
intros start g x.
simpl. 
case_eq (g start). 
(* g start = Some a *)
intros a aeq. 
simpl. 

case_eq (diff x 0). 
(* diff x 0 = Some _ *)
intros c ceq.
rewrite (diffWithZero x) in ceq. 
inversion ceq. subst. 
destruct c.
replace (start+0) with start by auto. split. congruence. intros. inversion H.  
specialize (IHn (S start) g c). destruct IHn as [IHn1 IHn2]. 
split. 
intros scn. assert (cn: c<n) by intuition. 
replace (start + S c) with (S start + c) by omega. 
apply IHn1; auto. 
intros scn. assert (cn: c >= n) by intuition. 
apply IHn2; auto.  
(* diff x 0 = None *)
intros ceq.
destruct x; inversion ceq. 

(* g start = None *)
intros geq. 
case_eq (fromFunAux n (S start) g). 
(* nil *)
intros H. 
destruct x.
(* x = 0 *) 
simpl. replace (start + 0) with start by auto. auto. 
(* x <> 0 *)
simpl. 
specialize (IHn (S start) g x).  destruct IHn as [IHn1 IHn2].
split.
intros sxn. assert (xn: x<n) by intuition.
specialize (IHn1 xn). 
rewrite H in IHn1. simpl in IHn1. replace (start + S x) with (S (start + x)) by auto. 
assumption. 
auto.  
intros. destruct p as [gap v]. 
destruct x. 
(* x = 0 *)
simpl. rewrite <- geq. auto. 
(* x <> 0 *)
rewrite getSucc.
specialize (IHn (S start) g x). destruct IHn as [IHn1 IHn2]. 
simpl. 
replace (start + S x) with (S (start + x))  by auto. 
rewrite H in IHn1. rewrite H in IHn2. 
split. intros sxn. assert (xn: x<n) by intuition.
specialize (IHn1 xn). 
assumption.
intros sxn.  assert (xn: x>=n) by intuition.
specialize (IHn2 xn). simpl in IHn2.  auto. 
Qed. 

Lemma fromFunCorrect {A} (g: nat -> option A) n : 
  (forall x, x >= n -> g x = None) -> forall x, fromFun n g x = g x.
Proof.
intros H x.
unfold fromFun.
assert (FF := fromFunAuxCorrect n 0 g x). destruct FF as [FF1 FF2]. 
destruct (Compare_dec.ge_dec x n).  
specialize (H _ g0). rewrite H. 
intuition. 
assert (xn: x < n) by omega.   
apply fromFunAuxCorrect; auto.  
Qed.
