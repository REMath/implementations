(*===========================================================================
    Reader monad, with instances for BYTE and DWORD
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool finfun fintype ssrnat eqtype seq tuple.
Require Import bitsrep bitsops bitsopsprops pmap cursor monad mem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
   We define a type of "readers of T", such that

   read m p = readerFail if memory at p in m is inaccessible for reading T
   read m p = readerWrap if we tried to read beyond the end of memory
   read m p = readerOk x q if memory between p inclusive and q exclusive represents x:X
  ---------------------------------------------------------------------------*)
CoInductive readerResult T := 
  readerOk (x: T) (q: Cursor 32) | readerWrap | readerFail. 
Definition reader T := Mem -> Cursor 32 -> readerResult T. 
Implicit Arguments readerOk [T]. 
Implicit Arguments readerWrap [T].
Implicit Arguments readerFail [T].

(* When reading from p a good reader produces a pointer q >= p and is oblivious to
   updates outside the range p inclusive to q exclusive *)
Definition goodReader T (read: Mem -> Cursor _ -> readerResult T) :=
    forall m pos,
      if read m pos is readerOk v pos' then
        leCursor pos pos' /\
        forall m':PMAP BYTE _, (forall p':BITS _, inRange pos pos' p' -> m p' = m' p') ->
        read m' pos = readerOk v pos'
      else True.

(* Package a reader together with a proof of goodness *)
Structure Reader T   := mkReader     {op; _: @goodReader T op}.
Structure readerType := mkReaderType {sort; getReader: Reader sort}. 
Coercion op : Reader >-> Funclass.
Coercion sort : readerType >-> Sortclass.

Definition read T := @getReader T. 
Implicit Arguments read [T]. 

Lemma readP T : goodReader (@read T).
Proof. destruct T as [T R]; by destruct R. Qed.

Lemma splitReaderOk {X} (a b:X) c d : readerOk a c = readerOk b d -> a = b /\ c = d.
Proof. move => H. by inversion H. Qed.

Lemma read_leCursor {R: readerType} m p q (v: R):
  read m p = readerOk v q -> leCursor p q.
Proof.
  move=> Hok. have Hgood := readP R m p. rewrite Hok in Hgood. tauto.
Qed.

(*---------------------------------------------------------------------------
   BYTE reader
  ---------------------------------------------------------------------------*)
Definition readBYTE_op : reader BYTE := 
  fun m pos => 
  if pos is mkCursor p 
  then if m p is Some x then readerOk x (next p) else readerFail
  else readerWrap.

Lemma readBYTE_good : goodReader readBYTE_op. 
Proof. move => m pos. rewrite /readBYTE_op. 
case E1: pos => [p |]; last done. 
case E2:(m p) => [b |]; last done. 
split; first apply leNext.
move => m' H'. rewrite /readBYTE_op -(H' p). 
by rewrite E2. by rewrite /inRange leCursor_refl ltNext. 
Qed. 

Canonical Structure readBYTE := mkReader readBYTE_good.  
Canonical Structure BYTE_readerType := Eval hnf in mkReaderType readBYTE.

Lemma readBYTE_next m (p:BITS _) b q : readBYTE m p = readerOk b q -> q = next p. 
Proof. rewrite /readBYTE/=. case (m p) => [b' |]; last done. congruence. Qed.

(*---------------------------------------------------------------------------
   Cursor reader
  ---------------------------------------------------------------------------*)
Definition getCursor_op : reader DWORD := 
  fun m pos => 
  if pos is mkCursor p 
  then readerOk p p 
  else readerFail.

Lemma getCursor_good : goodReader getCursor_op. 
Proof. move => m pos. rewrite /getCursor_op. 
case E1: pos => [p |]; last done. 
split; first apply leCursor_refl. 
done. 
Qed. 

Definition getCursor := mkReader getCursor_good.  

(*---------------------------------------------------------------------------
   Reader monad
  ---------------------------------------------------------------------------*)
Definition unitRead_op X (x:X) : reader X := 
  fun m pos => readerOk x pos.

Definition bindRead_op T U (r: reader T) (f: T -> reader U) : reader U :=
  fun m pos => match r m pos with 
              | readerOk x pos' => f x m pos'
              | readerFail => readerFail
              | readerWrap => readerWrap
              end.

Lemma unitRead_good X (x:X) : goodReader (unitRead_op x).  
Proof. move => m p. rewrite /unitRead_op. split; last done. by apply leCursor_refl. Qed.

Canonical Structure unitRead X (x:X) := mkReader (@unitRead_good _ x). 

Lemma bindRead_good T U (r: Reader T) (f: T -> Reader U) 
  : goodReader (bindRead_op (op r) (fun x => op (f x))).  
Proof. move => m p. rewrite /bindRead_op.  
assert (GR1: goodReader r) by by destruct r.
case E1: (op r m p) => [x q | |]; last done; last done. 

(* r m p = readerOk _ *)
assert (GR2: goodReader (f x)) by by destruct (f x). 
specialize (GR1 m p). rewrite E1 in GR1. destruct GR1 as [GR1a GR1b]. 
case E2: (op (f x) m q) => [y q' | |]; last done; last done. 
(* (f x) m q = readerOk _ *)
specialize (GR2 m q). rewrite E2 in GR2. destruct GR2 as [GR2a GR2b]. 
split; first apply: leCursor_trans GR1a  GR2a. 

move => m' H'. 
rewrite GR1b. rewrite GR2b. 

done. 

rewrite /inRange. move => p' RA. rewrite H'. done. rewrite /inRange. 
destruct (andP RA) as [qp' p'q']. by rewrite (leCursor_trans GR1a qp'). 
move => p' RA. destruct (andP RA) as [pp' p'q]. rewrite H'. done. 
rewrite /inRange. by rewrite (ltCursor_leCursor_trans p'q GR2a) pp'. 
Qed.  

Canonical Structure bindRead T U r f := mkReader (@bindRead_good T U r f). 

Require Import FunctionalExtensionality. 
Require Import ProofIrrelevance. 

Lemma readerMixin_extensional T (r1 r2: Reader T) :
  (forall m, op r1 m = op r2 m) -> r1 = r2.
Proof. move => H. 
assert (HH := functional_extensionality _ _ H).
destruct r1 as [op1 ax1]. destruct r2 as [op2 ax2].
simpl in HH. subst. by rewrite (proof_irrelevance _ ax1 ax2). 
Qed. 

Implicit Arguments read [T].

Instance readerMonadOps : MonadOps Reader :=
{ retn := unitRead ; bind := bindRead }.

Instance readerMonad : @Monad Reader readerMonadOps.
Proof. apply Build_Monad. 

move => X Y x f.
apply readerMixin_extensional => m. rewrite /bind /= /bindRead_op /unitRead_op. by apply functional_extensionality.  

move => X c. 
apply readerMixin_extensional => m. rewrite /=/bindRead_op. apply functional_extensionality => p. by case (c m p).

move => X Y Z c f g. 
apply readerMixin_extensional => m. rewrite /=/bindRead_op. apply functional_extensionality => p. by case (c m p).  
Qed.


Lemma bindGetCursor {Y} s (f: _ -> Reader Y) p: 
  bind getCursor f s (mkCursor p) = f p s p.
Proof. done. Qed. 

Lemma bindGetCursorBad {Y} s (f: _ -> Reader Y):
  bind getCursor f s (hwm _) = readerFail. 
Proof. done. Qed. 

Require Import update. Open Scope update_scope.
Lemma bindReadUpdate {Y} (m:Mem) (p:DWORD) (v:BYTE) (f:BYTE -> Reader Y) : 
  bind readBYTE f (m!p:=v) p = f v (m!p:=v) (next p). 
Proof. simpl. rewrite /bindRead_op/readBYTE_op. Require Import pmapprops.
rewrite updateThenLookup. done. 
Qed. 

(*---------------------------------------------------------------------------
   DWORD reader
  ---------------------------------------------------------------------------*)
Canonical Structure readDWORD :=
  let! b0 = read;
  let! b1 = read;
  let! b2 = read;
  let! b3 = read;
  retn (bytesToDWORD b3 b2 b1 b0).
Canonical Structure DWORD_readerType := Eval hnf in mkReaderType readDWORD. 

Canonical Structure readWORD :=
  let! b0 = read;
  let! b1 = read;
  retn (bytesToWORD b1 b0).
Canonical Structure WORD_readerType := Eval hnf in mkReaderType readWORD. 


Lemma readDWORD_next m (p:BITS _) v (q:BITS _) : 
  readDWORD m p = readerOk v q -> q = p +#4.
Proof. move => H. rewrite /readDWORD/readBYTE_op/read/=/bindRead_op/=/readBYTE_op in H. 
case E0: (m p) => [b0 |]; rewrite E0 in H; last done. 
case E0': (next p) => [p1 |]; rewrite E0' in H; last done. 
case E1: (m p1) => [b1 |]; rewrite E1 in H; last done. 
case E1': (next p1) => [p2 |]; rewrite E1' in H; last done.
case E2: (m p2) => [b2 |]; rewrite E2 in H; last done.
case E2': (next p2) => [p3 |]; rewrite E2' in H; last done. 
case E3: (m p3) => [b3 |]; rewrite E3 in H; last done. 
case E3': (next p3) => [p4 |]; rewrite E3' in H; last done. 
rewrite /next in E0', E1', E2', E3'. 
destruct (p == ones _); first discriminate E0'. 
destruct (p1 == ones _); first discriminate E1'. 
destruct (p2 == ones _); first discriminate E2'. 
destruct (p3 == ones _); first discriminate E3'.
rewrite /unitRead_op in H.
replace q with p4 by congruence. 
replace p4 with (incB p3) by congruence.
replace p3 with (incB p2) by congruence.
replace p2 with (incB p1) by congruence.
replace p1 with (incB p) by congruence.
by rewrite addIsIterInc. 
Qed. 
 
Definition readDWORDorBYTE (dword:bool) :=
  if dword as dword return Reader (DWORDorBYTE dword) then readDWORD else readBYTE.

Canonical Structure DWORDorBYTE_readerType (dword:bool) := 
  mkReaderType (readDWORDorBYTE dword).

(*---------------------------------------------------------------------------
   Reading pairs   
  ---------------------------------------------------------------------------*)
Section ProdReader.

  Variable X Y : readerType.

  Definition readProd : Reader (X*Y)  :=
    let! x = read;
    let! y = read;
    retn (x,y).

  Canonical Structure prod_readerType := Eval hnf in mkReaderType readProd. 

  Lemma readProdSplit x y p q m :
    readProd m p = readerOk (x,y) q ->
    exists p', read m p = readerOk x p' /\ 
               read m p' = readerOk y q.  
  Proof.
  move => H. rewrite /=/bindRead_op in H.
  case E1: (read m p) => [x' p' | |]; rewrite E1 in H; last done; last done. 
  exists p'. 
  case E2: (read m p') => [y' p'' | |]; rewrite E2 in H; last done; last done.  
  rewrite /unitRead_op in H.
  assert (EQ: (x', y') = (x,y) /\ p'' = q) by apply (splitReaderOk H). 
  split; congruence.   
  Qed.

End ProdReader.

(*---------------------------------------------------------------------------
   Reading sequences
  ---------------------------------------------------------------------------*)
Section ReadSeq.

  Variable R: readerType.

  Fixpoint readSeq  n : Reader (seq R) :=
  if n is n'.+1 then 
    let! x = read;
    let! xs = readSeq n';
    retn (x::xs)
  else 
    retn nil.

  Canonical Structure seq_readerType n := Eval hnf in mkReaderType (readSeq n). 

  Lemma readSeqCat xs : forall p ys q m, 
    readSeq (size xs + size ys) m p = readerOk (xs++ys) q ->
    exists p', readSeq (size xs) m p = readerOk xs p' /\ 
               readSeq (size ys) m p' = readerOk ys q.  
  Proof.
  induction xs => p ys q m H; first by exists p. 
  rewrite /=/bindRead_op in H. rewrite /=/bindRead_op. 
  case E1: (getReader R m p) => [z p' | |]; rewrite E1 in H; last done; last done. 
  case E2: (readSeq (size xs + size ys) m p') => [zs p'' | |]; rewrite E2 in H; last done; last done. 
  rewrite /unitRead_op in H.  
  inversion H; subst; clear H. 
  specialize (IHxs _ _ _ _ E2). 
  destruct IHxs as [p'' [H1 H2]]. exists p''.
  split; last done. 
  by rewrite H1. 
  Qed. 

  Lemma readSeqCons x : forall p ys q m, 
    readSeq (1 + size ys) m p = readerOk (x::ys) q ->
    exists p', read m p = readerOk x p' /\ 
               readSeq (size ys) m p' = readerOk ys q.  
  Proof. 
  move => p ys q m H. rewrite /=/bindRead_op in H. 
  rewrite /=/bindRead_op. 
  case E1: (getReader R m p) => [z p' | |]; rewrite E1 in H; last done; last done. 
  case E2: (readSeq (size ys) m p') => [zs p'' | |]; rewrite E2 in H; last done; last done. 
  rewrite /unitRead_op in H.  
  inversion H; subst; clear H. 
  by exists p'. 
  Qed. 


End ReadSeq. 

(*---------------------------------------------------------------------------
   Reading tuples
  ---------------------------------------------------------------------------*)
Require Import tuplehelp. 
Section ReadTuple.

  Variable R: readerType.

  Fixpoint readTuple {n} :Reader (n.-tuple R):=
  if n is n'.+1 then
    let! x = read;
    let! xs = readTuple;
    retn (cons_tuple x xs)
  else
    retn (nil_tuple _).

  Canonical Structure tuple_readerType n := Eval hnf in mkReaderType (@readTuple n). 

  (* Bit messy. I'm sure this could be simplified *)
  Lemma readTupleCat n1 : forall n2 (xs1:n1.-tuple R) p (xs2:n2.-tuple R) q m, 
    readTuple m p = readerOk (cat_tuple xs1 xs2) q ->
    exists p', readTuple m p = readerOk xs1 p' /\ 
               readTuple m p' = readerOk xs2 q.  
  Proof.
  induction n1.  
  + move => n2 xs1. rewrite (tuple0 xs1). move => p ys q m H. exists p. split; first done. by rewrite H catNil.
  + move => n2. case/tupleP => [x xs]. move => p ys q m H. 
    rewrite /=/bindRead_op in H. rewrite /=/bindRead_op. 
  case E1: (getReader R m p) => [z p' | |]; rewrite E1 in H; last done; last done. 
  case E2: (readTuple (n:=n1+n2) m p') => [zs p'' | |]; rewrite E2 in H; last done; last done. 
  rewrite /unitRead_op in H.
  rewrite catCons in H.
  assert (EQ: cons_tuple z zs = [tuple of x:: (cat_tuple xs ys)] /\ p'' = q) by apply (splitReaderOk H). 
  destruct EQ as [EQ1 EQ2].
  assert (EQ3: z = x /\ zs = cat_tuple xs ys) by by apply splitTuple. 
  destruct EQ3 as [EQ4 EQ5]. 
  specialize (IHn1 _ xs p' ys p'' m). 
  assert (HH: readTuple m p' = readerOk (cat_tuple xs ys) p'') by congruence.
  specialize (IHn1 HH). 
  destruct IHn1 as [p''' [H1 H2]]. exists p'''.
  split. rewrite H1. rewrite /unitRead_op. rewrite EQ4. done. 
  congruence. 
  Qed. 

End ReadTuple. 


