(*===========================================================================
    Writer monad, with instances for BYTE and DWORD
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool finfun fintype ssrnat eqtype seq.
Require Import bitsrep bitsops bitsopsprops pmap cursor monad mem update pmapprops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
   We define a type of "writer returning T", such that

   write m p = writerFail if relevant memory beyond p in m is inaccessible 
   write m p = writerWrap if we tried to write beyond the end of memory
   write m p = writerOk m' q if we have now written between p inclusive and q exclusive to obtain m'
  ---------------------------------------------------------------------------*)
CoInductive writerResult T := 
  writerOk (x:T) (m:Mem) (q:Cursor 32) | writerWrap | writerFail. 
Definition writer T := Mem -> Cursor 32 -> writerResult T.
Implicit Arguments writerOk [T].
Implicit Arguments writerWrap [T].
Implicit Arguments writerFail [T].

(* When writing to p a good writer produces a pointer q >= p and
   does not make updates outside the range p inclusive to q exclusive *)
(* @TODO: a good writer doesn't read i.e. doesn't depend on contents of memory *)
Definition goodWriter T (write: Mem -> Cursor 32 -> writerResult T) :=
  forall m pos,
    if write m pos is writerOk v m' pos' then
      leCursor pos pos' /\
      forall p':BITS _, outRange pos pos' p' -> m p' = m' p'
    else True.  

(* Package a writer together with a proof of goodness *)
Structure Writer T := mkWriter     {op; _: @goodWriter T op}.
Structure writerType := mkWriterType {sort; getWriter: Writer sort}. 
Coercion op : Writer >-> Funclass.
Coercion sort : writerType >-> Sortclass.

Definition write T := @getWriter T.
Implicit Arguments write [T]. 

Lemma writeP T : goodWriter (@write T). 
Proof. destruct T as [T W]; by destruct W. Qed.

(*---------------------------------------------------------------------------
   Writer monad
  ---------------------------------------------------------------------------*)
Definition retnWrite_op X (x:X) : writer X  := fun m p => writerOk x m p. 

Definition bindWrite_op T U (w: writer T) (f: T -> writer U) : writer U :=
  fun m pos => match w m pos with
               | writerOk x m' pos' => f x m' pos'
               | writerFail => writerFail
               | writerWrap => writerWrap
               end.

Lemma retnWrite_good X (x:X) : goodWriter (retnWrite_op x).  
Proof. move => m pos. split => //. apply leCursor_refl.  Qed. 

Canonical Structure retnWrite X (x:X) := mkWriter (@retnWrite_good _ x). 

Lemma bindWrite_good T U (w: Writer T) (f: T -> Writer U) 
  : goodWriter (bindWrite_op (op w) (fun x => op (f x))).  
Proof. move => m pos. rewrite /bindWrite_op.  
assert (GW1: goodWriter w) by by destruct w.
case E1: (op w m pos) => [x' m' pos' | |] => //. 
case E2: (op (f x') m' pos') => [x'' m'' pos'' | |] => //. 
rewrite /goodWriter in GW1. specialize(GW1 m pos). rewrite E1 in GW1. 
destruct GW1 as [LE1 H1].
assert (GW2: goodWriter (f x')) by by destruct (f x').  
rewrite /goodWriter in GW2. specialize (GW2 m' pos'). rewrite E2 in GW2. 
destruct GW2 as [LE2 H2]. 
split. 
apply: leCursor_trans LE1 LE2.
move => p' RANGE. 
specialize (H1 p'). specialize (H2 p'). 
rewrite /outRange in H1 H2 RANGE.
case (andP RANGE) => [R1 R2]. 
rewrite H1. rewrite H2. done. 
rewrite R2 andbT. apply: ltCursor_leCursor_trans R1 LE1. 
rewrite R1 andTb. apply: leCursor_trans LE2 R2. 
Qed.  

Canonical Structure bindWrite T U w f := mkWriter (@bindWrite_good T U w f). 

(* Of course Writer is a monad *)
Instance writerMonadOps : MonadOps Writer :=
{ retn := retnWrite
; bind := bindWrite
}.

Require Import FunctionalExtensionality. 
Require Import ProofIrrelevance. 

Lemma writerMixin_extensional T (w1 w2: Writer T) :
  (forall m, op w1 m = op w2 m) -> w1 = w2.
Proof. move => H. 
assert (HH := functional_extensionality _ _ H).
destruct w1 as [op1 ax1]. destruct w2 as [op2 ax2].
simpl in HH. subst. by rewrite (proof_irrelevance _ ax1 ax2). 
Qed. 

Instance writerMonad : @Monad Writer writerMonadOps.
Proof. apply Build_Monad. 

move => X Y x f.
apply writerMixin_extensional => m. rewrite /bind /= /bindWrite_op /retnWrite_op. by apply functional_extensionality.  

move => X c. 
apply writerMixin_extensional => m. rewrite /=/bindWrite_op. apply functional_extensionality => p. by case (c m p).

move => X Y Z c f g. 
apply writerMixin_extensional => m. rewrite /=/bindWrite_op. apply functional_extensionality => p. by case (c m p).  
Qed.


(*---------------------------------------------------------------------------
   Lookup cursor
  ---------------------------------------------------------------------------*)
Definition getCursor_op : writer DWORD := 
  fun m pos => 
  if pos is mkCursor p 
  then writerOk p m pos 
  else writerFail.

Lemma getCursor_good : goodWriter getCursor_op. 
Proof. move => m pos. rewrite /getCursor_op. 
case E1: pos => [p |]; last done. 
split => //. apply leCursor_refl. 
Qed. 

Definition getCursor := mkWriter getCursor_good.  


(*---------------------------------------------------------------------------
   BYTE writer
  ---------------------------------------------------------------------------*)
Definition writeBYTE_op b : writer unit  := 
  fun m pos => 
  if pos is mkCursor p
  then if m p then writerOk tt (updatePMap m p b) (next p) else writerFail
  else writerWrap.

Lemma writeBYTE_good v : goodWriter (writeBYTE_op v). 
Proof. move => m pos. rewrite /writeBYTE_op.  
case E1: pos => [pos' |] //.
case E2: (m pos') => [b |] //. rewrite /isSome. 
split. apply leNext. 
move => p' RANGE.
rewrite updateThenLookupDistinct => //. 
rewrite /outRange in RANGE. 
case (andP RANGE) => [R1 R2]. 
move => H. 
rewrite H in R1. 
rewrite ltCursor_nat in R1. by rewrite ltnn in R1. 
Qed. 

Canonical Structure writeBYTE v := mkWriter (writeBYTE_good v).  

(* Writer for WORDs is easy to construct *)
Definition writeWORD : WORD -> Writer unit :=
  fun w =>
  let: (b1,b0) := split2 8 8 w in
  do! writeBYTE b0;
  do! writeBYTE b1;
  retn tt.


(* Writer for DWORDs is easy to construct *)
Definition writeDWORD : DWORD -> Writer unit :=
  fun d =>
  let: (b3,b2,b1,b0) := split4 8 8 8 8 d in
  do! writeBYTE b0;
  do! writeBYTE b1;
  do! writeBYTE b2;
  do! writeBYTE b3;
  retn tt.

