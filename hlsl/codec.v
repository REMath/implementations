(*===========================================================================
    Codec: put a reader and an encoder together with round-trip property
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
Require Import bitsrep bitsprops mem monad reader cursor enc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* A codec consists of a reader, an encoder and a roundtrip property *)
Definition memIs (m:Mem) p q (bs: seq BYTE) := readSeq _ (size bs) m p = readerOk bs q.

Lemma memIsApp : forall {m xs p p'} ys,
  memIs m p p' (xs++ys) -> exists p'', memIs m p p'' xs /\ memIs m p'' p' ys.
Proof.
move => m xs p p' ys mi. 
rewrite /memIs in mi. 
rewrite size_cat in mi. 
assert (H := readSeqCat mi). 
destruct H as [pos'' [H1 H2]]. by exists pos''.  
Qed. 

Lemma memIsCons m x xs p p' :
  memIs m p p' (x::xs) -> memIs m p (nextCursor p) [::x] /\ memIs m (nextCursor p) p' xs.
Proof. move => mi.
assert (H := readSeqCons mi).  
destruct H as [pos'' [H1 H2]]. simpl in H1.
rewrite /nextCursor.  
rewrite /readBYTE_op in H1. 
case E: p => [pos |]. 
+ rewrite E in H1. 
  case E': (m pos) => [b |]. 
  - rewrite E' in H1. rewrite /memIs/=/bindRead_op/readBYTE_op E' /unitRead_op/=. 
    split. congruence. 
    subst. rewrite -H2. by inversion H1. 
    split. by rewrite E' in H1. by rewrite E' in H1. 
+ split. rewrite E in H1. done. rewrite E in H1. done. 
Qed. 

Class Codec {R:readerType} {E: Encoder R} := 
  roundtrip: forall {m p q x}, memIs m p q (encode x) -> (getReader R) m p = readerOk x q.
Implicit Arguments Codec [E]. 

Instance CodecBYTE : Codec BYTE_readerType.
Proof. move => m p q x. rewrite /memIs /readSeq /=. 
rewrite  /bindRead_op /unitRead_op /encode /encodeBYTE /BYTE_readerType /read /= /readBYTE_op. 
case E1: p => [pp |]; last done. 
case E2: (m pp) => [b |]; last done. 
congruence.  
Qed. 

Lemma applyRoundtrip {X Y:readerType} `{ed:Codec X} {m:Mem} {q x w} {f: X -> Reader Y} :
  (f x m q = w) ->
  (forall p, memIs m p q (encode x) -> bind (getReader X) f m p = w).
Proof. move => H p MI. rewrite /bind /= /bindRead_op (roundtrip MI). by apply H. Qed.

Lemma applyRoundtripCat {X Y:readerType} `{ed:Codec X} {m q x z w} (f : X -> Reader Y) :
  (forall p, memIs m p q              z  -> f x m p = w) ->
  (forall p, memIs m p q (encode x ++ z) -> bind (getReader X) f m p = w).
Proof. 
  move => H p MI. 
  case: (memIsApp MI) => [p' [MI1 MI2]].
  assert (RT := roundtrip MI1). 
  rewrite /bind /= /bindRead_op  RT. 
  by apply (H p' MI2). 
Qed.

Lemma applyRoundtripCons {Y:readerType} {m q} (x:BYTE) {z w} (f : BYTE -> Reader Y) :
  forall p, 
  (memIs m (nextCursor p) q z  -> f x m (nextCursor p) = w) ->
  (memIs m p q (encode x ++ z) -> bind readBYTE f m p = w).
Proof. 
  move => p H MI. 
  case: (memIsCons MI) => [MI1 MI2].
  specialize (H MI2).   
  simpl.   rewrite /bindRead_op. rewrite /memIs/=/bindRead_op in MI1.  
  destruct (readBYTE_op m p) => //. by inversion MI1.  
Qed.

Instance CodecDWORD : Codec DWORD_readerType.
Proof. move => m p q x.
rewrite /encode /encodeDWORD. 
elim e:(split4 8 8 8 8 x) => [[[b3 b2] b1] b0].
rewrite /getReader /=.
apply: applyRoundtripCat => ?. 
apply: applyRoundtripCat => ?. 
apply: applyRoundtripCat => ?. 
apply applyRoundtrip. rewrite -(split4eta (x:BITS(8+8+8+8))) /bytesToDWORD. 
by rewrite e. 
Qed. 

Instance CodecWORD : Codec WORD_readerType.
Proof. move => m p q x.
rewrite /encode /encodeWORD. 
elim e:(split2 8 8 x) => [b1 b0].
rewrite /getReader /=.
apply: applyRoundtripCat => ?. 
apply applyRoundtrip. simpl in x. rewrite /split2 in e. 
replace b1 with (@high 8 8 x) by congruence. 
replace b0 with (@low 8 8 x) by congruence. 
rewrite /bytesToWORD. by rewrite -(split2eta (x:BITS(8+8))). 
Qed. 

(*
Instance CodecDWORDorBYTE dword : Codec (DWORDorBYTE_readerType dword).
*)
