(* Additional lemmas about tuples *)
Require Import ssreflect ssrnat eqtype seq tuple.

Lemma mapCons {n A B} (f: A -> B) b (p: n.-tuple A) : 
  map_tuple f [tuple of b :: p] = [tuple of f b :: map_tuple f p]. 
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth (f b)). Qed.

Lemma theadCons : forall {n A} (a:A) (aa: n.-tuple A), thead [tuple of a::aa] = a. 
Proof. done. Qed. 

Lemma beheadCons {n A} a (aa: n.-tuple A) : behead_tuple [tuple of a::aa] = aa.
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed.

Lemma zipCons {n A B} a (aa: n.-tuple A) b (bb: n.-tuple B) : 
  zip_tuple [tuple of a::aa] [tuple of b::bb] = [tuple of (a,b) :: zip_tuple aa bb]. 
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth (a,b)). Qed.

Lemma nseqCons {n A} (a:A) : nseq_tuple (S n) a = [tuple of a::nseq_tuple n a]. 
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed.

Lemma catCons {n1 n2 A} (a:A) (aa:n1.-tuple A) (bb:n2.-tuple A) : 
  cat_tuple [tuple of a::aa] bb = [tuple of a::cat_tuple aa bb]. 
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed. 

Lemma catNil {n A} (aa:n.-tuple A) : 
  cat_tuple [tuple] aa = aa.  
Proof. exact: val_inj. Qed. 

Lemma behead_nseq {n A} (a:A) : behead_tuple (nseq_tuple n.+1 a) = nseq_tuple n a.
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed.

Lemma splitTuple {X n} {a b:X} {c d:n.-tuple X} : cons_tuple a c = cons_tuple b d -> a = b /\ c = d.
Proof. move => H. split. by inversion H. apply val_inj. by inversion H. Qed.

(* The last n elements *)
Fixpoint lastn {T} n {n2} : (n2+n).-tuple T -> n.-tuple T :=
  if n2 is _.+1 return (n2+n).-tuple T -> n.-tuple T
  then fun p => lastn _ (behead_tuple p) else fun p => p.

(* The first n elements *)
Fixpoint firstn {T} {n1} n : (n+n1).-tuple T -> n.-tuple T := 
  if n is _.+1 return (n+n1).-tuple T -> n.-tuple T
  then fun p => cons_tuple (thead p) (firstn _ (behead_tuple p)) else fun p => nil_tuple _. 

