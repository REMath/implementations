(*===========================================================================
    Monadic syntax and monad laws 
  ===========================================================================*)
Require Import ssreflect ssrnat.

(* Collect the monad operations in their own class, and define nice Fsharp-like notation *)
(*=MonadOps *)
Class MonadOps T :=
{ retn {X} : X -> T X
; bind {X Y} : T X -> (X -> T Y) -> T Y }.
(*=End *)

Notation "'let!' x = c ; d" := 
  (bind c (fun x => d)) 
  (at level 200, x ident, c at level 150, d at level 200, right associativity).

Notation "'let!' ( x , y ) = c ; d" :=
  (bind c (fun z => match z with ( x , y ) => d end)) 
  (at level 200, x ident, y ident, c at level 150, d at level 200).

Notation "'let!' ( x , y , z ) = c ; d" :=
  (bind c (fun z => match z with ( x , y , z ) => d end)) 
  (at level 200, x ident, y ident, c at level 150, d at level 200).

Notation "'do!' c ; d" := 
  (bind c (fun _ => d)) 
  (at level 200, c at level 150, d at level 200).

Fixpoint doMany {T} {ops: MonadOps T} n (c:T unit) : T unit :=
if n is n.+1 
then (do! c; doMany n c) 
else retn tt.

(*=Monad *)
Class Monad T {ops: MonadOps T} :=
{ id_l X Y (x: X) (f: X -> T Y) : bind (retn x) f = f x
; id_r X (c: T X) : bind c retn = c
; assoc X Y Z (c: T X) (f: X -> T Y) (g : Y -> T Z) :
          bind (bind c f) g = bind c (fun x => bind (f x) g) }.
(*=End *)
Lemma doManyAdd {T} {ops: MonadOps T} {laws: Monad T}  n c : 
  forall n', doMany (n+n') c = do! doMany n c; doMany n' c.
Proof. induction n; move => n'. by rewrite add0n id_l. by rewrite /= assoc IHn. Qed.

Require Import FunctionalExtensionality. 

Lemma doLet {T}{X} `{HT: Monad T} (c1: T unit) (c2: unit -> T X) :
  (let! u = c1; c2 u) = (do! c1; c2 tt).
Proof.
  f_equal. extensionality u. by case: u.
Qed. 

Lemma doRet {T} `{HT: Monad T} c :
  (do! c; retn tt) = c.
Proof.
  by rewrite -doLet id_r.
Qed. 