(*===========================================================================
    Some useful instances of Monad
  ===========================================================================*)
Require Import ssreflect seq.
Require Import monad.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import FunctionalExtensionality. 

(*---------------------------------------------------------------------------
    Option monad
  ---------------------------------------------------------------------------*)
Instance optionMonadOps : MonadOps option :=
{ retn := Some
; bind := fun X Y (c: option X) f => if c is Some y then f y else None }.

Instance optionMonad : Monad option.
Proof. apply Build_Monad. done. move => X; by case. move => X Y Z; by case. Qed. 

(*---------------------------------------------------------------------------
    Error monad
  ---------------------------------------------------------------------------*)
Section Error.

  Variable F: Type.

  Inductive Result X :=
  | Error (f:F) 
  | Success (x:X).

  Global Instance errorMonadOps : MonadOps Result :=
  { retn := Success
  ; bind := fun X Y (c: Result X) f => 
    match c with Success x => f x | Error e => Error _ e end }.

  Global Instance errorMonad : Monad Result.
  Proof. apply Build_Monad. done. move => X; by case. move => X Y Z; by case. Qed. 

  Definition raiseError {X} e : Result X := Error _ e.

End Error.

(*---------------------------------------------------------------------------
    List monad
    @todo akenn: fix this so we don't get a universe inconsistency later!
  ---------------------------------------------------------------------------*)
(*
Lemma flatten_map_cat {A B} (f:A->seq B) x y : 
  flatten (map f (x ++ y)) = flatten (map f x) ++ flatten (map f y).
Proof. induction x => //. by rewrite /= IHx catA. Qed.

Instance seqMonadOps : MonadOps seq :=
{ retn := fun X (x:X) => x::nil
; bind := fun X Y (x: seq X) f => flatten (map f x) }.

Instance seqMonad : Monad seq.
Proof. apply Build_Monad. 
+ move => X Y x f. by rewrite /= cats0.  
+ move => X c. rewrite /=. induction c => //. by rewrite /=IHc.  
+ induction c => //. move => f g. rewrite/=flatten_map_cat. rewrite/= in IHc. by rewrite IHc. 
Qed.
*)
(*---------------------------------------------------------------------------
    I/O monad. D is the type of the input/output data
  ---------------------------------------------------------------------------*)
Section IO.

  Variable Chan: Type.
  Variable D: Type.

  Inductive IOM X :=
  | retnIO (x:X)
  | Out (ch:Chan) (d:D) (rest:IOM X)
  | In (ch:Chan) (f:D -> IOM X).

  Fixpoint bindIO X Y (c: IOM X) (f: X -> IOM Y) :=
   match c with 
   | retnIO y => f y 
   | Out ch d rest => Out ch d (bindIO rest f) 
   | In ch g => In ch (fun d => bindIO (g d) f)
   end.

  Global Instance IOMonadOps : MonadOps IOM :=
  { retn := retnIO; bind := bindIO }.

  Global Instance IOMonad : Monad IOM.
  Proof. apply Build_Monad.
  (* assoc *) done. 
  (* id_l *) induction c => //. 
  + rewrite /= in IHc. by rewrite /=IHc. 
  + rewrite /=. rewrite /= in H. by rewrite (functional_extensionality _ _ H). 
  (* id_r *) induction c => //. 
  + move => f g. rewrite /= in IHc. by rewrite /=IHc. 
  + move => f0 g. rewrite /= in H. 
    rewrite /=. apply f_equal. apply functional_extensionality. move => d. by rewrite H. 
  Qed. 

  Definition IO_write ch d : IOM unit := Out ch d (retn tt).
  Definition IO_read ch : IOM D := In ch retn.

  Require Import Streams. 
  Fixpoint IO_run X (s:Stream D) (m: IOM X) : seq D * X :=
  match m with
  | retnIO x => (nil,x)
  | In ch g => let: Cons h t := s in IO_run t (g h)
  | Out ch d m => let: (output, result) := IO_run s m in (cons d output, result)
  end.

  Definition OutputM X := (seq D * X)%type.
 
  Global Instance OutputMonadOps : MonadOps OutputM :=
  { retn := fun {X} (x:X) => (nil, x); 
    bind := fun {X Y} (c: OutputM X) (f: X -> OutputM Y) => 
            let (s, x) := c in
            let (s', y) := f x in (s++s', y) }.

  Global Instance OutputMonad : Monad OutputM.
  Proof. apply Build_Monad.
  (* assoc *) move => X Y x f. rewrite /bind/retn/=. by case (f x). 
  (* id_l *) move => X c. rewrite /bind/retn/=. case c => s x. by rewrite cats0.  
  (* id_r *) move => X Y Z c f g. case c => s x. 
    rewrite /bind/=. case (f x) => s' y. case (g y) => s'' z. by rewrite catA. 
  Qed. 

  Definition Output_write d : OutputM unit := ([::d], tt).
End IO. 

Existing Instance IOMonadOps.
Existing Instance IOMonad.
Existing Instance OutputMonadOps.
Existing Instance OutputMonad.

(*---------------------------------------------------------------------------
    State monad. S is the type of states
  ---------------------------------------------------------------------------*)
Section State.

  Context {S: Type}.

  Definition SM X := S -> (S * X)%type.

  (* Of course, this is a monad *)
  Global Instance SMonadOps : MonadOps SM :=
  { retn := fun X (x: X) (s:S) => (s, x)
  ; bind := fun X Y (c: SM X) (f: X -> SM Y) => 
            fun s => let (st1, a1) := c s in f a1 st1 }.

  Global Instance SMonad : Monad SM.
  Proof. 
  apply Build_Monad.
  (* assoc *) move => X Y x f. by apply functional_extensionality => s. 
  (* id_l *) move => X c. apply functional_extensionality => s. simpl. by elim (c s).  
  (* id_r *) move => X Y Z c f g. apply functional_extensionality => s. simpl. by elim (c s).
  Qed.   

  Definition SM_get : SM S := fun s => (s,s).
  Definition SM_set (s':S) : SM unit := fun s => (s',tt). 

  Lemma bindGet {Y} (s: S) (f: S -> SM Y): 
    bind SM_get f s = f s s.
  Proof. done. Qed. 

End State.

(*---------------------------------------------------------------------------
    Stateful I/O. S is the type of states, D the type of input/output data
  ---------------------------------------------------------------------------*)
(*
Require Import Streams. 
Section StateIO.

  Variable S: Type.
  Variable D: Type.

  Inductive Act := In (d:D) | Out (d:D).

  Definition SO X := S -> seq Act -> S -> X -> Prop.
  Inductive SOtrans X : SO X :=
  | unitSO (x: X) : forall s, SOtrans s nil s x
  | bindSO Y (c: SO Y) (f: Y -> SO X) : 
    forall s s' s'' t t' x y, c s t s' y -> f y s' t' s'' x -> SOtrans s (t++t') s'' x.


Check unitSO. SOtrans.
Check unitSO.
  (* Of course, this is a monad *)
  Global Instance SOMonadOps : MonadOps SO :=
  { retn := unitSO
  ; bind := bindSO }. fun X Y (c: SO X) (f: X -> SO Y) => 
            fun str s => let: (st1, xs1, a1) := c str s in 
                     let: (st2, xs2, a2) := f a1 str st1 in
                     (st2, xs1++xs2, a2) }.

  Global Instance SOMonad : Monad SO.
  Proof. 
  apply Build_Monad.
  (* assoc *) move => X Y x f. apply functional_extensionality => s. 
              simpl. by case E: (f x s) => [[st2 xs2] a2]. 
  (* id_l *) move => X c. apply functional_extensionality => s.
             simpl. case E: c => [[st xs] a]. by rewrite cats0. 
  (* id_r *) move => X Y Z c f g. apply functional_extensionality => s.
             simpl. case E1: (c s) => [[st1 xs1] a1]. 
                    case E2: (f a1 st1) => [[st2 xs2] a2]. 
                    case E3: (g a2 st2) => [[st3 xs3] a3]. by rewrite catA. 
  Qed.   

  Definition SO_get : SO S := fun s => (s,nil,s).
  Definition SO_set (s':S) : SO unit := fun s => (s',nil,tt). 
  Definition SO_output (d:D) : SO unit := fun s => (s,d::nil,tt).
End StateO.
*)

(*===========================================================================
    Monad transformers
  ===========================================================================*)

Section MonadTransformers.

(* Base monad *)
Variable M: Type -> Type.
Variable ops: MonadOps M.
Variable laws: Monad M.

(*---------------------------------------------------------------------------
    Option monad transformer
  ---------------------------------------------------------------------------*)
(* Base monad *)
Section OptionMT.

  Definition optionMT X := M (option X).

  Global Instance optionMT_ops : MonadOps optionMT :=
  { retn := fun X (x:X) => retn (Some x)
  ; bind := fun X Y (c: optionMT X) (f: X -> optionMT Y) => 
      bind (MonadOps:=ops) c (fun x:option X => if x is Some x' then f x' else retn None) }.

  Global Instance optionMT_laws : Monad optionMT.
  Proof. apply Build_Monad. 
  (* assoc *) move => X Y x f. by rewrite /=id_l. 
  (* id_l *)  move => X c. rewrite /= -{2}(id_r (option X) c). 
    apply: f_equal. apply functional_extensionality => x. by elim x.   
  (* id_r *) move => X Y Z c f g. rewrite /=assoc. apply: f_equal. 
    apply functional_extensionality => x. elim x => //. by rewrite id_l.  
  Qed. 

  Global Coercion OMT_lift {X} (c: M X) : optionMT X :=
  let! x = c; retn (Some x). 
End OptionMT.

(*---------------------------------------------------------------------------
    Error monad transformer
  ---------------------------------------------------------------------------*)
Section ErrorMT.

  Variable F: Type.

  Definition errorMT X := M (Result F X).

  Global Instance errorMT_ops : MonadOps errorMT :=
  { retn := fun X (x:X) => retn (Success _ x)
  ; bind := fun X Y (c: errorMT X) (f: X -> errorMT Y) => 
            bind (MonadOps:=ops) c (fun x => 
            match x with Success x => f x | Error e => retn (Error _ e) end) }.

  Global Instance errorMT_laws : Monad errorMT.
  Proof. apply Build_Monad. 
  (* assoc *) move => X Y x f. by rewrite/= id_l. 
  (* id_l *)  move => X c. simpl. rewrite -{2}(id_r (Result _ _) c).  
  apply f_equal. apply functional_extensionality => x. by elim x.   
  (* id_r *) move => X Y Z c f g. simpl. rewrite assoc. 
  apply f_equal. apply functional_extensionality => x. 
  elim x => //. move => f'. by rewrite id_l.  
  Qed. 

  Definition EMT_raise {X} e : errorMT X := 
    retn (Error _ e).

  Global Coercion EMT_lift {X} (c: M X) : errorMT X :=
    let! x = c; retn (Success _ x).

End ErrorMT.

(*---------------------------------------------------------------------------
    State monad transformer. S is the type of states, M is underlying monad

    This causes a universe inconsistency with procstatemonad.v!
  ---------------------------------------------------------------------------*)
Section StateMT.

  Variable S: Type.

  Definition SMT X := S -> M (S * X)%type.

  (* Of course, this is a monad *)
  Global Instance SMT_ops : MonadOps SMT :=
  { retn := fun X (x: X) (s:S) => retn (s, x)
  ; bind := fun X Y (c: SMT X) (f: X -> SMT Y) => 
            fun s => let! (st1, a1) = c s; f a1 st1 }.

  Global Instance SMT_laws : Monad SMT.
  Proof. 
  assert (H1:forall Z, (fun z:S*Z => let (st,x) := z in retn (T:=M)(st, x)) = fun z => retn z).
  move => Z. apply functional_extensionality. by elim.

  assert(H2: forall Z, (fun z:S*Z => retn z) = retn). 
  move => Z. by apply functional_extensionality. 

  apply Build_Monad. 
  (* assoc *) move => X Y x f. apply functional_extensionality => s. by rewrite /=id_l. 
  (* id_l *) move => X c. apply functional_extensionality => s. by rewrite /= H1/= id_r. 
  (* id_r *) move => X Y Z c f g. apply functional_extensionality => s.
  rewrite /= assoc/=. apply f_equal. apply functional_extensionality. by elim. 
  Qed.   

  Definition SMT_get : SMT S := fun s => retn (s,s). 
  Definition SMT_set (s':S) : SMT unit := fun s => retn (s',tt).

  Global Coercion SMT_lift {X} (c: M X) : SMT X := 
  fun s => let! r = c; retn (s,r).

  Lemma SMT_bindGet {Y} (s: S) (f: S -> SMT Y): 
    bind SMT_get f s = f s s.
  Proof. by rewrite /bind/SMT_get/= id_l. Qed. 

  Lemma SMT_doSet {Y} (s s': S) (c: SMT Y):
    (do! SMT_set s'; c) s = c s'.
  Proof. by rewrite /bind/SMT_set/= id_l. Qed. 

End StateMT.

End MonadTransformers.