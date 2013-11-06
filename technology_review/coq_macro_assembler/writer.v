(*===========================================================================
    Syntax for writers, with instances for BYTE and DWORD
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool finfun fintype ssrnat eqtype seq tuple.
Require Import bitsrep bitsops bitsopsprops cursor monad monadinst.
Require Import FunctionalExtensionality String cstring.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*=WriterTm *)
Inductive WriterTm A := 
| writerRetn (x: A)
| writerNext (b: BYTE) (w: WriterTm A)
| writerCursor (w: Cursor 32 -> WriterTm A)
| writerFail.
Class Writer T := 
  getWriterTm: T -> WriterTm unit.

Instance writeBYTE : Writer BYTE := 
  fun b => writerNext b (writerRetn tt).
(*End *)
Implicit Arguments writerFail [[A]].

Fixpoint writerTmBind X Y (w: WriterTm X) (f: X -> WriterTm Y) : WriterTm Y :=
  match w with
  | writerRetn x => f x
  | writerNext b w' => writerNext b (writerTmBind w' f)
  | writerCursor w' => writerCursor (fun p => writerTmBind (w' p) f)
  | writerFail => @writerFail _
  end.

Instance writerTmMonadOps : MonadOps WriterTm :=
{ retn := @writerRetn
; bind := writerTmBind }.

Instance writerTmMonad : Monad WriterTm. 
Proof. apply Build_Monad. 
(* id_l *)
  move => X Y x f. done. 
(* id_r *)
  move => X. elim => //. 
  - by move => b w' /= ->.
  - move => w' /= IH.
    apply f_equal. apply functional_extensionality => p. by rewrite IH. 
(* assoc *)
  move => X Y Z. elim => //. 
  - move => b w' /= IH f g. by rewrite IH.
  - move => w' /= IH f g.
    apply f_equal. apply functional_extensionality => p. by rewrite IH. 
Qed. 

Definition getWCursor : WriterTm (Cursor 32) := writerCursor (fun p => writerRetn p).
Definition writeNext {T} {W: Writer T}: Writer T := W.

(* Functional interpretation of writer on sequences *)
Fixpoint runWriterTm X (w: WriterTm X) (c: Cursor 32) : option (X * seq BYTE) :=
  match w with
  | writerRetn x => Some (x, nil)
  | writerNext byte w =>
    if c is mkCursor p
    then 
      if runWriterTm w (next p) is Some (x, bytes) then Some (x, byte::bytes) else None
    else None
  | writerFail => None
  | writerCursor w => runWriterTm (w c) c 
  end.

Lemma runWriterTm_bind X Y (w1: WriterTm X) (w2: X -> WriterTm Y) p y bytes:
  runWriterTm (let! x = w1; w2 x) p = Some (y, bytes) ->
  exists x p' bytes1 bytes2,
    runWriterTm w1 p = Some (x, bytes1) /\
    runWriterTm (w2 x) p' = Some (y, bytes2) /\
    bytes = bytes1 ++ bytes2.
Proof.
  revert p bytes. induction w1 => p bytes Hrun //=.
  - exists x, p, nil, bytes. rewrite Hrun. by eauto.
  - simpl in Hrun. destruct p as [p|]; last done.
    revert Hrun.
    case Hrun': (runWriterTm (writerTmBind w1 w2) (next p)) => [[y' bytes']|];
        last done.
    move=> [Hy' Hbytes]. subst y' bytes.
    apply IHw1 in Hrun' as [x [p' [bytes1 [bytes2 IH]]]].
    case: IH => Hw1 [Hw2 Hbytes'] => {IHw1}.
    do 4 eexists. rewrite Hw1. split; first done. split; first eassumption.
    rewrite Hbytes'. done.
  - simpl in Hrun.
    apply H in Hrun as [x [p' [bytes1 [bytes2 IH]]]].
    case: IH => Hw1 [Hw2 Hbytes'] => {H}.
    eauto 10.
Qed.

Definition runWriter T (w: Writer T) (c: Cursor 32) (x: T): option (seq BYTE) :=
  let! (_, bytes) = runWriterTm (w x) c;
  retn bytes.

(*---------------------------------------------------------------------------
   Writer type class together with BYTE, WORD, DWORD and pad instances
  ---------------------------------------------------------------------------*)

(*=writeDWORD *)
Instance writeDWORD : Writer DWORD := fun d =>
  let: (b3,b2,b1,b0) := split4 8 8 8 8 d in
  do! writeBYTE b0;
  do! writeBYTE b1;
  do! writeBYTE b2;
  do! writeBYTE b3;
  retn tt.
(*=End *)

Instance writeWORD : Writer WORD := fun w =>
  let: (b1,b0) := split2 8 8 w in
  do! writeNext b0;
  do! writeNext b1;
  retn tt.

Instance writeDWORDorBYTE dw : Writer (DWORDorBYTE dw) := 
  if dw as dw return Writer (DWORDorBYTE dw) then writeDWORD else writeBYTE. 
Implicit Arguments writeDWORDorBYTE [].

Fixpoint writePad m : Writer unit := fun _ =>
  if m is m'.+1 
  then do! writeBYTE #0; writePad m' tt 
  else retn tt.

Definition writeAlign (m:nat) : Writer unit := fun _ => 
  let! c = getWCursor;
  if c is mkCursor pos
  then writePad (toNat (negB (lowWithZeroExtend m pos))) tt
  else retn tt.

Fixpoint writeTupleBYTE (m:nat) : Writer (m.-tuple BYTE) := 
  if m is m'.+1
  then fun tup => do! writeBYTE (thead tup); writeTupleBYTE (behead_tuple tup)
  else fun tup => retn tt.

Global Existing Instance writeTupleBYTE.

Fixpoint writeString (n:nat) : Writer string := fun s =>
  if n is n'.+1
  then if s is String c s' 
       then do! writeBYTE (fromNat (Ascii.nat_of_ascii c)); writeString n' s'
       else do! writeBYTE #0; writeString n' s
  else retn tt.

Definition writeCString : Writer cstring := fun cs =>
  (fix WS (s:string) :=
  if s is String c s' 
  then do! writeBYTE (fromNat (Ascii.nat_of_ascii c)); WS s'
  else writeBYTE #0) cs.  

Global Existing Instance writeCString. 


