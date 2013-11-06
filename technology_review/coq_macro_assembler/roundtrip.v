(*===========================================================================
    Round trip properties for readers and writers
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
Require Import bitsrep bitsprops monad reader cursor writer String cstring.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The relation [simrw x p R W] is supposed to mean that reader R simulates
   writer W for the purpose of reading value x from position p.
   Simulating means that they essentially proceed in lock step, except that
   they are allowed to read the cursor position independently of each other.
   If the writer fails, there is no restriction on the reader.
 *)
Inductive simrw {X T} (x: X): 
  Cursor 32 -> Reader X -> WriterTm T -> Prop :=
| simrw_retn p t: simrw x p (readerRetn x) (writerRetn t)
| simrw_next p R b W': simrw x (next p) (R b) W' -> simrw x p (readerNext R) (writerNext b W')
| simrw_rcursor p R' W: simrw x p (R' p) W -> simrw x p (readerCursor R') W
| simrw_wcursor p R W': simrw x p R (W' p) -> simrw x p R (writerCursor W')
| simrw_fail p R: simrw x p R writerFail
| simrw_hwm R b W': simrw x (hwm _) R (writerNext b W').

(*---------------------------------------------------------------------------
   Put a reader and a writer together with a round-trip property
  ---------------------------------------------------------------------------*)
(*=Roundtrip *)
Class Roundtrip X (R: Reader X) (W: Writer X) :=
  roundtrip: forall x p, simrw x p R (W x).
(*=End *)

(* Generalisation of simrw_next that also handles Cursor *)
Lemma simrw_next' A (x:A) (p: Cursor 32) R b (W': WriterTm unit):
  (forall p': BITS 32, p = p' -> simrw x (next p') (R b) W') ->
  simrw x p (readerNext R) (writerNext b W').
Proof.
  intros H. elim Hp: p => [p'|]; last constructor. constructor. exact: H.
Qed.

(* Further generalisation. *)
Lemma simrw_bind A B T (R: Reader T) (W: Writer T) (HRW: Roundtrip R W)
      (x:A) (t:T) (p: Cursor 32) R' (W': WriterTm B):
  (forall p', simrw x p' (R' t) W') ->
  simrw x p (let! t' = readNext; R' t') (do! writeNext t; W').
Proof.
  intros H. simpl. rewrite /writeNext. specialize (HRW t p).
  induction HRW; try constructor; auto.
Qed.

Lemma simrw_bind_end A T (R: Reader T) (W: Writer T) (HRW: Roundtrip R W)
      (x:A) (t:T) (p: Cursor 32) R':
  (forall p', simrw x p' (R' t) (retn tt)) ->
  simrw x p (let! t' = readNext; R' t') (writeNext t).
Proof.
  intros H. rewrite <-doRet. exact: simrw_bind.
Qed.

(*---------------------------------------------------------------------------
   BYTE, WORD and DWORD reading and writing
  ---------------------------------------------------------------------------*)
Instance RoundtripBYTE : Roundtrip readBYTE writeBYTE.
Proof. move => x. elim => [p |]; repeat constructor. Qed. 

Instance RoundtripWORD : Roundtrip readWORD writeWORD.
Proof.
  move=> x p. rewrite /readWORD /writeWORD.
  elim e:(split2 8 8 x) => [b1 b0].
  apply simrw_next' => p0 _. apply simrw_next' => p1 _.
  rewrite (split2eta (x: BITS (8+8))).
  rewrite /split2 in e. injection e => <- <-; constructor.
Qed.

Instance RoundtripDWORD : Roundtrip readDWORD writeDWORD.
Proof.
  move => x p. rewrite /readDWORD/writeDWORD.
  elim e:(split4 8 8 8 8 x) => [[[b3 b2] b1] b0].
  apply simrw_next' => p' _.
  apply simrw_next' => {p'} p' _.
  apply simrw_next' => {p'} p' _.
  apply simrw_next' => {p'} p' _.
  rewrite -(split4eta (x:BITS (8+8+8+8))) e. constructor.
Qed. 

(*---------------------------------------------------------------------------
   DWORDorBYTE reading and writing
  ---------------------------------------------------------------------------*)
Instance RoundtripDWORDorBYTE dw : Roundtrip (readDWORDorBYTE dw) (writeDWORDorBYTE dw) := 
  if dw as dw return Roundtrip (readDWORDorBYTE dw) (writeDWORDorBYTE dw) 
  then RoundtripDWORD else RoundtripBYTE. 

Instance RoundtripPad m : Roundtrip (readPad m) (writePad m).
Proof. 
  induction m => v p; case v. 
  apply simrw_retn. 

  rewrite /readPad-/readPad. 
  rewrite /writePad-/writePad. 
  apply simrw_next' => p' _. 
  apply IHm.  
Qed.   

Require Import tuplehelp.
Instance RoundtripTupleBYTE m : Roundtrip (readTupleBYTE m) (@writeTupleBYTE m).
Proof. 
  induction m => v p. 
+ rewrite (tuple0 v)/=. apply simrw_retn.  
+ case/tupleP: v => [b bs].
  simpl. apply simrw_next' => p' _.
  rewrite beheadCons theadCons.
  apply simrw_bind_end; first apply IHm.
  move => p''.
  apply simrw_retn.    
Qed.   

Instance RoundtripAlign m : Roundtrip (readAlign m) (writeAlign m). 
Proof. 
rewrite /readAlign/writeAlign/Roundtrip.
move => v p. case v. 
constructor.
constructor.
destruct p; last exact: simrw_retn.
apply: RoundtripPad. 
Qed. 

