(*===========================================================================
    State transformer monad for processor
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool ssrnat finfun fintype seq eqtype.
Require Import bitsops bitsprops monad monadinst procstate exn reader enc cursor.
Require Import String FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope update_scope.

Definition ST := SMT (Result (option GeneralException)) ProcState.

Definition getProcState: ST ProcState := SMT_get _ (S:=_).
Definition setProcState: ProcState -> ST unit := SMT_set _ (S:=_). 
Definition raiseUnspecified {X} : ST X := SMT_lift _ (raiseError None).
Definition raiseExn {X} (e:GeneralException) : ST X := SMT_lift _ (raiseError (Some e)).

Definition getRegFromProcState r :=
  let! s = getProcState; 
  retn (registers s r). 

(* Retrieving a flag that is undefined leads to unspecified behaviour *)
Definition getFlagFromProcState f :=
  let! s = getProcState; 
  if flags s f is mkFlag b then 
    retn b 
  else 
    raiseUnspecified.

(* This is wrong because wrap-around is under-specified *)
Definition getFromProcState {R:readerType} (p: BITS 32) : ST R :=
  let! s = getProcState;
  match getReader R (memory s) p with
  | readerFail => raiseExn ExnGP
  | readerWrap => raiseUnspecified
  | readerOk v _ => retn v
  end.

Definition readFromProcState {R:readerType} (p: BITS 32) : ST (R*DWORD) :=
  let! s = getProcState;
  match getReader R (memory s) p with
  | readerOk v (mkCursor p) => retn (v,p)
  | _ => raiseExn ExnGP
  end.


(* See Section 5.3 in Volume 3A of Intel manuals *)
(* When effective segment limit is 0xffffffff then behaviour is unspecified for
   reads that wrap around. Otherwise, it is "correct": no partial reads or writes *)
Definition getBYTEFromProcState := getFromProcState (R:=BYTE_readerType). 
Definition getDWORDFromProcState := getFromProcState (R:=DWORD_readerType).
Definition getDWORDorBYTEFromProcState dword := getFromProcState (R:=DWORDorBYTE_readerType dword). 

(* Update monadic operations *)
Definition setRegInProcState (r:AnyReg) d :=
  let! s = getProcState; 
  setProcState (s!r:=d).

Definition updateFlagInProcState (f:Flag) (b:bool) :=
  let! s = getProcState; 
  setProcState (s!f:=b).  

Definition forgetFlagInProcState f :=
  let! s = getProcState; 
  setProcState (s!f:=FlagUnspecified).

Definition setBYTERegInProcState r (d: BYTE) :=
  let! s = getProcState;
  let (h,l) := split2 24 8 (registers s r) in
  setProcState (mkProcState (registers s !r := h ## d) (flags s) (memory s)).

Definition primSetBYTEInProcState (p: PTR) (b:BYTE) :=
  let! s = getProcState;
  if isMapped p (memory s) 
  then setProcState (s !p:=b)
  else raiseExn ExnGP. 

(* Behaviour is unspecified if we try to write bytes beyond the end of memory *)
Fixpoint setBYTESInProcState (pc: Cursor 32) (bs:seq BYTE) :=
  if bs is b::bs then
    if pc is mkCursor p then    
      do! primSetBYTEInProcState p b;
      setBYTESInProcState (next p) bs
    else raiseUnspecified
  else retn tt.

Definition setInProcState {X} `{Encoder X} p (x:X) := setBYTESInProcState p (encode x).
Definition setDWORDInProcState (p:DWORD) (d:DWORD) := setInProcState p d. 
Definition setBYTEInProcState (p:DWORD) (b:BYTE)   := setInProcState p b.
Definition setDWORDorBYTEInProcState dword p  :=
  if dword as dword return DWORDorBYTE dword -> _ 
  then fun d => setDWORDInProcState p d else fun d => setBYTEInProcState p d. 


(*
Require Import bitsrep tuplehelp. 
Instance FlagStateUpdate : Update FlagState Flag bool.
apply Build_Update. 
(* Same flag *)
move => m k v w.  
rewrite /update /FlagStateUpdateOps /setFlag /setBit.
induction k. simpl. rewrite beheadCons. done. 
rewrite /setBitAux-/setBitAux. rewrite !theadCons!beheadCons. 
rewrite IHk. simpl. done. simpl. rewrite 
*)

Lemma setRegGetRegDistinct Y r1 v r2 (f: _ -> ST Y) s : 
  ~~(r1 == r2) ->
  (do! setRegInProcState r1 v; bind (getRegFromProcState r2) f) s =
  (bind (getRegFromProcState r2) (fun x => do! setRegInProcState r1 v; f x)) s.
Proof. move => neq. rewrite /setRegInProcState /getRegFromProcState /=. 
rewrite setThenGetDistinct; by done.  
Qed.

(* Lemmas involving register lookup and update *)
Lemma doSetReg {Y} r v (f: ST Y) s : 
  (do! setRegInProcState r v; f) s = f (s !r:=v).
Proof. by rewrite /setRegInProcState/setProcState assoc SMT_bindGet SMT_doSet. Qed.

Lemma letGetReg {Y} (s: ProcState) r (f: DWORD -> ST Y): 
  bind (getRegFromProcState r) f s = f (registers s r) s. 
Proof. by rewrite /getRegFromProcState/getProcState assoc SMT_bindGet. Qed. 

