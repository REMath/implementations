(*===========================================================================
    Model for x86 memory

    Note that operations are partial, as not all memory is mapped
    A more refined model would incorporate R/W/X permissions, on the
    appropriate granularity. 

    BEWARE of "punning" this partiality for the purpose of defining
    separating conjunction: we will at some point wish to talk about *separate*
    regions of memory not all of which are accessible under given permissions,
    and the re-use of partiality for separation would preclude this. 
  ===========================================================================*)
Require Import ssreflect ssrfun ssrnat ssrbool finfun eqtype fintype seq.
Require Import bitsrep bitsops.
Require Export pmap.
Local Open Scope update_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* 32-bit addressable memory *)
Definition Mem := PMAP BYTE 32. 
Definition PTR := DWORD.
Identity Coercion PTRtoDWORD : PTR >-> DWORD.

(* Initially, no memory is mapped *)
Definition initialMemory : Mem := EmptyPMap.

(* Memory from p to just below p' in m consists exactly of the bytes in xs *)
Fixpoint memIs (m:Mem) (p p':PTR) xs :=
  if xs is x::xs then m p = Some x /\ memIs m (incB p) p' xs else p=p'.

Definition bytesToDWORD (b3 b2 b1 b0: BYTE) : DWORD := b3 ## b2 ## b1 ## b0.
Definition bytesToWORD (b1 b0: BYTE) : WORD := b1 ## b0.

(* Map some memory, filling it with ones (to be more visible!) *)
Definition reserveMemory (m: Mem) (p:PTR) (c: DWORD) : Mem :=  
  bIterFrom p c (fun p m => m !p := ones 8) m.

(* Returns bytes with most-significant first *)
Definition DWORDToBytes (d: DWORD) : BYTE*BYTE*BYTE*BYTE := split4 8 8 8 8 d.

Definition isMapped (p:PTR) (ms: Mem) : bool := ms p. 

Instance MemUpdateOpsDWORD : UpdateOps Mem PTR DWORD :=
  fun m p v =>
  let '(b3,b2,b1,b0) := DWORDToBytes v in
  m !p:=b0 !incB p:=b1 !incB(incB p):=b2 !incB(incB(incB p)):=b3. 

(*
Instance MemUpdateDWORD : Update Mem DWORD DWORD. 
Proof. 
apply Build_Update. 
move => m p v w. 
rewrite /update /MemUpdateOpsDWORD. 
destruct (DWORDToBytes w) as [[[b3 b2] b1] b0]. 
destruct (DWORDToBytes v) as [[[b7 b6] b5] b4]. 
rewrite (update_diff _ _ p).
rewrite (update_diff _ _ p).  
rewrite (update_diff _ _ p).
rewrite update_same. 
rewrite (update_diff _ _ (incB p)).
rewrite (update_diff _ _ (incB p)).  
rewrite update_same. 
rewrite (update_diff _ _ (incB (incB p)) _ b2).  
rewrite update_same. 
rewrite update_same. 
done. 
apply incBDistinct. 
apply incBDistinct. 
apply incBincBDistinct. 
apply incBDistinct. 
apply incBincBDistinct. 
apply incBincBincBDistinct. 

move => m p q v w pq. 
rewrite /update /MemUpdateOpsDWORD. 
destruct (DWORDToBytes w) as [[[b3 b2] b1] b0]. 
destruct (DWORDToBytes v) as [[[b7 b6] b5] b4]. 

rewrite (update_diff _ (incB (incB p))).  Implicit update_diff. rewrite update_same. 
simpl. 
Definition updateBYTE (p:DWORD) (b:BYTE) (ms: Mem) : option Mem :=
  if isMapped p ms then Some (ms !p := b) else None.

*)
