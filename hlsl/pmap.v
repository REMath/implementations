(*===========================================================================
  Representation of partial finite maps whose domain is BITS n
  We use a representation that is sparse, has O(n) lookup, and is canonical
  so Leibniz equality coincides with extensional equality
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
Require Import bitsrep.
Require Export update.

(* Binary maps: a PMAP V n is a partial map from BITS n to values in V *)
Section Maps.

  Variable V: Type.

  (* Non-empty maps *)
  Inductive NEPMAP : nat -> Type := 
  | VAL   : V -> NEPMAP 0
  | SPLIT : forall {n} (lo hi: NEPMAP n), NEPMAP n.+1
  | LSPLIT : forall {n} (lo: NEPMAP n), NEPMAP n.+1
  | RSPLIT : forall {n} (hi: NEPMAP n), NEPMAP n.+1.

  (* Possibly-empty maps *)
  Inductive PMAP n := 
  | PMap :> NEPMAP n -> PMAP n
  | EmptyPMap : PMAP n. 

  (* Lookup an element in the map *)
  Fixpoint lookupNE {n} (m: NEPMAP n) : BITS n -> option V :=
  match m with
  | VAL v          => fun p => Some v
  | SPLIT _  lo hi => fun p => let (p,b) := splitlsb p in if b then lookupNE hi p else lookupNE lo p
  | LSPLIT _ lo    => fun p => let (p,b) := splitlsb p in if b then None else lookupNE lo p
  | RSPLIT _ hi    => fun p => let (p,b) := splitlsb p in if b then lookupNE hi p else None
  end.
  Definition lookup {n} (m: PMAP n) (p:BITS n) := if m is PMap m' then lookupNE m' p else None.

  (* Singleton NEPMAP *)
  Fixpoint singleNE {n} : BITS n -> V -> NEPMAP n :=
  match n with
  | O => fun p v => VAL v
  | S _ => fun p v => let (p,b) := splitlsb p in 
                      if b then RSPLIT (singleNE p v) 
                           else LSPLIT (singleNE p v)
  end.

  (* Update an element in the map *)
  Fixpoint updateNE {n} (m: NEPMAP n) : BITS n -> V -> NEPMAP n :=
  match m with
  | SPLIT _ lo hi => 
    fun p v => let (p,b) := splitlsb p in 
    if b then SPLIT lo (updateNE hi p v) else SPLIT (updateNE lo p v) hi
  | LSPLIT _ lo => 
    fun p v => let (p,b) := splitlsb p in
    if b then SPLIT lo (singleNE p v) else LSPLIT (updateNE lo p v)
  | RSPLIT _ hi => 
    fun p v => let (p,b) := splitlsb p in 
    if b then RSPLIT (updateNE hi p v) else SPLIT (singleNE p v) hi
  | VAL _ => 
    fun p v => VAL v
  end.

  Definition updatePMap {n} (m: PMAP n) (p: BITS n) (v: V) :=
  if m is PMap m' then PMap _ (updateNE m' p v) else PMap _ (singleNE p v).

  (* Remove an element from the map if it is present *)
  Fixpoint removeNE {n} (m: NEPMAP n) : BITS n -> option (NEPMAP n) :=
  match m with
  | SPLIT _ lo hi => 
    fun p => let (p,b) := splitlsb p in
    if b then 
      if removeNE hi p is Some m' then Some (SPLIT lo m') else Some (LSPLIT lo)
    else 
      if removeNE lo p is Some m' then Some (SPLIT m' hi) else Some (RSPLIT hi)

  | LSPLIT _ lo => 
    fun p => let (p,b) := splitlsb p in 
    if b then Some (LSPLIT lo)
    else if removeNE lo p is Some m' then Some (LSPLIT m') else None
  | RSPLIT _ hi => 
    fun p => let (p,b) := splitlsb p in
    if b then if removeNE hi p is Some m' then Some (RSPLIT m') else None
    else Some (RSPLIT hi)
  | VAL _ => 
    fun p => None
  end.

  Definition removePMap {n} (m: PMAP n) (p: BITS n) :=
  if m is PMap m' 
  then (if removeNE m' p is Some m'' then PMap _ m'' else EmptyPMap _) 
  else m.

  Definition consBfun {A} {n} b (f: BITS n.+1 -> A): BITS n -> A :=
    fun x => f (consB b x).

  Fixpoint fillNE {n} : (BITS n -> V) -> NEPMAP n :=
    match n with
    | 0 => fun f => VAL (f (zero _))
    | S n' => fun f =>
        SPLIT (fillNE (consBfun false f)) (fillNE (consBfun true f))
    end.

  (* Builds a total map with the same mappings as f *)
  Definition fill {n} (f: BITS n -> V) : PMAP n := PMap _ (fillNE f).

  (* Builds a partial map with the same mappings as f *)
  Fixpoint pmap_of {n} : (BITS n -> option V) -> PMAP n :=
    match n as n return (BITS n -> option V) -> PMAP n with
    | 0 => fun f => match f (zero _) with
                    | Some v => PMap _ (VAL v)
                    | None => @EmptyPMap _
                    end
    | S n' => fun f =>
        let left := pmap_of (consBfun false f) in
        let right := pmap_of (consBfun true f) in
        match left, right with
        | PMap ml , PMap mr => SPLIT ml mr
        | PMap ml , EmptyPMap => LSPLIT ml
        | EmptyPMap , PMap mr => RSPLIT mr
        | EmptyPMap , EmptyPMap => @EmptyPMap _
        end
    end.

End Maps.

Implicit Arguments lookup [n V]. 
Implicit Arguments singleNE [n V]. 
Implicit Arguments updateNE [n V]. 
Implicit Arguments lookupNE [n V]. 
Implicit Arguments removePMap [n V]. 
Implicit Arguments updatePMap [n V]. 
Implicit Arguments EmptyPMap [n V]. 
Implicit Arguments fillNE [n V]. 
Implicit Arguments fill [n V]. 
Implicit Arguments pmap_of [n V]. 

(* Usually we just use function application for lookup *)
Definition PMapToFun V n (p: PMAP V n) := lookup p.
Coercion PMapToFun : PMAP >-> Funclass. 

(* Nice syntax for functional update *)
Instance PMapUpdateOps {n} V : UpdateOps (PMAP V n) _ _ := @updatePMap V n. 


