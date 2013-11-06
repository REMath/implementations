(*===========================================================================
  Arithmetic and logical operations on n-bit words
  For proofs of properties of operations see bitsopsprops.v
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
    Increment and decrement operations
  ---------------------------------------------------------------------------*)

Fixpoint incB {n} : BITS n -> BITS n :=
  if n is n.+1 
  then fun p => let (p,b) := splitlsb p in 
                if b then joinlsb (incB p, false) else joinlsb (p, true)
  else fun _ => nilB. 

Fixpoint decB {n} : BITS n -> BITS n :=
  if n is _.+1
  then fun p => let (p,b) := splitlsb p in 
                if b then joinlsb (p, false) else joinlsb (decB p, true)
  else fun _ => nilB.

(*---------------------------------------------------------------------------
    Bitwise logical operations
  ---------------------------------------------------------------------------*)

(* Lift a unary operation on booleans to one on n-bit values *)
Definition liftUnOp {n} op (p: BITS n): BITS n := map_tuple op p.

(* Lift a binary operation on booleans to one on n-bit values *)
Definition liftBinOp {n} op (p1 p2: BITS n) : BITS n :=
  map_tuple (fun pair => op pair.1 pair.2) (zip_tuple p1 p2).  

Definition invB {n} := liftUnOp (n:=n) negb.
Definition andB {n} := liftBinOp (n:=n) andb. 
Definition orB  {n} := liftBinOp (n:=n) orb. 
Definition xorB {n} := liftBinOp (n:=n) xorb.

(* Negation (two's complement) *)
Definition negB {n} (p: BITS n) := incB (invB p).

(*---------------------------------------------------------------------------
    Addition
  ---------------------------------------------------------------------------*)

Definition fullAdder carry b1 b2 : bool * bool :=
    match carry, b1, b2 with
    | false, false, false => (false, false) 
    | true, false, false | false, true, false | false, false, true => (false, true)
    | true, true, false | false, true, true | true, false, true => (true, false)
    | true, true, true => (true, true)
    end.

(* Add with carry, producing a word one bit larger than the inputs *)  
Fixpoint adcB n carry : BITS n -> BITS n -> BITS n.+1 :=
  if n is _.+1 then
    fun p1 p2 => let (p1,b1) := splitlsb p1 in let (p2,b2) := splitlsb p2 in
           let (carry',b) := fullAdder carry b1 b2 in
           joinlsb (adcB carry' p1 p2, b)
  else fun _ _ => singleBit carry.

(* Add with carry=0 and ignore carry out *)
Definition addB {n} (p1 p2: BITS n) := dropmsb (adcB false p1 p2).

(* Add with carry=0 and return None on overflow *)
Definition addBovf n (p1 p2: BITS n) := 
  let: (c,r) := splitmsb (adcB false p1 p2) in 
  if c then None else Some r.

Definition computeOverflow n (arg1 arg2 res: BITS n) :=
  match (msb arg1,msb arg2,msb res) with
  | (true,true,false) | (false,false,true) => true | _ => false
  end.

(* Some handy notation *)
Notation "b +# n" := (addB b #n) (at level 50, left associativity).

(*---------------------------------------------------------------------------
    Subtraction
  ---------------------------------------------------------------------------*)

Definition sbbB {n} borrow (arg1 arg2: BITS n) := 
  let (carry,res) := splitmsb (adcB (~~borrow) arg1 (invB arg2))
  in (~~carry,res). 
Definition subB {n} (p1 p2: BITS n) := (sbbB false p1 p2).2. 

Notation "b -# n" := (subB b #n) (at level 50, left associativity).

(*---------------------------------------------------------------------------
    Unsigned comparison
  ---------------------------------------------------------------------------*)
Fixpoint ltB {n} : BITS n -> BITS n -> bool :=
  if n is n.+1 
  then fun p1 p2 => let (q1,b1) := splitlsb p1 in
                    let (q2,b2) := splitlsb p2 in
                    (ltB q1 q2 || ((q1 == q2) && (~~b1) && b2))
  else fun p1 p2 => false.

Definition leB {n} (p1 p2: BITS n) := ltB p1 p2 || (p1 == p2).

(*---------------------------------------------------------------------------
    Multiplication
  ---------------------------------------------------------------------------*)
Fixpoint fullmulB n1 n2 : BITS n1 -> BITS n2 -> BITS (n1+n2) :=
  if n1 is n.+1 return BITS n1 -> BITS n2 -> BITS (n1+n2)
  then (fun p1 p2 => let (p,b) := splitlsb p1 in 
       if b then addB (joinlsb (fullmulB p p2, false)) (zeroExtendAux n.+1 p2)
            else joinlsb (fullmulB p p2, false))
  else (fun p1 p2 => #0).

Definition mulB {n} (p1 p2: BITS n) :=
  low n (fullmulB p1 p2).

Notation "b *# n" := (mulB b #n) (at level 40, left associativity).
 
(*---------------------------------------------------------------------------
    Shift and rotation operations
  ---------------------------------------------------------------------------*)

(* Rotate right: lsb goes into msb, everything else gets shifted right *)
Definition rorB {n} (p: BITS n.+1) : BITS n.+1 := let (p,b) := splitlsb p in joinmsb (b, p). 

(* Rotate left: msb goes into lsb, everything else gets shifted left *)
Definition rolB {n} (p: BITS n.+1) := let (b,p) := splitmsb p in joinlsb (p, b).

(* Shift right: shift everything right and put 0 in msb *)
Definition shrB {n} : BITS n -> BITS n := 
  if n is n.+1 then fun p =>  joinmsb0 (droplsb (n:=n) p) else fun p => nilB. 

(* Arithmetic shift right: shift one bit to the right, copy msb *)
Definition sarB {n} (p: BITS n.+1) := joinmsb (msb p, droplsb p).

(* Lossless shift left: shift one bit to the left, put 0 in lsb *)
Definition shlBaux {n} (p: BITS n) : BITS n.+1  := joinlsb (p, false).

(* Shift left: shift one bit to the left, put 0 in lsb, lose msb *)
Definition shlB {n} (p: BITS n)  := dropmsb (shlBaux p).

(*---------------------------------------------------------------------------
    Iteration and ranges
  ---------------------------------------------------------------------------*)

(* Iteration *)
Fixpoint bIter {n A} : BITS n -> (A -> A) -> A -> A :=
  if n is m.+1 
  then fun p f x => if p == zero _ then x
                    else let (p,b) := splitlsb p in
                    if b then let r := bIter p f (f x) in bIter p f r
                    else let r := bIter p f x in bIter p f r
  else fun p f x => x.

Definition bIterFrom {n A} (p c: BITS n) (f: BITS n -> A -> A) x :=
  let (p',r) := bIter c (fun pair : BITS n * A => let (p,r) := pair in (incB p, f p r)) (p,x)
  in r.   

(* Ranges *)
Definition bIota {n} (p m: BITS n) : seq (BITS n) := rev (bIterFrom p m cons nil).
Definition bRange {n} (p q: BITS n) := bIota p (subB q p). 
