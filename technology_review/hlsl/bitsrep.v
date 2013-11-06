(*===========================================================================
  Basic representation of n-bit words

  We use n.-tuples of bools, as this gives decidable equality and finiteness
  for free. 

  Tuples are practical for evaluation inside Coq, and so all operations on 
  words can be evaluated using compute, cbv, etc. 

  Proofs of various properties of bitvectors can be found in bitsprops.v
  Definitions of operations on bitvectors can be found in bitsops.v
  Proofs of properties of operations can be found in bitsopsprops.v
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple fintype zmodp.
Require Import ZArith.

(* We represent n-bit words by a tuple of booleans, least-significant bit at the head *)
Definition BITS n := n.-tuple bool. 

(* Construction *)
Notation "'nilB'" := (nil_tuple _). 
Definition consB {n} (b:bool) (p: BITS n) : BITS n.+1 := cons_tuple b p. 
Definition joinlsb {n} (pair: BITS n*bool) : BITS n.+1 := cons_tuple pair.2 pair.1.

(* Destruction *)
Definition splitlsb {n} (p: BITS n.+1): BITS n*bool := (behead_tuple p, thead p).
Definition droplsb {n} (p: BITS n.+1) := (splitlsb p).1. 

(* Some useful synonyms *)
Definition NIBBLE := BITS 4.
Definition BYTE   := BITS 8.
Definition WORD   := BITS 16.
Definition DWORD  := BITS 32.
Definition QWORD  := BITS 64.

Identity Coercion DWORDtoBITS32 : DWORD >-> BITS.
Identity Coercion BYTEtoBITS32 : BYTE >-> BITS.
Identity Coercion WORDtoBITS32 : WORD >-> BITS.

(* This is useful especially for multi-mode instructions *)
Definition DWORDorBYTE (dword: bool) := BITS (if dword then 32 else 8). 

(*---------------------------------------------------------------------------
    Conversion to and from natural numbers.

    For large naturals, be careful to use ssrnat's Num and [Num of] constructs
    for creating and printing naturals.
  ---------------------------------------------------------------------------*)
Fixpoint fromNat {n} m : BITS n :=
  if n is _.+1 
  then joinlsb (fromNat m./2, odd m)
  else nilB. 
Notation "# m" := (fromNat m) (at level 0). (* e.g. write #10 for decimal 10 *)

Definition toNat {n} (p: BITS n) := foldr (fun (b:bool) n => b + n.*2) 0 p.

(*---------------------------------------------------------------------------
    All bits identical
  ---------------------------------------------------------------------------*)
Definition copy n b : BITS n := nseq_tuple n b.
Definition zero n := copy n false.
Definition ones n := copy n true.

(*---------------------------------------------------------------------------
    Concatenation and splitting of bit strings
  ---------------------------------------------------------------------------*)

(* Most and least significant bits, defaulting to 0 *)
Definition msb {n} (b: BITS n) := last false b.
Definition lsb {n} (b: BITS n) := head false b.

Definition catB {n1 n2} (p1: BITS n1) (p2: BITS n2) : BITS (n2+n1) := 
  cat_tuple p2 p1.
Notation "y ## x" := (catB y x) (right associativity, at level 60).  

(* The n high bits *)
Fixpoint high n {n2} : BITS (n2+n) -> BITS n :=
  if n2 is _.+1 then fun p => let (p,b) := splitlsb p in high _ p else fun p => p. 

(* The n low bits *)
Fixpoint low {n1} n : BITS (n+n1) -> BITS n := 
  if n is _.+1 then fun p => let (p,b) := splitlsb p in joinlsb (low _ p, b)
               else fun p => nilB.

(* n1 high and n2 low bits *)
Definition split2 n1 n2 p := (high n1 p, low n2 p).

Definition split3 n1 n2 n3 (p: BITS (n3+n2+n1)) : BITS n1 * BITS n2 * BITS n3 :=
  let (hi,lo) := split2 n1 _ p in 
  let (lohi,lolo) := split2 n2 _ lo in (hi,lohi,lolo).

Definition split4 n1 n2 n3 n4 (p: BITS (n4+n3+n2+n1)): BITS n1 * BITS n2 * BITS n3 * BITS n4 :=
  let (b1,rest) := split2 n1 _ p in 
  let (b2,rest) := split2 n2 _ rest in
  let (b3,b4)   := split2 n3 _ rest in (b1,b2,b3,b4).

(* Sign extend by {extra} bits *)
Definition signExtend extra {n} (p: BITS n.+1) := copy extra (msb p) ## p.

(* Truncate a signed integer by {extra} bits; return None if this would overflow *)
Definition signTruncate extra {n} (p: BITS (n.+1 + extra)) : option (BITS n.+1) :=
  let (hi,lo) := split2 extra _ p in
  if msb lo && (hi == ones _) || negb (msb lo) && (hi == zero _)
  then Some lo
  else None.

(* Zero extend by {extra} bits *)
Definition zeroExtend extra {n} (p: BITS n) := zero extra ## p.

(* Truncate an unsigned integer by {extra} bits; return None if this would overflow *)
Definition zeroTruncate extra {n} (p: BITS (n + extra)) : option (BITS n) :=
  let (hi,lo) := split2 extra _ p in
  if hi == zero _ then Some lo else None.
    
(* Special case: split at the most significant bit.
   split 1 n doesn't work because it requires BITS (n+1) not BITS n.+1 *)
Fixpoint splitmsb {n} : BITS n.+1 -> bool * BITS n := 
  if n is _.+1 
  then fun p => let (p,b) := splitlsb p in let (c,r) := splitmsb p in (c,joinlsb(r,b))
  else fun p => let (p,b) := splitlsb p in (b,p). 
Definition dropmsb {n} (p: BITS n.+1) := (splitmsb p).2. 

(* Extend by one bit at the most significant bit. Again, signExtend 1 n does not work
   because BITS (n+1) is not definitionally equal to BITS n.+1  *)
Fixpoint joinmsb {n} : bool * BITS n -> BITS n.+1 :=
  if n is _.+1 
  then fun p => let (hibit, p) := p in 
                let (p,b) := splitlsb p in joinlsb (joinmsb (hibit, p), b)
  else fun p => joinlsb (nilB, p.1).
Definition joinmsb0 {n} (p: BITS n) : BITS n.+1 := joinmsb (false,p).

(*---------------------------------------------------------------------------
    Single bit operations
  ---------------------------------------------------------------------------*)

(* Booleans are implicitly coerced to one-bit words, useful in combination with ## *)
Coercion singleBit b : BITS 1 := joinlsb (nilB, b).

(* Get bit i, counting 0 as least significant *)
(* For some reason tnth is not efficiently computable, so we use nth *)
Definition getBit {n} (p: BITS n) (i:nat) := nth false p i.

(* Set bit i to b *)
Fixpoint setBitAux {n} i b : BITS n -> BITS n :=
  if n is _.+1 
  then fun p => let (p,oldb) := splitlsb p in
                if i is i'.+1 then joinlsb (setBitAux i' b p, oldb) else joinlsb (p,b)
  else fun p => nilB.

Definition setBit {n} (p: BITS n) i b := setBitAux i b p.

(*---------------------------------------------------------------------------
    Efficient conversion to and from Z
  ---------------------------------------------------------------------------*)

Definition toPosZ {n} (p: BITS n) :=
  foldr (fun b z => if b then Zsucc (Zdouble z) else Zdouble z) Z0 p. 

Definition toNegZ {n} (p: BITS n) := 
  foldr (fun b z => if b then Zdouble z else Zsucc (Zdouble z)) Z0 p.

Definition toZ {n} (bs: BITS n.+1) :=
  match splitmsb bs with
  | (false, bs') => toPosZ bs'
  | (true, bs') => Zopp (Zsucc (toNegZ bs'))
  end.

Fixpoint fromPosZ {n} (z: Z): BITS n :=
  if n is _.+1 
  then joinlsb (fromPosZ (Zdiv2 z), negb (Zeven_bool z))
  else nilB.

Fixpoint fromNegZ {n} (z: Z): BITS n :=
  if n is _.+1 
  then joinlsb (fromNegZ (Zdiv2 z), Zeven_bool z)
  else nilB.

Definition fromZ {n} (z:Z) : BITS n :=
  match z with
  | Zpos _ => fromPosZ z
  | Zneg _ => fromNegZ (Zpred (Zopp z))
  | _ => zero _
  end.

(*---------------------------------------------------------------------------
    Conversion to and from 'Z_(2^n)
  ---------------------------------------------------------------------------*)

Definition toZp {n} (p: BITS n) : 'Z_(2^n) := inZp (toNat p).
Definition fromZp {n} (z: 'Z_(2^n)) : BITS n := fromNat z. 

Definition bool_inZp m (b:bool): 'Z_m := inZp b. 
Definition toZpAux {m n} (p:BITS n) : 'Z_(2^m) := inZp (toNat p). 


(*---------------------------------------------------------------------------
    Support for hexadecimal notation
  ---------------------------------------------------------------------------*)
Section HexStrings.
  Require Import String.
  Import Ascii.
  Definition charToNibble c : NIBBLE := 
    fromNat (findex 0 (String c EmptyString) "0123456789ABCDEF0123456789abcdef").
  Definition charToBit c : bool := ascii_dec c "1".

  Fixpoint digits s := 
  if s is String c s then digits s ++ [::charToNibble c] else nil.

  Program Fixpoint fromDigits n (d: seq NIBBLE) {struct d} : BITS n :=
  if n is n.+4
  then if d is c::rest then fromDigits n rest ## c else #0
  else #0. 

  Fixpoint bits s := 
  if s is String c s then bits s ++ [::charToBit c] else nil.

  Program Fixpoint fromBits n (d: seq bool) {struct d} : BITS n :=
  if n is n.+1
  then if d is c::rest then fromBits n rest ## c else #0
  else #0. 

  Definition fromHex {n} s := fromDigits n (digits s).
  Definition fromBin s := let n:= String.length s in fromBits n (bits s).

  Definition nibbleToChar (n: NIBBLE) := 
  match String.get (toNat n) "0123456789ABCDEF" with None => " "%char | Some c => c end.

  Definition appendNibbleOnString n s :=
  (s ++ String.String (nibbleToChar n) EmptyString)%string.

End HexStrings.

Fixpoint toHex {n} :=
  match n return BITS n -> string with
  | 0 => fun bs => EmptyString
  | 1 => fun bs => appendNibbleOnString (zero 3 ## bs) EmptyString
  | 2 => fun bs => appendNibbleOnString (zero 2 ## bs) EmptyString
  | 3 => fun bs => appendNibbleOnString (zero 1 ## bs) EmptyString
  | _ => fun bs => let (hi,lo) := split2 _ 4 bs in appendNibbleOnString lo (toHex hi)
  end.

Import Ascii.
Fixpoint bytesToHex (b: seq BYTE) :=
  if b is b::bs then
  String.String (nibbleToChar (high (n2:=4) 4 b)) (
             String.String (nibbleToChar (low 4 b)) (
             String.String (" "%char) (
             bytesToHex bs)))
  else ""%string.

Coercion hexToDWORD (s:string) :DWORD  := fromHex s.
Coercion hexToBYTE (s:string) :BYTE := fromHex s.

Notation "#x y" := (fromHex y) (at level 0). 
Notation "#b y" := (fromBin y) (at level 0).


