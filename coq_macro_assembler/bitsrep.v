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
(* DWORDorBYTE is especially useful for multi-mode instructions *)
(*=BITS *)
Definition BITS n := n.-tuple bool. 
Definition NIBBLE := BITS 4.
Definition BYTE   := BITS 8.
Definition WORD   := BITS 16.
Definition DWORD  := BITS 32.
Definition QWORD  := BITS 64.
Definition DWORDorBYTE (d: bool) := 
  BITS (if d then 32 else 8).
(*=End *)


Identity Coercion DWORDtoBITS32 : DWORD >-> BITS.
Identity Coercion BYTEtoBITS32 : BYTE >-> BITS.
Identity Coercion WORDtoBITS32 : WORD >-> BITS.

(* Construction *)
Notation "'nilB'" := (nil_tuple _). 
Definition consB {n} (b:bool) (p: BITS n) : BITS n.+1 := cons_tuple b p. 
Definition joinlsb {n} (pair: BITS n*bool) : BITS n.+1 := cons_tuple pair.2 pair.1.

(* Destruction *)
Definition splitlsb {n} (p: BITS n.+1): BITS n*bool := (behead_tuple p, thead p).
Definition droplsb {n} (p: BITS n.+1) := (splitlsb p).1. 

(*---------------------------------------------------------------------------
    Conversion to and from natural numbers.

    For large naturals, be careful to use ssrnat's Num and [Num of] constructs
    for creating and printing naturals.
  ---------------------------------------------------------------------------*)
Fixpoint fromNat {n} m : BITS n :=
  if n is _.+1 
  then joinlsb (fromNat m./2, odd m)
  else nilB. 
Notation "# m" := (fromNat m) (at level 0). 
Arguments fromNat n m : simpl never.

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

(* Take m least significant bits of n-bit argument and fill with zeros if m>n *)
Fixpoint lowWithZeroExtend m {n} : BITS n -> BITS m := 
  if n is _.+1 
  then fun p => let (p,b) := splitlsb p in 
                if m is m'.+1 then joinlsb (@lowWithZeroExtend m' _ p, b)
                else zero 0
  else fun p => zero m.

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

Fixpoint zeroExtendAux extra {n} (p: BITS n) : BITS (extra+n) := 
  if extra is e.+1 then joinmsb0 (zeroExtendAux e p) else p.

Definition joinNibble {n}  (p:NIBBLE) (q: BITS n) : BITS (n.+4) :=
  let (p1,b0) := splitlsb p in
  let (p2,b1) := splitlsb p1 in
  let (p3,b2) := splitlsb p2 in
  let (p4,b3) := splitlsb p3 in
   joinmsb (b3, joinmsb (b2, joinmsb (b1, joinmsb (b0, q)))).
  
Notation "y ## x" := (catB y x) (right associativity, at level 60).  


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

(*=fromBin *)
Fixpoint fromBin s : BITS (length s) :=
  if s is String c s 
  then joinmsb (charToBit c, fromBin s) else #0. 
(*=End *)

(*=fromHex *)
Fixpoint fromHex s : BITS (length s * 4) :=
  if s is String c s 
  then joinNibble (charToNibble c) (fromHex s) else #0. 
(*=End *)

Fixpoint fromString s : BITS (length s * 8) :=
  if s is String c s return BITS (length s * 8) 
  then fromString s ## fromNat (n:=8) (nat_of_ascii c) else nilB.  

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
(*Fixpoint bytesToHex (b: seq BYTE) :=
  if b is b::bs then
  String.String (nibbleToChar (high (n2:=4) 4 b)) (
             String.String (nibbleToChar (low 4 b)) (
             String.String (" "%char) (
             bytesToHex bs)))
  else ""%string.
*)

Fixpoint bytesToHexAux (b: seq BYTE) res :=
  match b with b::bs => 
    bytesToHexAux bs (String.String (nibbleToChar (high (n2:=4) 4 b)) (
             String.String (nibbleToChar (low 4 b)) (
             String.String (" "%char) res)))
  | nil => res end.  

Definition bytesToHex b := bytesToHexAux (rev b) ""%string.

(* Convert an ASCII character (from the standard Coq library) to a BYTE *) 
Definition charToBYTE (c: ascii) : BYTE :=
  let (a0,a1,a2,a3,a4,a5,a6,a7) := c in
  [tuple a0;a1;a2;a3;a4;a5;a6;a7]. 

(* Convert an ASCII string to a tuple of BYTEs... *)
Fixpoint stringToTupleBYTE (s: string) : (length s).-tuple BYTE :=
  if s is String c s then cons_tuple (charToBYTE c) (stringToTupleBYTE s)
  else nil_tuple _.

(* ...which is easily coerced to a sequence *)
Definition stringToSeqBYTE (s: string) : seq BYTE :=
  stringToTupleBYTE s.

(* Notation for hex, binary, and character/string *)
Notation "#x y" := (fromHex y) (at level 0). 
Notation "#b y" := (fromBin y) (at level 0).
Notation "#c y" := (fromString y) (at level 0).

(*=fortytwo *)
Example fortytwo  := #42 : BYTE.
Example fortytwo1 := #x"2A".
Example fortytwo2 := #b"00101010".
Example fortytwo3 := #c"*".
(*=End *)

