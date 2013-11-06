(*===========================================================================
    Notation for instructions
    You can cut-and-paste this notation into inline assembler in VS!
  ===========================================================================*)
Require Import ssreflect ssrbool seq.
Require Import bitsrep bitsops reg instr.
Require Export String.

(* Sugar *)
Definition SrcImm n := SrcI (fromNat n). 
Coercion SrcImm : nat >-> Src.

Delimit Scope instr_scope with asm. 

Notation "'[' r ']'" := 
  (mkMemSpec r None #0) 
  (at level 0, r at level 0, n at level 0) : instr_scope.

Notation "'[' r '+' n ']'" := 
  (mkMemSpec r None #n) 
  (at level 0, r at level 0, n at level 0) : instr_scope.

Notation "'[' r '-' n ']'" := 
  (mkMemSpec r None (negB #n)) 
  (at level 0, r at level 0, n at level 0) : instr_scope.

Notation "'[' r '+' i '+' n ']'" := 
  (mkMemSpec r (Some (i,S1)) #n) 
  (at level 0, r at level 0, i at level 0, n at level 0) : instr_scope.

Notation "'[' r '+' i '*' '2' ']'" := 
  (mkMemSpec r (Some(i,S2)) #0) 
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '2' '+' n ']'" := 
  (mkMemSpec r (Some(i,S2)) #n) 
  (at level 0, r at level 0, i at level 0, n at level 0) : instr_scope.

Notation "'[' r '+' i '*' '4' ']'" := 
  (mkMemSpec r (Some(i,S4)) #0) 
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '4' '+' n ']'" := 
  (mkMemSpec r (Some(i,S4)) #n) 
  (at level 0, r at level 0, i at level 0, n at level 0) : instr_scope.

Notation "'[' r '+' i '*' '8' ']'" := 
  (mkMemSpec r (Some(i,S8)) #0) 
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '8' '+' n ']'" := 
  (mkMemSpec r (Some(i,S8)) #n) 
  (at level 0, r at level 0, i at level 0, n at level 0) : instr_scope.

Definition DWORDtoDWORDorBYTE dword : DWORD -> DWORDorBYTE dword :=
  match dword return DWORD -> DWORDorBYTE dword 
  with true => fun d => d | false =>fun d => low 8 d end. 

Definition RegMemPairToDstSrc {dword} dst src := 
  match dst, src with
  | RegMemR dst, SrcR src => DstSrcRR dword dst src
  | RegMemR dst, SrcM src => DstSrcRM dword dst src
  | RegMemR dst, SrcI c => DstSrcRI dword dst (DWORDtoDWORDorBYTE dword c)
  | RegMemM dst, SrcR src => DstSrcMR dword dst src
  (* Don't do it! *)
  | RegMemM dst, SrcM src => DstSrcMI dword dst #0
  | RegMemM dst, SrcI c => DstSrcMI dword dst (DWORDtoDWORDorBYTE dword c)
  end.
(*Coercion DstSrcPairCoerce : nat >-> Src. *)

Definition SrcToRegImm src :=
  match src with
  | SrcI c => RegImmI true c
  | SrcR r => RegImmR true r
  (* Don't do it! *)
  | SrcM m => RegImmI _ #0
  end.

(*Notation "'mov' x , ':' y" := (MOVOPGEN x (#y)) (x at level 0, y at level 0, at level 40).

Notation "'mov' x , '$' y" := (MOVOPGEN x (#y)) (x at level 0, y at level 0, at level 40).
*)
Notation "'mov' x , y" := (MOVOP true (RegMemPairToDstSrc x y)) (x,y at level 0, at level 40).
Notation "'mov' 'byte' x , y" := (MOVOP false (RegMemPairToDstSrc x y)) (x,y at level 0, at level 40).

Notation inc := (UOP true OP_INC). 
Notation dec := (UOP true OP_DEC). 
Notation not := (UOP true OP_NOT). 
Notation neg := (UOP true OP_NEG).

Notation "'adc' x , y" := (BOP true OP_ADC (RegMemPairToDstSrc x y)) (x,y at level 0, at level 40).
Notation "'add' x , y" := (BOP true OP_ADD (RegMemPairToDstSrc x y)) (x,y at level 0, at level 40).
Notation "'sub' x , y" := (BOP true OP_SUB (RegMemPairToDstSrc x y)) (x,y at level 0, at level 40).
Notation "'sbb' x , y" := (BOP true OP_SBB (RegMemPairToDstSrc x y)) (x,y at level 0, at level 40).
Notation "'and' x , y" := (BOP true OP_AND (RegMemPairToDstSrc x y)) (x,y at level 0, at level 40).
Notation "'or' x , y" := (BOP true OP_OR (RegMemPairToDstSrc x y)) (x,y at level 0, at level 40).
Notation "'xor' x , y" := (BOP true OP_XOR (RegMemPairToDstSrc x y)) (x,y at level 0, at level 40).
Notation "'cmp' x , y" := (BOP true OP_CMP (RegMemPairToDstSrc x y)) (x,y at level 0, at level 40).
Notation "'test' x , y" := (TESTOP true x (SrcToRegImm y)) (x,y at level 0, at level 40).

Notation "'sal' x , c" := (SHIFTOP true OP_SAL x (ShiftCountI #c)) (x, c at level 0, at level 40).
Notation "'sar' x , c" := (SHIFTOP true OP_SAR x (ShiftCountI #c)) (x, c at level 0, at level 40).
Notation "'shl' x , c" := (SHIFTOP true OP_SHL x (ShiftCountI #c)) (x, c at level 0, at level 40).
Notation "'shr' x , c" := (SHIFTOP true OP_SHR x (ShiftCountI #c)) (x, c at level 0, at level 40).
Notation "'rcl' x , c" := (SHIFTOP true OP_RCL x (ShiftCountI #c)) (x, c at level 0, at level 40).
Notation "'rcr' x , c" := (SHIFTOP true OP_RCR x (ShiftCountI #c)) (x, c at level 0, at level 40).
Notation "'rol' x , c" := (SHIFTOP true OP_ROL x (ShiftCountI #c)) (x, c at level 0, at level 40).
Notation "'ror' x , c" := (SHIFTOP true OP_ROR x (ShiftCountI #c)) (x, c at level 0, at level 40).
Notation "'mul' x" := (MUL x) (x at level 0, at level 40).

Notation "'ja' x"  := (JCC CC_BE false x) (at level 40, format "'ja' x").
Notation "'jae' x" := (JCC CC_B false x) (at level 40, format "'jae' x").
Notation "'jab' x" := (JCC CC_B true x) (at level 40, format "'jab' x").
Notation "'jbe' x" := (JCC CC_BE true x) (at level 40, format "'jbe' x").
Notation "'jc' x"  := (JCC CC_B true  x) (at level 40, format "'jc' x").
Notation "'je' x"  := (JCC CC_Z true  x) (at level 40, format "'je' x").
Notation "'jg' x"  := (JCC CC_LE false x) (at level 40, format "'jg' x").
Notation "'jge' x" := (JCC CC_L false  x) (at level 40, format "'jge' x").
Notation "'jl' x"  := (JCC CC_L true   x) (at level 40, format "'jl' x").
Notation "'jle' x" := (JCC CC_LE true x) (at level 40, format "'jle' x").
Notation "'jna' x" := (JCC CC_BE true  x) (at level 40, format "'jna' x").
Notation "'jnb' x" := (JCC CC_B false  x) (at level 40, format "'jnb' x").
Notation "'jnbe' x" := (JCC CC_BE false  x) (at level 40, format "'jnbe' x").
Notation "'jnc' x" := (JCC CC_B false  x) (at level 40, format "'jnc' x").
Notation "'jne' x" := (JCC CC_Z false  x) (at level 40, format "'jne' x").
Notation "'jng' x" := (JCC CC_LE true  x) (at level 40, format "'jng' x").
Notation "'jnge' x" := (JCC CC_L true  x) (at level 40, format "'jnge' x").
Notation "'jnl' x" := (JCC CC_L false  x) (at level 40, format "'jnl' x").
Notation "'jnle' x" := (JCC CC_LE false  x) (at level 40, format "'jnle' x").
Notation "'jno' x" := (JCC CC_O false  x) (at level 40, format "'jno' x").
Notation "'jnp' x" := (JCC CC_P false  x) (at level 40, format "'jnp' x").
Notation "'jns' x" := (JCC CC_S false  x) (at level 40, format "'jns' x").
Notation "'jnz' x" := (JCC CC_Z false  x) (at level 40, format "'jnz' x").
Notation "'jo' x" := (JCC CC_O true  x) (at level 40, format "'jo' x").
Notation "'jp' x" := (JCC CC_P true  x) (at level 40, format "'jp' x").
Notation "'jpe' x" := (JCC CC_P true  x) (at level 40, format "'jpe' x").
Notation "'jpo' x" := (JCC CC_P false  x) (at level 40, format "'jpo' x").
Notation "'js' x" := (JCC CC_S true  x) (at level 40, format "'js' x").
Notation "'jz' x" := (JCC CC_Z true  x) (at level 40, format "'jz' x").

Notation "'jmp' x"  := (JMP (SrcI x)) (at level 40).
Notation "'call' x"  := (CALL (SrcI x)) (at level 40, format "'call' x").
Notation "'push' x"  := (PUSH x) (at level 40).
Notation "'pop' x"  := (POP x) (at level 40).
Notation "'ret' x" := (RET (# x)) (at level 40, format "'ret' x"). 


