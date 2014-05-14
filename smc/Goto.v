Require Import
  Coqlib Utf8
  Integers
  Util
  LatticeSignatures
  AbMachineNonrel.

Set Implicit Arguments.
Unset Elimination Schemes.

Inductive register := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7.
Instance register_eq_dec : EqDec register.
Proof.
unfold EqDec.
refine (
  λ r r',
  match r, r' with
  | R0, R0
  | R1, R1
  | R2, R2
  | R3, R3
  | R4, R4
  | R5, R5
  | R6, R6
  | R7, R7
    => left eq_refl
  | _, _ => right _
  end);
  abstract discriminate.
Defined.

Inductive flag := FLE | FLT | FEQ.
Instance flag_eq_dec : EqDec flag.
Proof.
unfold EqDec.
refine (λ f f',
        match f, f' with
        | FEQ, FEQ
        | FLT, FLT
        | FLE, FLE => left eq_refl
        | _, _ => right _
        end);
  abstract congruence.
Defined.

Definition addr := int.

Inductive instruction :=
(* arithmetic *)
| ICst (v:int) (dst:register)
| IBinop (op: int_binary_operation) (src dst: register)
| ICmp (src dst: register)
(* memory *)
| ILoad  (src dst: register)
| IStore (src dst: register)
(* control *)
| IGoto (tgt: addr)
| IGotoCond (f: flag) (tgt: addr)
| IGotoInd (r: register)
| ISkip
| IHalt (r: register)
.

Section Encoding.

Definition encode_register (r: register) : Z :=
  match r with
  | R0 => 0
  | R1 => 1
  | R2 => 2
  | R3 => 3
  | R4 => 4
  | R5 => 5
  | R6 => 6
  | R7 => 7
  end.

Definition decode_register (v: Z) : option register :=
  match v with
  | 0 => Some R0
  | 1 => Some R1
  | 2 => Some R2
  | 3 => Some R3
  | 4 => Some R4
  | 5 => Some R5
  | 6 => Some R6
  | 7 => Some R7
  | _ => None
  end.

Definition encode_flag (f: flag) : Z :=
  match f with
  | FLE => 0
  | FLT => 1
  | FEQ => 2
  end.

Definition decode_flag (v: Z) : option flag :=
  match v with
  | 0 => Some FLE
  | 1 => Some FLT
  | 2 => Some FEQ
  | _ => None
  end.

Definition encode_binop (op: int_binary_operation) : Z :=
  match op with
  | OpAdd  => 0
  | OpSub  => 1
  | OpMul  => 2
  | OpDivs => 3
  | OpShl  => 4
  | OpShr  => 5
  | OpShru => 6
  | OpAnd  => 7
  | OpOr   => 8
  | OpXor  => 9
  | OpCmp  _ => 10
  | OpCmpu _ => 11
  end.

Definition decode_binop (v: Z) : option int_binary_operation :=
  match v with
  | 0 => Some OpAdd
  | 1 => Some OpSub
  | 2 => Some OpMul
  | 3 => Some OpDivs
  | 4 => Some OpShl
  | 5 => Some OpShr
  | 6 => Some OpShru
  | 7 => Some OpAnd
  | 8 => Some OpOr
  | 9 => Some OpXor
  | _ => None
  end.

Definition combine_instruction (type arg src dst: Z) : Z :=
    type * two_p 24
  + arg  * two_p 16
  + src  * two_p 8
  + dst  * two_p 0.

Definition encode_Z : Z → int := Int.repr.
Definition decode_Z : int → Z := Int.unsigned.

Definition split_instruction (v: int) : Z * Z * Z * Z :=
  let v := decode_Z v in
  let (v, dst) := Z.div_eucl v 256 in
  let (v, src) := Z.div_eucl v 256 in
  let (v, arg) := Z.div_eucl v 256 in
  let (v, type) := Z.div_eucl v 256 in
  (type, arg, src, dst).

Local Notation "[ t , a , s , d ]" := (encode_Z (combine_instruction t a s d)).
Local Coercion encode_register : register >-> Z.
Local Coercion encode_flag : flag >-> Z.
Local Coercion encode_binop : int_binary_operation >-> Z.

Definition encode_instr (i: instruction) : list int :=
  match i with
  | ICst v rd =>       [ 9, 0,  0, rd] :: v :: nil
  | IBinop op rs rd => [ 8,op, rs, rd] :: nil
  | ICmp rs rd =>      [ 7, 0, rs, rd] :: nil
  | ILoad rs rd =>     [ 6, 0, rs, rd] :: nil
  | IStore rs rd =>    [ 5, 0, rs, rd] :: nil
  | IGoto v =>         [ 4, 0,  0, 0] :: v :: nil
  | IGotoCond f v =>   [ 3, f,  0, 0] :: v :: nil
  | IGotoInd rs =>     [ 2, 0, rs, 0] :: nil
  | ISkip =>           [ 1, 0,  0, 0] :: nil
  | IHalt rs =>        [ 0, 0, rs, 0] :: nil
  end.

Notation "p +1" := (Int.add p Int.one) (at level 39).

Definition decode_from (m: int → int) (base: int) : option (instruction * nat) :=
  match split_instruction (m base) with
  | (0, 0, src, 0) => do_opt rs <- decode_register src; Some (IHalt rs, 1%nat)
  | (1, 0, 0, 0) => Some (ISkip, 1%nat)
  | (2, 0, src, 0) => do_opt rs <- decode_register src; Some (IGotoInd rs, 1%nat)
  | (3, flg, 0, 0) => do_opt f <- decode_flag flg;
                      Some (IGotoCond f (m (base+1)), 2%nat)
  | (4, 0, 0, 0) => Some (IGoto (m (base+1)), 2%nat)
  | (5, 0, src, dst) => do_opt rs <- decode_register src;
                        do_opt rd <- decode_register dst;
                        Some (IStore rs rd, 1%nat)
  | (6, 0, src, dst) => do_opt rs <- decode_register src;
                        do_opt rd <- decode_register dst;
                        Some (ILoad rs rd, 1%nat)
  | (7, 0, src, dst) => do_opt rs <- decode_register src;
                        do_opt rd <- decode_register dst;
                        Some (ICmp rs rd, 1%nat)
  | (8, o, src, dst) => do_opt op <- decode_binop o;
                        do_opt rs <- decode_register src;
                        do_opt rd <- decode_register dst;
                        Some (IBinop op rs rd, 1%nat)
  | (9, 0, 0, dst) => do_opt rd <- decode_register dst;
                      Some (ICst (m (base+1)) rd, 2%nat)
  | _ => None
  end.

Definition decode_instr (e: list int) : option (instruction * nat) :=
  decode_from (λ n, nth (Zabs_nat (Int.unsigned n)) e Int.zero) Int.zero.

Lemma unit_test0 :
  decode_instr (encode_instr ISkip) = Some (ISkip, 1%nat).
Proof. reflexivity. Qed.

Lemma unit_test1 :
  decode_instr (encode_instr (IHalt R4)) = Some (IHalt R4, 1%nat).
Proof. reflexivity. Qed.

Lemma unit_test2 :
  decode_instr (encode_instr (ICst (Int.repr 64) R7)) = Some (ICst (Int.repr 64) R7, 2%nat).
Proof. reflexivity. Qed.

Lemma unit_test3 :
  decode_instr (encode_instr (IBinop OpMul R2 R5)) = Some (IBinop OpMul R2 R5, 1%nat).
Proof. reflexivity. Qed.

Lemma unit_test4 :
  decode_instr (encode_instr (IGotoCond FLT (Int.repr 127))) = Some (IGotoCond FLT (Int.repr 127), 2%nat).
Proof. reflexivity. Qed.

End Encoding.
