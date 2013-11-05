(* Copyright (c) 2005, Regents of the University of California
 * All rights reserved.
 *
 * Author: Adam Chlipala
 * Extended by: Goran Doychev, Ignacio Echeverria, Laurent Mauborgne
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - Neither the name of the University of California, Berkeley nor the names of
 *   its contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

(* Utility functions *)

open X86Types
open AsmUtil

let reg8_to_int = function
    AL -> 0
  | CL -> 1
  | DL -> 2
  | BL -> 3
  | AH -> 4
  | CH -> 5
  | DH -> 6
  | BH -> 7

let reg8_to_string = function
    AL -> "AL"
  | CL -> "CL"
  | DL -> "DL"
  | BL -> "BL"
  | AH -> "AH"
  | CH -> "CH"
  | DH -> "DH"
  | BH -> "BH"

let int_to_reg8 = function
    0 -> AL
  | 1 -> CL
  | 2 -> DL
  | 3 -> BL
  | 4 -> AH
  | 5 -> CH
  | 6 -> DH
  | 7 -> BH
  | _ -> raise (Invalid_argument "int_to_reg8")

let reg16_to_int = function
    AX -> 0
  | CX -> 1
  | DX -> 2
  | BX -> 3
  | SP -> 4
  | BP -> 5
  | SI -> 6
  | DI -> 7

let reg16_to_string = function
    AX -> "AX"
  | CX -> "CX"
  | DX -> "DX"
  | BX -> "BX"
  | SP -> "SP"
  | BP -> "BP"
  | SI -> "SI"
  | DI -> "DI"

let int_to_reg16 = function
    0 -> AX
  | 1 -> CX
  | 2 -> DX
  | 3 -> BX
  | 4 -> SP
  | 5 -> BP
  | 6 -> SI
  | 7 -> DI
  | _ -> raise (Invalid_argument "int_to_ret16")

let reg32_to_int = function
    EAX -> 0
  | ECX -> 1
  | EDX -> 2
  | EBX -> 3
  | ESP -> 4
  | EBP -> 5
  | ESI -> 6
  | EDI -> 7

let reg32_to_string = function
    EAX -> "EAX"
  | ECX -> "ECX"
  | EDX -> "EDX"
  | EBX -> "EBX"
  | ESP -> "ESP"
  | EBP -> "EBP"
  | ESI -> "ESI"
  | EDI -> "EDI"

let int_to_reg32 = function
    0 -> EAX
  | 1 -> ECX
  | 2 -> EDX
  | 3 -> EBX
  | 4 -> ESP
  | 5 -> EBP
  | 6 -> ESI
  | 7 -> EDI
  | _ -> raise (Invalid_argument "int_to_reg32")

let string_to_reg32 = function
    "EAX" -> EAX
  | "ECX" -> ECX
  | "EDX" -> EDX
  | "EBX" -> EBX
  | "ESP" -> ESP
  | "EBP" -> EBP
  | "ESI" -> ESI
  | "EDI" -> EDI
  | _ -> raise (Invalid_argument "reg32_to_string")

let segment_reg_to_int = function
    ES -> 0
  | CS -> 1
  | SS -> 2
  | DS -> 3
  | FS -> 4
  | GS -> 5

let segment_reg_to_string = function
    ES -> "ES"
  | CS -> "CS"
  | SS -> "SS"
  | DS -> "DS"
  | FS -> "FS"
  | GS -> "GS"

let int_to_segment_reg = function
    0 -> ES
  | 1 -> CS
  | 2 -> SS
  | 3 -> DS
  | 4 -> FS
  | 5 -> GS
  | _ -> raise (Invalid_argument "int_to_segment_reg")

let float_reg_to_int = function
    ST0 -> 0
  | ST1 -> 1
  | ST2 -> 2
  | ST3 -> 3
  | ST4 -> 4
  | ST5 -> 5
  | ST6 -> 6
  | ST7 -> 7

let float_reg_to_string = function
    ST0 -> "ST0"
  | ST1 -> "ST1"
  | ST2 -> "ST2"
  | ST3 -> "ST3"
  | ST4 -> "ST4"
  | ST5 -> "ST5"
  | ST6 -> "ST6"
  | ST7 -> "ST7"

let int_to_float_reg = function
    0 -> ST0
  | 1 -> ST1
  | 2 -> ST2
  | 3 -> ST3
  | 4 -> ST4
  | 5 -> ST5
  | 6 -> ST6
  | 7 -> ST7
  | _ -> raise (Invalid_argument "int_to_float_reg")

let mmx_reg_to_int = function
    MM0 -> 0
  | MM1 -> 1
  | MM2 -> 2
  | MM3 -> 3
  | MM4 -> 4
  | MM5 -> 5
  | MM6 -> 6
  | MM7 -> 7

let mmx_reg_to_string = function
    MM0 -> "MM0"
  | MM1 -> "MM1"
  | MM2 -> "MM2"
  | MM3 -> "MM3"
  | MM4 -> "MM4"
  | MM5 -> "MM5"
  | MM6 -> "MM6"
  | MM7 -> "MM7"

let int_to_mmx_reg = function
    0 -> MM0
  | 1 -> MM1
  | 2 -> MM2
  | 3 -> MM3
  | 4 -> MM4
  | 5 -> MM5
  | 6 -> MM6
  | 7 -> MM7
  | _ -> raise (Invalid_argument "int_to_mmx_reg")

let control_reg_to_int = function
    CR0 -> 0
  | CR2 -> 2
  | CR3 -> 3
  | CR4 -> 4

let control_reg_to_string = function
    CR0 -> "CR0"
  | CR2 -> "CR2"
  | CR3 -> "CR3"
  | CR4 -> "CR4"

let int_to_control_reg = function
    0 -> CR0
  | 2 -> CR2
  | 3 -> CR3
  | 4 -> CR4
  | _ -> raise (Invalid_argument "int_to_control_reg")

let debug_reg_to_int = function
    DR0 -> 0
  | DR1 -> 1
  | DR2 -> 2
  | DR3 -> 3
  | DR6 -> 6
  | DR7 -> 7

let debug_reg_to_string = function
    DR0 -> "DR0"
  | DR1 -> "DR1"
  | DR2 -> "DR2"
  | DR3 -> "DR3"
  | DR6 -> "DR6"
  | DR7 -> "DR7"

let int_to_debug_reg = function
    0 -> DR0
  | 1 -> DR1
  | 2 -> DR2
  | 3 -> DR3
  | 6 -> DR6
  | 7 -> DR7
  | _ -> raise (Invalid_argument "int_to_debug_reg")

let test_reg_to_int = function
    TR3 -> 3
  | TR4 -> 4
  | TR5 -> 5
  | TR6 -> 6
  | TR7 -> 7

let test_reg_to_string = function
    TR3 -> "TR3"
  | TR4 -> "TR4"
  | TR5 -> "TR5"
  | TR6 -> "TR6"
  | TR7 -> "TR7"

let int_to_test_reg = function
    3 -> TR3
  | 4 -> TR4
  | 5 -> TR5
  | 6 -> TR6
  | 7 -> TR7
  | _ -> raise (Invalid_argument "int_to_test_reg")

let flag_to_int = function
    ID -> 0
  | VIP -> 1
  | VIF -> 2
  | AC -> 3
  | VM -> 4
  | RF -> 5
  | NT -> 6
  | IOPL -> 7
  | OF -> 8
  | DF -> 9
  | IF_flag -> 10
  | TF -> 11
  | SF -> 12
  | ZF -> 13
  | AF -> 14
  | PF -> 15
  | CF -> 16
 
let int_to_flag = function
  |  0 ->   ID
  |  1 ->  VIP
  |  2 ->  VIF
  |  3 ->  AC
  |  4 ->  VM
  |  5 ->  RF
  |  6 ->  NT
  |  7 ->  IOPL
  |  8 ->  OF
  |  9 ->  DF
  |  10 ->  IF_flag
  |  11 ->  TF
  |  12 ->  SF
  |  13 ->  ZF
  |  14 ->  AF
  |  15 ->  PF
  |  16 ->  CF
  | _ -> raise (Invalid_argument "int_to_flag")

let flag_to_string = function  
  |  ID -> "ID"
  |  VIP -> "VIP"
  |  VIF -> "VIF"
  |  AC -> "AC"
  |  VM -> "VM"
  |  RF -> "RF"
  |  NT -> "NT"
  |  IOPL -> "IOPL"
  |  OF -> "OF"
  |  DF -> "DF"
  |  IF_flag -> "IF_flag"
  |  TF -> "TF"
  |  SF -> "SF"
  |  ZF -> "ZF"
  |  AF -> "AF"
  |  PF -> "PF"
  |  CF -> "CF"


let condition_to_int = function
    O -> 0
  | B -> 2
  | Z -> 4
  | BE -> 6
  | S -> 8
  | P -> 10
  | L -> 12
  | LE -> 14

let cc_to_int (truth, f) =
  if truth then
    condition_to_int f
  else
    1 + condition_to_int f

let cc_to_string = function
    (true, O) -> "O"
  | (false, O) -> "NO"
  | (true, B) -> "B"
  | (false, B) -> "AE"
  | (true, Z) -> "Z"
  | (false, Z) -> "NZ"
  | (true, BE) -> "BE"
  | (false, BE) -> "A"
  | (true, S) -> "S"
  | (false, S) -> "NE"
  | (true, P) -> "P"
  | (false, P) -> "NP"
  | (true, L) -> "L"
  | (false, L) -> "GE"
  | (true, LE) -> "LE"
  | (false, LE) -> "G"

let condition_to_string f = cc_to_string (true, f)

let int_to_condition = function
    0 -> O
  | 2 -> B
  | 4 -> Z
  | 6 -> BE
  | 8 -> S
  | 10 -> P
  | 12 -> L
  | 14 -> LE
  | x -> raise (Invalid_argument (Printf.sprintf "int_to_condition %d" x))

let int_to_cc n =
  if n mod 2 = 0 then
    (true, int_to_condition n)
  else
    (false, int_to_condition (n-1))

let sse_to_int = function
    SseEQ -> 0
  | SseLT -> 1
  | SseLE -> 2
  | SseUNORD -> 3
  | SseNEQ -> 4
  | SseNLT -> 5
  | SseNLE -> 6
  | SseORD -> 7

let sse_to_string = function
    SseEQ -> "EQ"
  | SseLT -> "LT"
  | SseLE -> "LE"
  | SseUNORD -> "UNORD"
  | SseNEQ -> "NEQ"
  | SseNLT -> "NLT"
  | SseNLE -> "NLE"
  | SseORD -> "ORD"

let int_to_sse = function
    0 -> SseEQ
  | 1 -> SseLT
  | 2 -> SseLE
  | 3 -> SseUNORD
  | 4 -> SseNEQ
  | 5 -> SseNLT
  | 6 -> SseNLE
  | 7 -> SseORD
  | _ -> raise (Invalid_argument "int_to_sse")

let scale_to_size = function
    Scale1 -> 1
  | Scale2 -> 2
  | Scale4 -> 4
  | Scale8 -> 8

let scale_to_int = function
    Scale1 -> 0
  | Scale2 -> 1
  | Scale4 -> 2
  | Scale8 -> 3

let scale_to_string scale =
  string_of_int (scale_to_size scale)

let int_to_scale = function
    0 -> Scale1
  | 1 -> Scale2
  | 2 -> Scale4
  | 3 -> Scale8
  | _ -> raise (Invalid_argument "scale_from_int")

let arith_op_to_string = function
    Add -> "ADD"
  | Addc -> "ADC"
  | And -> "AND"
  | CmpOp -> "CMP"
  | Or -> "OR"
  | Sub -> "SUB"
  | Subb -> "SBB"
  | Xor -> "XOR"

let arith_op_to_int = function
    Add -> 0
  | Addc -> 2
  | And -> 4
  | CmpOp -> 7
  | Or -> 1
  | Sub -> 5
  | Subb -> 3
  | Xor -> 6

let int_to_arith_op = function
    0 -> Add
  | 1 -> Or
  | 2 -> Addc 
  | 3 -> Subb
  | 4 -> And
  | 5 -> Sub
  | 6 -> Xor
  | 7 -> CmpOp
  | n ->
      Printf.printf "n = %d\n" n;
      raise (Invalid_argument "int_to_arith_op")

let shift_op_to_string = function
    Rol -> "ROL"
  | Ror -> "ROR"
  | Shl -> "SHL"
  | Shr -> "SHR"
  | Sar -> "SAR"

let shift_op_to_int = function
    Rol -> 0
  | Ror -> 1
  | Shl -> 4
  | Shr -> 5
  | Sar -> 7

let int_to_shift_op = function
    0 -> Rol
  | 1 -> Ror
  | 4 -> Shl
  | 5 -> Shr
  | 7 -> Sar
  | x -> raise (Invalid_argument (Printf.sprintf "int_to_shift_op: Invalid argument %d" x))

let read_rm_with_spare int_to_reg bits seg_override =
  let rm, bits = read_uint bits 3 in
  let spare, bits = read_uint bits 3 in
  let modb, bits = read_uint bits 2 in
  if modb = 3 then Reg (int_to_reg rm), bits, spare
  else 
    let base, index, bits = 
      if rm = 4 (* case with SIB byte *) then
        let base, bits = read_uint bits 3 in
	let index, bits = read_uint bits 3 in
	let scale, bits = read_uint bits 2 in
        if index = 4 then base, None, bits
        else base, Some(int_to_scale scale, int_to_reg32 index), bits
      else rm, None, bits in
    let disp, base, bits = match modb, base with
      0,5 -> let disp, bits = read_int32 bits 32 in
        disp, None, bits
    | 0,_ -> Int64.zero, Some(int_to_reg32 base), bits
    | 1,_ -> let disp, bits = read_uint32_extend bits 8 in
        disp, Some(int_to_reg32 base), bits
    | 2,_ -> let disp, bits = read_int32 bits 32 in
        disp, Some(int_to_reg32 base), bits
    | _,_ -> failwith "Unexpected modb" in
    Address { addrDisp = disp;
              addrBase = base;
              addrIndex = index;
              segBase = seg_override}, bits, spare

let read_rm32_with_spare = read_rm_with_spare int_to_reg32
let read_rm8_with_spare = read_rm_with_spare int_to_reg8
  
let read_rm reg_to_int bits =
  let ans, bits, spare = read_rm_with_spare reg_to_int bits None in
  ans, bits
let read_rm32 bits =
  let ans, bits, spare = read_rm32_with_spare bits None in
  ans, bits
let read_rm8 bits =
  let ans, bits, spare = read_rm8_with_spare bits None in
  ans, bits
