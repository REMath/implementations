(* Copyright (c) 2005, Regents of the University of California
 * All rights reserved.
 *
 * Author: Adam Chlipala
 * Extended by: Goran Doychev, Laurent Mauborgne, Ignacio Echeverria
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

(** Utility functions *)

open AsmUtil
open X86Types

(** {6 Conversion functions} *)

(** In this module, a function [X_to_int] converts an [X] into its x86
   machine language integer representation, a function [X_to_string] converts an
   [X] into a human-readable string, and a function [int_to_X] reverses the
   operation of [X_to_int].
 *)

val reg8_to_int : reg8 -> int
val reg8_to_string : reg8 -> string
val int_to_reg8 : int -> reg8

val reg16_to_int : reg16 -> int
val reg16_to_string : reg16 -> string
val int_to_reg16 : int -> reg16

val reg32_to_int : reg32 -> int
val reg32_to_string : reg32 -> string
val int_to_reg32 : int -> reg32
val string_to_reg32 : string -> reg32

val segment_reg_to_int : segment_reg -> int
val segment_reg_to_string : segment_reg -> string
val int_to_segment_reg : int -> segment_reg

val float_reg_to_int : float_reg -> int
val float_reg_to_string : float_reg -> string
val int_to_float_reg : int -> float_reg

val mmx_reg_to_int : mmx_reg -> int
val mmx_reg_to_string : mmx_reg -> string
val int_to_mmx_reg : int -> mmx_reg

val control_reg_to_int : control_reg -> int
val control_reg_to_string : control_reg -> string
val int_to_control_reg : int -> control_reg

val debug_reg_to_int : debug_reg -> int
val debug_reg_to_string : debug_reg -> string
val int_to_debug_reg : int -> debug_reg

val test_reg_to_int : test_reg -> int
val test_reg_to_string : test_reg -> string
val int_to_test_reg : int -> test_reg

val flag_to_int : flag -> int
val int_to_flag : int -> flag
val flag_to_string : flag -> string


val condition_to_int : condition -> int
val condition_to_string : condition -> string
val int_to_condition : int -> condition

val cc_to_int : cc -> int
val cc_to_string : cc -> string
val int_to_cc : int -> cc

val sse_to_int : sse -> int
val sse_to_string : sse -> string
val int_to_sse : int -> sse

val scale_to_size : scale -> int
val scale_to_int : scale -> int
val scale_to_string : scale -> string
val int_to_scale : int -> scale

val arith_op_to_int : arith_op -> int
val arith_op_to_string : arith_op -> string
val int_to_arith_op : int -> arith_op

val shift_op_to_int : shift_op -> int
val shift_op_to_string : shift_op -> string
val int_to_shift_op : int -> shift_op


(** {6 x86 register/memory operands} *)

val read_rm : (int -> 'a) -> bits -> 'a genop * bits
(** Read a register-or-memory operand, given a way to convert integers to
   registers. *)

val read_rm32 : bits -> op32 * bits
val read_rm8 : bits -> op8 * bits
(** Specialized versions for particular register sets *)

val read_rm_with_spare : (int -> 'a) -> bits -> segment_reg option -> 'a genop * bits * int
(** Like [read_rm], but also tells you the contents of the "spare" bits of the
   r/m byte.
 *)

val read_rm32_with_spare : bits -> segment_reg option -> op32 * bits * int
val read_rm8_with_spare : bits -> segment_reg option -> op8 * bits * int
