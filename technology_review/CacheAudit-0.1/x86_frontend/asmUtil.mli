(* Copyright (c) 2005, Regents of the University of California
 * All rights reserved.
 *
 * Author: Adam Chlipala 
 * Extended by: Goran Doychev, Ignacio Echeverria, Boris Koepf, Laurent Mauborgne
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

(** Assembly parsing utilities *)

type bits
(** A bit source to use with functional IO *)

(** {6 Creating bit sources} *)

val bits : int64 array -> bits
(** Build a bit source from an array of 32-bit integers, represented with
   extra bits. *)

val read_from_channel : in_channel -> bits
val read_from_file : string -> bits
(** Create a bit source from a channel or a filename. *)

(** {6 Basic input} *)

val more : bits -> bool
(** Are there any bits left to read from this source? *)

val get_byte : bits -> int
(** What byte number in the source we have already read upto *)

val skip : bits -> int -> bits
(** Skip ahead a number of bits *)

val goto : bits -> int -> bits
(** Sets the current address to the second argument. This address is the number of bytes since beginning of file *)
(** {6 Reading integers} *)

val read_uint : bits -> int -> int * bits
val read_int : bits -> int -> int * bits
(** Read the specified number of bits from a bit source, returning the unsigned
   or signed integer we've read and the modified bit source.
   This won't cross 32-bit word boundaries.
 *)

val read_uint32 : bits -> int -> int64 * bits
val read_uint32_extend : bits -> int -> int64 * bits
val read_int32 : bits -> int -> int64 * bits
(** We take the easy way out and use [int64] here so that we can use the same
   type for both signed and unsigned values.
   The difference between the first two is that [read_uint32] zero-extends,
   while [read_uint32_extend] sign-extends.
 *)


val write_int32 : bits -> int -> int64 -> bits


val read_string : bits -> string * bits
(** Read a zero-terminated string. *)

val off_to_int : int64 -> int
(* Translates an Int64 into int, assuming this is positive and not too big *)
