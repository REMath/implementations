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

(* Assembly parsing utilities *)

type bits = int64 array * int

let bits arr = (arr, 0)

let get_byte (_, pos) = pos / 8

let _read_int32 inf =
  let rec read n acc =
    if n = 0 then
      acc
    else
      try read (n-1) (input_byte inf :: acc)
      with End_of_file ->
	if n = 4 then
	  raise End_of_file
	else
	  acc in
  let bytes = read 4 [] in
  List.fold_left (fun n byte ->
    Int64.add (Int64.of_int byte) (Int64.shift_left n 8)) Int64.zero bytes

let read_int32s inf =
  let rec read acc =
    let n = try
      Some (_read_int32 inf)
    with End_of_file -> None in
    match n with
      None -> Array.of_list (List.rev acc)
    | Some n -> read (n :: acc) in
  read []

let read_from_channel inf = bits (read_int32s inf)
let read_from_file fname =
  let inf = open_in_bin fname in
  let res = read_from_channel inf in
  close_in inf;
  res

let more (arr, pos) =
  let word = pos / 32 in
  word < Array.length arr

let width_mask len =
  Int64.sub (Int64.shift_left Int64.one len) Int64.one

let skip (arr, pos) n = (arr, pos+n)

let goto (arr, pos) addr = (arr, addr*8)

let truncate len n =
  Int64.logand n (width_mask len)

let read_int32' extender (arr, pos) len =
  if len > 32 then
    raise (Invalid_argument "read_int32': can't read more than 32 bits");

  let word = pos / 32 in
  let bit = pos mod 32 in

  if word >= Array.length arr then
    raise (Invalid_argument "read_int32': reading past end of bit source");

  let left = 32 - bit in
  let v = if left < len then begin
    if word+1 >= Array.length arr then
      raise (Invalid_argument "read_int32': reading past end of bit source");

    let lowWord = truncate left (Int64.shift_right arr.(word) bit) in

    let inHighWord = len - left in
    let highWord = truncate inHighWord arr.(word+1) in

    Int64.add lowWord (Int64.shift_left highWord left)
  end else
    truncate len (Int64.shift_right arr.(word) bit) in
  extender len v,
  (arr, pos+len)

let write_int32' (arr, pos) len value =
  if len > 32 then
    raise (Invalid_argument "write_int32': can't write more than 32 bits");

  let word = pos / 32 in
  let bit = pos mod 32 in

  if word >= Array.length arr then
    raise (Invalid_argument "write_int32': writing past end of bit source");

  let left = 32 - bit in
  if left < len then begin
    if word+1 >= Array.length arr then
      raise (Invalid_argument "write_int32': writing past end of bit source");

    arr.(word) <- Int64.logor (truncate bit arr.(word)) (truncate 32 (Int64.shift_left value bit));

    let inHighWord = len - left in
    let highWord = Int64.shift_right value left in
    arr.(word+1) <- Int64.logor (Int64.shift_left arr.(word+1) inHighWord) (truncate inHighWord highWord)
  end else begin
    let nVal = truncate 32 (Int64.shift_left (truncate len value) bit) in
    let mask = Int64.lognot (Int64.shift_left (width_mask len) bit) in
    arr.(word) <- Int64.logor (Int64.logand mask arr.(word)) nVal
  end;
  (arr, pos+len)

let write_int32 = write_int32'

let read_uint32 = read_int32' (fun len x -> x)
let read_uint32_extend = read_int32'
    (fun len x ->
      if Int64.logand x (Int64.shift_left Int64.one (len-1)) = Int64.zero then
	x
      else
	let mask = Int64.lognot (Int64.shift_left Int64.minus_one (64 - len)) in
	let mask = Int64.shift_left mask len in
	Int64.logor x mask)
    
let read_int32 = read_int32' (fun len x ->
  if Int64.logand x (Int64.shift_left Int64.one (len-1)) = Int64.zero then
    x
  else
    let neg1 = Int64.lognot (Int64.shift_left Int64.minus_one len) in
    Int64.neg (Int64.add (Int64.sub neg1 x) Int64.one))

let read_uint bits len =
  let ans, bits = read_uint32 bits len in
  Int64.to_int ans, bits

let read_int bits len =
  let ans, bits = read_int32 bits len in
  Int64.to_int ans, bits

let read_string bits =
  let rec loop bits chars =
    let ch, bits = read_uint bits 8 in
    if ch = 0 then
      String.concat "" (List.rev chars), bits
    else
      loop bits (String.make 1 (Char.chr ch) :: chars) in
  loop bits []

(* Translates an Int64 into int, assuming this is positive and not too big *)
let off_to_int off = if off < Int64.zero then failwith "Negative offset"
  else if off > (Int64.of_int max_int) then ( Format.printf "Offset 0x%Lx " off; failwith "Offset too big")
  else Int64.to_int off


