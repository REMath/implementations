(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

(* Executable infos, such as starting offset and translation from virtual addresses to offsets in the file  *)
open ExecInterfaces

type t = {
    start_offset : int;
    sections : section list ; (* TODO: a more efficient data structure *)
    bits : AsmUtil.bits;
  }

exception InvalidVirtualAddress
exception AddressNotInFile

let pp_section fmt sec = Format.fprintf fmt "@[section from 0x%Lx to 0x%Lx located at position %d in file@]" sec.start_addr sec.end_addr sec.offset

(* returns the section corresponding to a virtual address *)
let find_section sec addr = List.find (fun s -> 
    addr >= s.start_addr && addr < s.end_addr) sec

(* May raise InvalidVirtualAddress and AddressNotInFile*)
let virtual_to_offset x addr = 
  let s = try find_section x.sections addr
          with Not_found -> raise InvalidVirtualAddress in
(*  Format.printf "%a found for address 0x%Lx@\n" pp_section s addr;*)
  let res = AsmUtil.off_to_int (Int64.sub addr s.start_addr) + s.offset in
  if res<s.max_valid_offset then res else raise AddressNotInFile

let compute parse virtual_start sections bits =
  let internal = parse bits in
  Printf.printf "Start virtual address is 0x%Lx\n" (virtual_start internal);
  let res = 
    { start_offset = 0;
      sections = sections internal; 
      bits = bits
    } in
  (*List.iter (fun s -> pp_section Format.std_formatter s) res.sections;*)
  let so = try virtual_to_offset res (virtual_start internal)
  with InvalidVirtualAddress ->
    Format.printf "But start virtual address is not valid. Start offset will be 0\n";
    0
  in { res with start_offset = so }

let read_exec file =
  let bits = AsmUtil.read_from_file file in
  try compute Elf.parse Elf.virtual_start Elf.sections bits
  with Elf.NonElfFile -> 
    failwith "Only ELF executables supported"

let starting_offset x = x.start_offset

let get_bits x = x.bits

(* May raise InvalidVirtualAddress *)
let lookup mem addr = try
    let off = virtual_to_offset mem addr in
    fst (AsmUtil.read_uint32 (AsmUtil.goto mem.bits off) 32)
  with AddressNotInFile -> Int64.zero 

(* May raise InvalidVirtualAddress *)
let write mem addr len value = 
  let off = virtual_to_offset mem addr in
  let new_bits = AsmUtil.write_int32 (AsmUtil.goto mem.bits off) len value in
  { mem with bits = new_bits }
