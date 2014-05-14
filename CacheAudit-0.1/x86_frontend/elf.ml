(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

(* Data structures and parsing of elf files *)

(* Module parameters *******************************************************)
let check = ref true

(* Types used to store all relevent informations ****************************)
type elf32_addr = Int64.t (* 4 bytes unsigned *)
type elf32_half = int         (* 2 bytes unsigned *)
type elf32_off  = Int64.t (* 4 bytes unsigned *)
type elf32_sword = Nativeint.t (* 4 bytes, signed *)
type elf32_word = Int64.t
type elf32_char = char

type elf_type = 
  Et_none (* no file type *)
| Et_rel  (* Relocatable file *)
| Et_exec (* Executable file *)
| Et_dyn  (* Shared object file *)
| Et_other

type elf_ident_class = Elfclassnone | Elfclass32 | Elfclass64

type elf_ident_data = 
  Elfdatanone  (* invalid encosinf *)
| Elfdata2lsb  (* little endian *)
| Elfdata2msb  (* big endian *)

type elf_ident = {
(*  ei_magic is a constant, should be 0x7f folowwed by "ELF" *)
  ei_class : elf_ident_class;
  ei_data  : elf_ident_data;
}

type elf_header = {
  e_ident : elf_ident;
  e_type  : elf_type;
  e_entry : elf32_addr; (*the virtual address to which the system first 
                          transfers control *)
  e_phoff : int; (* offset of program header table *)
  e_shoff : int; (* offset of section header table *)
  e_phnum : int; (* the number of entries in the program header table *)
  e_shstrndx : elf32_half; (* section header table index of the entry associated with the section name string table *)
}

type elf32_shdr = {
  sh_name : string; (* read through an index into the string table *)
  sh_type : elf32_word;
  sh_addr : elf32_addr;
  sh_offset : int;
(* and more *)
}

type elf32_phdr = {
  p_offset: int;
  p_vaddr : elf32_addr;
  p_filesz: int; (* size of the segmet on the file *)
  p_memsz : int; (* file of the segment when mapped in memory *)
  p_lastaddr : elf32_addr; (* first address outside of segment *)
(* and more *)
}
type objectFile = {
  elf_header     : elf_header;
  program_header : elf32_phdr list;
  section_header : elf32_shdr list
}

type t = objectFile

(* A few printing functions, to help debugging *******************************)
open Format
open X86Print

let pp_elf_type fmt = function
  Et_none -> pp_print_string fmt "No file type"
| Et_rel  -> pp_print_string fmt "Relocatable file"
| Et_exec -> pp_print_string fmt "Executable file"
| Et_dyn  -> pp_print_string fmt "Shared object file"
| Et_other -> pp_print_string fmt "Other file type"

let pp_elf_ident_class fmt = function
  Elfclassnone -> pp_print_string fmt "unknown"
| Elfclass32 -> pp_print_string fmt "32 bits"
| Elfclass64 -> pp_print_string fmt "64 bits"

let pp_elf_ident_data fmt = function
  Elfdatanone -> pp_print_string fmt "invalid encoding"
| Elfdata2lsb -> pp_print_string fmt "little endian"
| Elfdata2msb -> pp_print_string fmt "big endian"

let pp_elf_ident fmt x = fprintf fmt "@[Class %a @,Data encoding: %a@]" pp_elf_ident_class x.ei_class pp_elf_ident_data x.ei_data

let pp_elf_header fmt x = fprintf fmt "@[%a@\nType of file: %a@\nEntry point address: %a@\nStart of program headers: %d (bytes into file)@\nStart of section header: %d (bytes into file)@\nNumber of program headers: %d@]"
pp_elf_ident x.e_ident
pp_elf_type x.e_type
pp_addr x.e_entry
x.e_phoff x.e_shoff x.e_phnum

let print_elf_header = pp_elf_header std_formatter

(* Now the parsing ***********************************************************)

exception NonElfFile

open AsmUtil

let parse_ident bits =
  let mag0, bits = read_uint bits 8 in
  let mag1, bits = read_uint bits 8 in
  let mag2, bits = read_uint bits 8 in
  let mag3, bits = read_uint bits 8 in
  if mag0 != 0x7f || mag1 != Char.code 'E' || mag2 != Char.code 'L'
                  || mag3 != Char.code 'F'
  then raise NonElfFile;
  let ei_class, bits = read_uint bits 8 in
  let ei_data, bits = read_uint bits 8 in
  let ei_version, _ = read_uint bits 8 in
  if !check&&(ei_version != 1) then
    failwith ("Incorrect version number "^(string_of_int ei_version));
  { ei_class = (match ei_class with
        1 -> Elfclass32
      | 2 -> if !check then failwith "64 bits executable not supported\n"
              else Elfclass64
      | _ -> if !check then failwith "Invalid executable class\n"
              else Elfclassnone
      );
    ei_data = (match ei_data with
        1 -> Elfdata2lsb
      | 2 -> if !check then failwith "Big endianness not supported\n"
              else Elfdata2msb
      | _ -> if !check then failwith "Invalid data encoding\n"
              else Elfdatanone
      );
  }

let parse_header bits =
  let e_ident = parse_ident bits in
  let e_type, bits = read_uint (goto bits 16) 16 in
  let e_machine, bits = read_uint bits 16 in
  let e_version, bits = read_uint32 bits 32 in
  let e_entry, bits = read_uint32 bits 32 in
  let e_phoff, bits = read_uint32 bits 32 in
  let e_shoff, bits = read_uint32 bits 32 in
  let e_flags, bits = read_uint32 bits 32 in
  let e_ehsize, bits = read_uint bits 16 in
  let e_phentsize, bits = read_uint bits 16 in
  let e_phnum, bits = read_uint bits 16 in
  let e_shentsize, bits = read_uint bits 16 in
  let e_shnum, bits = read_uint bits 16 in
  let e_shstrndx, bits = read_uint bits 16 in
  { e_ident = e_ident;
    e_type = (match e_type with
        0 -> Et_none
      | 1 -> Et_rel
      | 2 -> Et_exec
      | 3 -> Et_dyn
      | _ -> Et_other
      );
    e_entry = e_entry;
    e_phoff = off_to_int e_phoff;
    e_shoff = off_to_int e_shoff;
    e_phnum = e_phnum;
    e_shstrndx = e_shstrndx;
}

let parse_ph bits =
  let p_type, bits = read_uint32 bits 32 in
  let p_offset, bits = read_uint32 bits 32 in
  let p_vaddr, bits = read_uint32 bits 32 in
  let p_paddr, bits = read_uint32 bits 32 in
  let p_filesz, bits = read_uint32 bits 32 in
  let p_memsz, bits = read_uint32 bits 32 in
  let p_flags, bits = read_uint32 bits 32 in
  let p_align, bits = read_uint32 bits 32 in
  { p_offset = off_to_int p_offset;
    p_vaddr  = p_vaddr;
    p_filesz = off_to_int p_filesz;
    p_memsz = off_to_int p_memsz;
    p_lastaddr = Int64.add p_vaddr p_memsz;
  }, bits

let rec parse_phtable n bits acc =
  if n>0 then
    let ph, bits = parse_ph bits in
    parse_phtable (n-1) bits (ph::acc)
  else List.rev acc

let parse bits =
  let bits = goto bits 0 in
  let header = parse_header bits in
  let bits_ph = goto bits header.e_phoff in
  Printf.printf "Number of program headers: %d\n" header.e_phnum;
  { elf_header = header;
    program_header = parse_phtable header.e_phnum bits_ph [];
    section_header = [];
  }

let read file = parse (read_from_file file)

let virtual_start e = e.elf_header.e_entry

open ExecInterfaces

let sections e = List.map (fun s -> 
      { start_addr = s.p_vaddr;
        end_addr = s.p_lastaddr;
        offset = s.p_offset;
        max_valid_offset = s.p_offset + s.p_filesz;
      }) e.program_header
