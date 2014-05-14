(*===========================================================================
  PE/COFF generation

  We expect the following information:

  * imageBase:DWORD
    The location at which the image should be loaded

  * imports: seq DLLImports
    For each DLL that's imported, its name and a sequence of import entries

  * data: program
    Assembles to produce a data section with no reference to code.

  * code: DWORD -> seq (seq DWORD) -> program
    Given the base address of the data section, and addresses for each of the imports,
    produce the code section.

  From data we calculate the size (exact, and rounded up to page size, call it D)
  We place the data at RVA 0x1000, and the code at RVA D+0x1000. Entry point is
  assumed to coincide with the start of the code.

  Currently we emit an executable with three sections (code, data and imports), but with
  no exports or base relocations.
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program programassem cursor.
Require Import Ascii String.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive TargetType :=
| DLL
| EXE
.

Inductive ImportEntry :=
| ImportByOrdinal of nat
| ImportByName of string.

Record DLLImport := {
  DLLImport_name: string;
  DLLImport_entries: seq ImportEntry
}.

Record DLLExport := {
  DLLExport_name: string;
  DLLExport_addr: DWORD
}.

Fixpoint mkDLLExport (l : exportList) : seq DLLExport :=
  if l is (name, addr) :: rest
  then Build_DLLExport name addr :: mkDLLExport rest
  else [::].

(* We need character, string and byte sequence writers *)
Instance charWriter : Writer ascii :=
  fun c => writeBYTE #(nat_of_ascii c).

Instance stringWriter : Writer string :=
  fix sw s :=
    if s is String c s
    then do! writeNext c; sw s
    else retn tt.

(* Section 2.1: MSDOS Stub *)
(* This is the minimal stub taken from the "Tiny PE" *)
Definition MSDOSStub: program :=
LOCAL START; LOCAL END;
START:;;
  ds "MZ"%string;;
  pad 58;;
  dd (subB END START);;
END:;.

(* Section 2.2: Signature *)
Definition PEsig:program :=
  ds "PE"%string;;
  dw #0.

(* Section 2.3: COFF File Header *)
Definition makeCOFFFileHeader
  (Machine: WORD)
  (NumberOfSections: nat)
  (TimeDateStamp: DWORD)
  (PointerToSymbolTable: DWORD)
  (NumberOfSymbols: nat)
  (SizeOfOptionalHeader: WORD)
  (Characteristics: WORD) : program :=

  dw Machine;;
  dw #NumberOfSections;;
  dd TimeDateStamp;;
  dd PointerToSymbolTable;;
  dd #NumberOfSymbols;;
  dw SizeOfOptionalHeader;;
  dw Characteristics.

(* Section 2.3.1: Machine types *)
Definition IMAGE_FILE_MACHINE_i386 := #x"014c".

(* Section 2.3.2: Characteristics. We omit deprecated flags *)
Definition IMAGE_FILE_RELOCS_STRIPPED     := #x"0001".
Definition IMAGE_FILE_EXECUTABLE_IMAGE    := #x"0002".
Definition IMAGE_FILE_LARGE_ADDRESS_AWARE := #x"0020".
Definition IMAGE_FILE_32BIT_MACHINE       := #x"0100".
Definition IMAGE_FILE_DEBUG_STRIPPED      := #x"0200".
Definition IMAGE_FILE_SYSTEM              := #x"1000".
Definition IMAGE_FILE_DLL                 := #x"2000".
Definition IMAGE_FILE_UP_SYSTEM_ONLY      := #x"4000".

(* Windows Subsystem *)
Definition IMAGE_SUBSYSTEM_NATIVE := 1.
Definition IMAGE_SUBSYSTEM_WINDOWS_GUI := 2.
Definition IMAGE_SUBSYSTEM_WINDOWS_CUI := 3.

(* DLL Characteristics *)
Definition IMAGE_DLL_CHARACTERISTICS_DYNAMIC_BASE    := #x"0040".
Definition IMAGE_DLL_CHARACTERISTICS_FORCE_INTEGRITY := #x"0080".
Definition IMAGE_DLL_CHARACTERISTICS_NX_COMPAT       := #x"0100".
Definition IMAGE_DLL_CHARACTERISTICS_NO_ISOLATION    := #x"0200".
Definition IMAGE_DLL_CHARACTERISTICS_NO_SEH          := #x"0400".
Definition IMAGE_DLL_CHARACTERISTICS_NO_BIND         := #x"0800".
Definition IMAGE_DLL_CHARACTERISTICS_TERMINAL_SERVER_AWARE := #x"8000".

Definition makeMinimalHeader (targetType : TargetType) numberOfSections opthdrsize :=
  makeCOFFFileHeader
    IMAGE_FILE_MACHINE_i386
    numberOfSections (* Number of sections *)
    #0             (* Timestamp *)
    #0             (* Symbol table *)
    0              (* Number of symbols *)
    opthdrsize     (* Size of optional header *)
    (foldr orB #0
      [:: IMAGE_FILE_32BIT_MACHINE
        ; IMAGE_FILE_EXECUTABLE_IMAGE (* this is needed for DLLs too *)
        ; if targetType is DLL then IMAGE_FILE_DLL else #x"0000"
        ; IMAGE_FILE_RELOCS_STRIPPED
      ]).

Record Version := {majorVersion: WORD;
                   minorVersion: WORD}.
Instance writeVersion: Writer Version := fun v =>
  do! writeNext (majorVersion v); writeNext (minorVersion v).

Definition dv (v: Version) : program :=
  dw (majorVersion v);;
  dw (minorVersion v).

(* Section 2.4: Optional header *)
Definition makeOptionalHeader
  (Magic: WORD)
  (MajorLinkerVersion MinorLinkerVersion: BYTE)
  (SizeOfCode SizeOfInitializedData SizeOfUninitializedData: DWORD)
  (AddressOfEntryPoint: DWORD)
  (BaseOfCode BaseOfData: DWORD)
  (ImageBase: DWORD)
  (SectionAlignment: DWORD)
  (FileAlignment: DWORD)
  (OperatingSystemVersion ImageVersion SubsystemVersion: Version)
  (Win32VersionValue: DWORD)
  (SizeOfImage: DWORD)
  (SizeOfHeaders: DWORD)
  (CheckSum: DWORD)
  (Subsystem: WORD)
  (DllCharacteristics: WORD)
  (SizeOfStackReserve SizeOfStackCommit: DWORD)
  (SizeOfHeapReserve  SizeOfHeapCommit: DWORD)
  (LoaderFlags: DWORD)
  (NumberOfRvaAndSizes: DWORD) : program :=
  dw Magic;;
  db MajorLinkerVersion;; db MinorLinkerVersion;;
  dd SizeOfCode;; dd SizeOfInitializedData;; dd SizeOfUninitializedData;;
  dd AddressOfEntryPoint;;
  dd BaseOfCode;; dd BaseOfData;;
  dd ImageBase;;
  dd SectionAlignment;; dd FileAlignment;;
  dv OperatingSystemVersion;; dv ImageVersion;; dv SubsystemVersion;;
  dd Win32VersionValue;;
  dd SizeOfImage;; dd SizeOfHeaders;;
  dd CheckSum;;
  dw Subsystem;;
  dw DllCharacteristics;;
  dd SizeOfStackReserve;; dd SizeOfStackCommit;;
  dd SizeOfHeapReserve;; dd SizeOfHeapCommit;;
  dd LoaderFlags;;
  dd NumberOfRvaAndSizes.

(* Alignment within the file can be on 512 byte boundaries *)
(* But this doesn't work yet because the assembler needs the file
   to match the memory layout *)
Definition fileAlignBits := 9.
Definition fileAlign: DWORD := iter fileAlignBits shlB #1.

(* Once mapped into memory the sections must be on 4K boundaries *)
Definition sectAlignBits := 12.
Definition sectAlign: DWORD := iter sectAlignBits shlB #1.

Definition makeMinimalOptionalHeader (targetType : TargetType)
  codestart datastart codesize datasize imagebase imagesize hdrsize :=
  makeOptionalHeader
    #x"010B"
    #11 #0       (* linker version *)
    codesize     (* size of code *)
    datasize     (* size of initialized data *)
    #0           (* size of uninitialized data *)
    (if targetType is EXE then codestart else #0)    (* entry point *)
    codestart    (* base of code *)
    datastart    (* base of data *)
    imagebase    (* image base *)
    sectAlign    (* section alignment *)
    fileAlign    (* file alignment *)
    (Build_Version #6 #0)  (* OS version *)
    (Build_Version #0 #0)  (* image version *)
    (Build_Version #6 #0)  (* subsystem version *)
    #0
    imagesize    (* size of image *)
    hdrsize
    #0
    #IMAGE_SUBSYSTEM_WINDOWS_CUI
    (foldr orB #0
      [:: IMAGE_DLL_CHARACTERISTICS_NO_SEH
        ; IMAGE_DLL_CHARACTERISTICS_NX_COMPAT
        ; if targetType is DLL then IMAGE_DLL_CHARACTERISTICS_DYNAMIC_BASE else #x"0000"
      ])
    #x"00100000"
    #x"00001000"
    #x"00100000"
    #x"00001000"
    #0
    #16.

(* Section 3: Section header. We truncate/zero-pad the string to 8 characters *)
Definition makeSectionHeader
  (Name: string)                             (* Will be truncated and zero-padded to 8 characters *)
  (VirtualSize: DWORD)                       (* Size when loaded into memory; can be greater than raw size *)
  (VirtualAddress: DWORD)                    (* Address when loaded into memory *)
  (SizeOfRawData: DWORD)                     (* Actual size in the file. Must be multiple of FileAlignment *)
  (PointerToRawData: DWORD)                  (* Address in the file. Must  be multiple of FileAlignment *)
  (PointerToRelocations PointerToLinenumbers: DWORD)  (* Zero for executable images *)
  (NumberOfRelocations NumberOfLinenumbers: WORD)     (* Zero for executable images *)
  (Characteristics: DWORD) :=                         (* Section Flags *)
  let truncated := substring 0 8 Name in
  let getByte i : BYTE := if get i truncated is Some c then fromNat (nat_of_ascii c) else #0 in

  db (getByte 0);; db (getByte 1);; db (getByte 2);; db (getByte 3);;
  db (getByte 4);; db (getByte 5);; db (getByte 6);; db (getByte 7);;
  dd VirtualSize;;
  dd VirtualAddress;;
  dd SizeOfRawData;;
  dd PointerToRawData;;
  dd PointerToRelocations;;
  dd PointerToLinenumbers;;
  dw NumberOfRelocations;;
  dw NumberOfLinenumbers;;
  dd Characteristics.

(* Section 3.1: Section Flags *)
Definition IMAGE_SCN_CNT_CODE               := #x"00000020".
Definition IMAGE_SCN_CNT_INITIALIZED_DATA   := #x"00000040".
Definition IMAGE_SCN_CNT_UNINITIALIZED_DATA := #x"00000080".
Definition IMAGE_SCN_MEM_DISCARDABLE        := #x"02000000".
Definition IMAGE_SCN_MEM_NOT_CACHED         := #x"04000000".
Definition IMAGE_SCN_MEM_NOT_PAGED          := #x"08000000".
Definition IMAGE_SCN_MEM_SHARED             := #x"10000000".
Definition IMAGE_SCN_MEM_EXECUTE            := #x"20000000".
Definition IMAGE_SCN_MEM_READ               := #x"40000000".
Definition IMAGE_SCN_MEM_WRITE              := #x"80000000".

Definition nextAligned {n} m (pos: BITS n) := pos +# (toNat (negB (lowWithZeroExtend m pos))).

(* Section 5: Special Sections *)

Definition makeCodeSectionHeader virtualSize virtualAddress rawsize rawaddr :=
  makeSectionHeader
    ".text"
    virtualSize
    virtualAddress
    rawsize
    rawaddr
    #0 #0 #0 #0
    (foldr orB #0
      [:: IMAGE_SCN_CNT_CODE; IMAGE_SCN_MEM_EXECUTE; IMAGE_SCN_MEM_READ ]).

Definition makeRDataSectionHeader virtualSize virtualAddress rawsize rawaddr :=
  makeSectionHeader
    ".rdata"
    virtualSize
    virtualAddress
    rawsize
    rawaddr
    #0 #0 #0 #0
    (foldr orB #0
      [:: IMAGE_SCN_CNT_INITIALIZED_DATA; IMAGE_SCN_MEM_READ ]).

Definition makeDataSectionHeader virtualSize virtualAddress rawsize rawaddr :=
  makeSectionHeader
    ".data"
    virtualSize
    virtualAddress
    rawsize
    rawaddr
    #0 #0 #0 #0
    (foldr orB #0
      [:: IMAGE_SCN_CNT_INITIALIZED_DATA; IMAGE_SCN_MEM_READ; IMAGE_SCN_MEM_WRITE ]).

Definition makeEDataSectionHeader virtualSize virtualAddress rawsize rawaddr :=
  makeSectionHeader
    ".edata"
    virtualSize
    virtualAddress
    rawsize
    rawaddr
    #0 #0 #0 #0
    (foldr orB #0
      [:: IMAGE_SCN_CNT_INITIALIZED_DATA; IMAGE_SCN_MEM_READ; IMAGE_SCN_MEM_WRITE ]).

Definition makeIDataSectionHeader virtualSize virtualAddress rawsize rawaddr :=
  makeSectionHeader
    ".idata"
    virtualSize
    virtualAddress
    rawsize
    rawaddr
    #0 #0 #0 #0
    (foldr orB #0
      [:: IMAGE_SCN_CNT_INITIALIZED_DATA; IMAGE_SCN_MEM_READ; IMAGE_SCN_MEM_WRITE ]).

Fixpoint makeString (s:string) :=
  if s is String c s
  then db #(nat_of_ascii c);; makeString s
  else db #0.

(* [kEAT] is the continuation program writing the beginning of the Export Address Table
   [kENPT] is the continuation program writing the beginning of the Export Name Pointer Table
   [kEOT] is the continuation program writing the beginning of the Export Ordinal Table
   The last 2 tables are built in reverse order so that name addresses appear in lexical order in the
   Export Name Pointer Table.
 *)
Fixpoint computeExportTables (exports: seq DLLExport) (kEAT kENPT kEOT : program) (ord : WORD) : program :=
  if exports is Build_DLLExport name addr :: exports
  then
    LOCAL NAME;
    computeExportTables
      exports
      (kEAT ;; dd addr)
      (dd NAME;; kENPT)
      (dw ord ;; kEOT)
      (addB ord #1);;
    NAME:;;
    makeString name
  else
    kEAT ;;
    kENPT;;
    kEOT .

Definition makeExportTables (exports : seq DLLExport) :=
  computeExportTables exports prog_skip prog_skip prog_skip
  (* the next field should be set to the ordinal base, according to what's shown
     in the example in the section 5.3 of the spec. However, in reality, tools
     seem to agree that this is #0-based.
     See: http://stackoverflow.com/questions/5653316
   *)
  #0
.

Definition makeExportDirectoryTable (nameRVA nbEntries EATRVA NPTRVA OTRVA : DWORD) :=
  dd #0;; (* Reserved *)
  dd #0;; (* Time stamp *)
  dw #0;; (* Major version *)
  dw #0;; (* Minor version *)
  dd nameRVA;; (* Name RVA *)
  dd #1;; (* Ordinal base *)
  dd nbEntries;; (* # of entries in Address Table *)
  dd nbEntries;; (* # of entries in Name Pointer and Ordinal Tables *)
  dd EATRVA;; (* EAT RVA *)
  dd NPTRVA;; (* NPT RVA *)
  dd OTRVA. (* OT RVA *)

(* We lay out the .idata section as follows.

     IAT (One DWORD per entry, with null at end, for each DLL)
     ILT (Exactly the same as the IAT)
     Import directory (5 DWORDs per DLL, with 5 nulls at the end)
     Strings
*)
Fixpoint computeIATaddressesForOneDLL (base: DWORD) n :=
  if n is n'.+1 then base::computeIATaddressesForOneDLL (base+#4) n'
  else [::].

Fixpoint computeIATaddresses (base: DWORD) (imports: seq DLLImport) :=
  if imports is import::imports
  then let n := List.length (DLLImport_entries import)
       in computeIATaddressesForOneDLL base n :: computeIATaddresses (base +# 4 * n.+1) imports
  else [::].

Fixpoint computeIATsize (imports: seq DLLImport) :=
  if imports is import::imports
  then (List.length (DLLImport_entries import) + 1) * 4 + computeIATsize imports
  else 0.

Fixpoint computeIAT (imports: seq DLLImport) (continueOuter: seq DWORD -> program) : program :=
  if imports is import::imports
  then
    (fix computeIATforOneDLL (entries: seq ImportEntry) (continue: seq DWORD -> program) :=
       if entries is entry::entries
       then
         match entry with
         | ImportByOrdinal n =>
           computeIATforOneDLL entries (fun res => continue (orB #x"80000000" #n :: res))

         | ImportByName n =>
           LOCAL NAME;
           computeIATforOneDLL entries (fun res => continue (NAME :: res));;
           NAME:;;
           dw #0;; (* hint *)
           makeString n;;
           align 1 (* align on even byte *)
         end
       else computeIAT imports (fun res => continue (#0 :: res))
    ) (DLLImport_entries import) continueOuter
  else continueOuter nil.

Example ex :=
    [::Build_DLLImport "USER32.DLL" [::ImportByName "MessageBoxA"; ImportByName "MessageBoxW"];
       Build_DLLImport "KERNEL32.DLL" [::ImportByName "ExitProcess"]].

Fixpoint makeIATproper (entries: seq DWORD) :=
  if entries is entry::entries then dd entry;; makeIATproper entries else prog_skip.

Definition makeIAT (imports: seq DLLImport) :=
  computeIAT imports (fun res => makeIATproper res;; makeIATproper res).

Definition makeImportDirectoryTableEntry (nameRVA ILTRVA IATRVA :DWORD) :=
  dd ILTRVA;;
  dd #0;; (* Time stamp *)
  dd #0;; (* Forwarder chain *)
  dd nameRVA;; (* Name RVA *)
  dd IATRVA. (* IAT RVA *)

Fixpoint makeImportDirectory (IAT ILT: DWORD) (imports: seq DLLImport) :=
  if imports is Build_DLLImport name entries::imports
  then
  let IATsize := 4*(List.length entries + 1) in
    (LOCAL NAME;
     makeImportDirectoryTableEntry NAME ILT IAT;;
     makeImportDirectory (IAT +# IATsize) (ILT +# IATsize) imports;;
     NAME:;; makeString name)
  else makeImportDirectoryTableEntry #0 #0 #0.

(* Given a sequence of bytes compute its size, file-aligned size, and section-aligned size *)
Definition computeSizes (bytes: seq BYTE) :=
let size:DWORD := #(List.length bytes)
in (size, nextAligned fileAlignBits size, nextAligned sectAlignBits size).

(* Section 4.2: COFF Relocations *)
Definition makePEfile
  (targetType : TargetType)
  (progName: string)
  (imageBase: DWORD)
  (imports: seq DLLImport)
  (data: program)
  (code: DWORD -> seq (seq DWORD) -> program) : seq BYTE :=

(***** .data *****)

let dataRelBase := sectAlign in
let dataBase := addB imageBase dataRelBase in
let dataBytes := assemble dataBase data in
let: (dataSize,dataSizeFileAligned,dataSizeSectionAligned) := computeSizes dataBytes in

(***** .idata *****)

(* We want the import address table (IAT) for each imported DLL to live at a well-known
   location in the image, so that the code can indirect through it. We choose to put it
   immediately after the directory table, which has a known size. *)
let countImports := List.length imports in
let importsRelBase := addB dataRelBase dataSizeSectionAligned in
let IATRelBase := importsRelBase in
let IATBase := addB imageBase IATRelBase in
let IATBytes := assemble IATRelBase (makeIAT imports) in
let IATSize := #(List.length IATBytes) in         (* the size of the IAT + the ILT *)
let IATProperSize := #(computeIATsize imports) in (* the size of just the IAT *)
let importsDirectoryRelBase := addB IATRelBase IATSize in
(* RVAs of each entry in the IAT, to be supplied to the code *)
let IATRVAs := computeIATaddresses IATBase imports in
let importsBytes :=
  IATBytes ++
  assemble importsDirectoryRelBase (makeImportDirectory IATRelBase (addB IATRelBase IATProperSize) imports) in
let: (importsSize, importsSizeFileAligned, importsSizeSectionAligned) :=
  computeSizes importsBytes in

(***** .text *****)

let codeProgram := code dataBase IATRVAs in
let codeRelBase := addB importsRelBase importsSizeSectionAligned in
let codeBase := addB imageBase codeRelBase in
let codeBytes := assemble codeBase codeProgram in
let: (codeSize, codeSizeFileAligned, codeSizeSectionAligned) := computeSizes codeBytes in

(***** .edata *****)

(* We could use (code #0 [::]) instead of codeProgram in this part of the code, but might
   as well reuse codeProgram since it's been computed already.
 *)
let exports := mkDLLExport (get_export_safe codeBase codeProgram) in
let countExports := List.length exports in
let exportsRelBase := addB codeRelBase codeSizeSectionAligned in

let progNameRelBase := exportsRelBase in
let progNameBytes := assemble progNameRelBase (makeString progName) in

let ETRelBase := progNameRelBase +# (List.length progNameBytes) in
let ETBase := addB imageBase ETRelBase in
let ETBytes := assemble ETRelBase (makeExportTables exports) in

let exportsDirectoryRelBase := ETRelBase +# (List.length ETBytes) in
let exportsDirectoryBytes := assemble exportsDirectoryRelBase
  (makeExportDirectoryTable
     progNameRelBase (* program name string RVA *)
     #(countExports)
     ETRelBase                                  (* EAT RVA *)
     (addB ETRelBase (mulB #4 #(countExports))) (* NPT RVA = EAT RVA + 4 * countExports *)
     (addB ETRelBase (mulB #8 #(countExports))) (* EOT RVA = NPT RVA + 4 * countExports *)
  ) in

let exportsBytes := progNameBytes ++ ETBytes ++ exportsDirectoryBytes in

let: (exportsSize, exportsSizeFileAligned, exportsSizeSectionAligned) :=
  computeSizes exportsBytes in


let imageSize :=
  (addB sectAlign
  (addB dataSizeSectionAligned
  (addB importsSizeSectionAligned
  (addB codeSizeSectionAligned
        exportsSizeSectionAligned
  )))) in

assemble #0
(
LOCAL HEADER; LOCAL SECTIONS; LOCAL START;
LOCAL DIRECTORIES; LOCAL ENDHEADERS;
START:;;
  MSDOSStub;;
  PEsig;;
  makeMinimalHeader targetType (* number of sections *) 4 (low 16 (subB SECTIONS HEADER));;
HEADER:;;
  makeMinimalOptionalHeader targetType codeRelBase dataRelBase codeSizeFileAligned dataSizeFileAligned
    imageBase imageSize (subB ENDHEADERS START);;
DIRECTORIES:;;
  (* Exports *)
  dd exportsDirectoryRelBase;; dd #40;;
  (* Imports *)
  dd importsDirectoryRelBase;; dd #(countImports.+1 * 5 * 4);;
  (* Resources *)
  dd #0;; dd #0;;
  (* Exceptions *)
  dd #0;; dd #0;;
  (* Certificates *)
  dd #0;; dd #0;;
  (* Base relocations *)
  dd #0;; dd #0;;
  (* Debug *)
  dd #0;; dd #0;;
  (* Architecture *)
  dd #0;; dd #0;;
  (* Global Ptr *)
  dd #0;; dd #0;;
  (* TLS Table *)
  dd #0;; dd #0;;
  (* Load Config *)
  dd #0;; dd #0;;
  (* Bound Import *)
  dd #0;; dd #0;;
  (* IAT *)
  dd IATRelBase;; dd IATSize;;
  (* Delay Import Descriptor *)
  dd #0;; dd #0;;
  (* CLR Runtime Header *)
  dd #0;; dd #0;;
  (* Reserved *)
  dd #0;; dd #0;;
SECTIONS:;;
  let current := fileAlign in
  makeDataSectionHeader dataSize dataRelBase dataSizeFileAligned current;;
  let current := addB dataSizeFileAligned    current in
  makeIDataSectionHeader importsSize importsRelBase importsSizeFileAligned current;;
  let current := addB importsSizeFileAligned current in
  makeCodeSectionHeader codeSize codeRelBase codeSizeFileAligned current;;
  let current := addB codeSizeFileAligned    current in
  makeEDataSectionHeader exportsSize exportsRelBase exportsSizeFileAligned current;;
  let current := addB exportsSizeFileAligned current in
  align fileAlignBits;;
ENDHEADERS:;
) ++
dataBytes    ++ nseq (toNat (subB dataSizeFileAligned    dataSize))    #0 ++
importsBytes ++ nseq (toNat (subB importsSizeFileAligned importsSize)) #0 ++
codeBytes    ++ nseq (toNat (subB codeSizeFileAligned    codeSize))    #0 ++
exportsBytes ++ nseq (toNat (subB exportsSizeFileAligned exportsSize)) #0.
