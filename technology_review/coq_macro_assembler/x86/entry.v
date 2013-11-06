Require Import ssreflect seq finfun tuple fintype.
Require Import bitsrep bitsops mem reg instr instrsyntax encinstr.
Require Import program macros Ascii.

Local Open Scope instr_scope.

Definition sumEx := 
  LOCAL loopBody;
      MOV EAX, 1;;
      MOV EBX, 10;;
      XOR ECX, ECX;;
    loopBody:;;
      ADD ECX, EAX;;
      INC EAX;;
      CMP EAX, EBX;;
      JNZ loopBody
  .

Definition outEx :=
  LOCAL loopBody;
      MOV EAX, 1;;
      MOV EBX, 10;;
      XOR ECX, ECX;;
    loopBody:;;
      OUT false #50;;
      INC EAX;;
      CMP EAX, EBX;;
      JNZ loopBody
  .

Definition screenAddr:DWORD := #x"000b8000" +# 160*32.

Definition simpleScreenEx :=
  LOCAL busyBody;
    busyBody:;;
      MOV EDI, screenAddr;;
      MOV BYTE [EDI], #(nat_of_ascii "D");;
      MOV BYTE [EDI+1], #63;;
      JMP busyBody
  .

Definition prettyEx :=
  LOCAL loopBody;
  LOCAL busyBody;
      MOV EDI, screenAddr;;
      MOV EAX, 31;;
      MOV EBX, 255;;
    loopBody:;;
      MOV BYTE [EDI], #1;;                       
      INC EDI;;
      MOV [EDI], AL;;
      INC EDI;;
      ADD EAX, 16;;
      CMP EAX, EBX;;
      JNZ loopBody;;
    busyBody:;;
      JMP busyBody
  .
