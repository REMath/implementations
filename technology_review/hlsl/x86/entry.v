Require Import ssreflect seq finfun tuple fintype.
Require Import bitsrep bitsops mem reg instr instrsyntax encinstr.
Require Import program macros Ascii.

Local Open Scope instr_scope.

Definition sumEx := 
  LOCAL loopBody;
      mov EAX, 1;;
      mov EBX, 10;;
      xor ECX, ECX;;
    loopBody:;;
      add ECX, EAX;;
      inc EAX;;
      cmp EAX, EBX;;
      jnz loopBody
  .

Definition outEx :=
  LOCAL loopBody;
      mov EAX, 1;;
      mov EBX, 10;;
      xor ECX, ECX;;
    loopBody:;;
      OUT false #50;;
      inc EAX;;
      cmp EAX, EBX;;
      jnz loopBody
  .

Definition screenAddr:DWORD := #x"b8000" +# 160*32.

Definition simpleScreenEx :=
  LOCAL busyBody;
    busyBody:;;
      mov EDI, screenAddr;;
      mov byte [EDI], (nat_of_ascii "D");;
      mov byte [EDI+1], 63;;
      jmp busyBody
  .

Definition prettyEx :=
  LOCAL loopBody;
  LOCAL busyBody;
      mov EDI, screenAddr;;
      mov EAX, 31;;
      mov EBX, 255;;
    loopBody:;;
      mov byte [EDI], 1;;
      inc EDI;;
      mov byte [EDI], EAX;;
      inc EDI;;
      add EAX, 16;;
      cmp EAX, EBX;;
      jnz loopBody;;
    busyBody:;;
      jmp busyBody
  .
