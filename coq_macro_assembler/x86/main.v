Require Import ssreflect ssrbool ssrnat eqtype seq finfun tuple fintype.
Require Import bitsrep ilogic.
Require Import program programassem imp call.
Require Import cursor safe instrrules.
Require Import reg instr instrsyntax macros Ascii bitsops bitsprops bitsopsprops.
Require Import screenspec screenimp lifeimp.

Open Scope instr_scope.
Local Transparent ILFun_Ops.

Definition codeAddr: DWORD := #x"00300000".
Definition bufAddr : DWORD := #x"00400000".
Definition vesaAddr: DWORD := #x"f0000000".
Definition white   : DWORD := #x"ffffffff".

Definition mainBytes : seq BYTE :=
  assemble codeAddr (
  LOCAL buf;
  clsProg;;
  copyBuf screenBase buf;;
  MOV ECX, 20;;  MOV EDX, 40;;  makeGlider buf;;
  MOV ECX, 50;;  MOV EDX, 15;;  makeGlider buf;;
  MOV ECX, 5;;   MOV EDX, 5;;  makePulsar buf;;
  copyBuf buf screenBase;;

  LOCAL busy;
    busy:;;
      delay;;
      oneStepScreen screenBase buf;;
      copyBuf buf screenBase;;
      JMP busy;;
  buf:;
  ) (* ++ nseq (numCols*numRows*2) #0 *).

