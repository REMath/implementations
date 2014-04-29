goto main
tplt:
cst 0 -> R2    (* tplt + 1  *)
cst 0 -> R5    (* tplt + 3  *)
add R4 -> R5   (* tplt + 5  *)
load *R5 -> R6 (* tplt + 6  *)
cst 0 -> R7    (* tplt + 7  *)
mul R6 -> R7   (* tplt + 9  *)
add R7 -> R2   (* tplt + 10 *)
goto *R0       (* tplt + 11 *)

main:
cst 3 -> R2
cst 0 -> R0
cst gen -> R1
cst tplt -> R3
(* copy instruction 1 *)
cst 1 -> R6
add R3 -> R6
load *R6 -> R4
store R4 -> *R1
cst 1 -> R6
add R6 -> R1
cst 2 -> R6
add R3 -> R6
load *R6 -> R4
store R4 -> *R1
cst 1 -> R6
add R6 -> R1
loop:
cmp R0 >= R2
gotoLE post
(* load value vec1[R0] in R5 *)
cst -1000 -> R4
add R0 -> R4
load *R4 -> R5
(* copy and patch instruction 3 *)
cst 3 -> R6
add R3 -> R6
load *R6 -> R4
store R4 -> *R1
cst 1 -> R6
add R6 -> R1
cst 4 -> R6
add R3 -> R6
load *R6 -> R4
add R0 -> R4
store R4 -> *R1
cst 1 -> R6
add R6 -> R1
(* copy instruction 5 *)
cst 5 -> R6
add R3 -> R6
load *R6 -> R4
store R4 -> *R1
cst 1 -> R6
add R6 -> R1
(* copy instruction 6 *)
cst 6 -> R6
add R3 -> R6
load *R6 -> R4
store R4 -> *R1
cst 1 -> R6
add R6 -> R1
(* copy and patch instruction 7 *)
cst 7 -> R6
add R3 -> R6
load *R6 -> R4
store R4 -> *R1
cst 1 -> R6
add R6 -> R1
cst 8 -> R6
add R3 -> R6
load *R6 -> R4
add R5 -> R4
store R4 -> *R1
cst 1 -> R6
add R6 -> R1
(* copy instruction 9 *)
cst 9 -> R6
add R3 -> R6
load *R6 -> R4
store R4 -> *R1
cst 1 -> R6
add R6 -> R1
(* copy instruction 10 *)
cst 10 -> R6
add R3 -> R6
load *R6 -> R4
store R4 -> *R1
cst 1 -> R6
add R6 -> R1
(* next *)
cst 1 -> R6
add R6 -> R0
goto loop
post:
(* copy instruction 11 *)
cst 11 -> R6
add R3 -> R6
load *R6 -> R4
store R4 -> *R1
(* call generated code *)
cst reta -> R0
goto gen
reta:
goto main

gen:


























