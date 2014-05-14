cst init -> R0
dispatch:
goto *R0

init:
cst -1 -> R7
load *R7 -> R5 (* n *)
cst 1 -> R1    (* counter *)
cst 1 -> R2    (* accumulator *)
cst key -> R6
cst 2 -> R7
add R7 -> R6   (* address to patch *)
cst loop -> R0
goto dispatch

loop:
cst loop_exit -> R0
cmp R1, R5
gotoLE loop_break
cst loop_body -> R0
loop_break:
goto dispatch

loop_body:
cst 1 -> R7
add R7 -> R1 (* inc counter *)
cst 0 -> R3
add R2 -> R3 (* remember current value *)
key:
cst 0 -> R4
add R4 -> R2 (* accumulate *)
store R3 -> *R6 (* store new instr *)
cst loop -> R0
goto dispatch

loop_exit:
halt R2

(*
Computes the nth Fibonacci's number,
with n initially stored at address -1.

R5: n
R1: counter
R2: accumulator
R0: dispatch variable


*)
