      cst -1 -> R7
      load *R7 -> R0  (* n *)
      cst key+1 -> R6 (* address to patch *)
      cst 1 -> R1     (* counter *)
      cst 1 -> R2     (* accumulator *)
loop: cmp R1, R0
      gotoLE last
      cst 1 -> R7
      add R7 -> R1    (* inc counter *)
      cst 0 -> R3
      add R2 -> R3    (* remember current value *)
key:  cst 0 -> R4
      add R4 -> R2    (* accumulate *)
      store R3 -> *R6 (* store new instr *)
      goto loop
last: halt R2
