      cst init -> R0
      goto dispatch

init: cst -1 -> R7
      load *R7 -> R5
      cst 1 -> R1
      cst 1 -> R2
      cst key+1 -> R6
      cst loop -> R0
      goto dispatch

loop: cst loop_exit -> R0
      cmp R1 >= R5
      gotoLE loop_break
      cst loop_body -> R0
loop_break:
      goto dispatch

loop_body:
      cst 1 -> R7
      add R7 -> R1
      cst 0 -> R3
      add R2 -> R3
key:  cst 0 -> R4
      add R4 -> R2
      store R3 -> *R6
      cst loop -> R0
      goto dispatch

loop_exit:
      halt R2

dispatch: goto *R0

