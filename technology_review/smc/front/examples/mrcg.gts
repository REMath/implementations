      cst 0 -> R6
      cst 1 -> R5
loop: add R5 -> R6
      cst gen -> R0
      cst enc(store R1 -> *R2) -> R1
      store R1 -> *R0
      cst enc(goto R2) -> R1
      cst gen + 1 -> R0
      store R1 -> *R0
      cst ggen -> R2
      cst loop -> R0
      cst enc(goto R0) -> R1
      goto gen
gen:  skip
      skip
ggen: skip
