      cst dead -> R7
main: cst g -> R0
      cst h -> R1
      load *R0 -> R2
      cst 1 -> R4
      add R2 -> R4
      store R4 -> *R0
      load *R1 -> R3
g:    store R2 -> *R0
h:    goto* R7
      store R3 -> *R1
      goto main
dead:
