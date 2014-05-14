      cst main -> R6
      cst alter -> R7
main: goto *R7
      store R0 -> *R7
alter:load *R6 -> R0
      cst enc(skip) -> R1
      store R1 -> *R6
      goto main
