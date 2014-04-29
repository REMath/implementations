main: cst Ret -> R3
      goto f
Ret:  goto main

f:    cst 42 -> R1
      cst -1 -> R2
      add R3 -> R2
      load *R2 -> R0
      cst ref+1 -> R2
      load *R2 -> R2
      cmp R0, R2
      gotoEQ ok
      goto error
ok:   goto *R3

error:cst 1 -> R1
      halt R1

ref:  goto f
