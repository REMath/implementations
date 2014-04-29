       cmp R6, R7
tgt:   gotoLE patch
       halt R0
new:   halt R0
patch: cst new -> R0
       cst (tgt+1) -> R2
       store R0 -> *R2
       goto tgt

