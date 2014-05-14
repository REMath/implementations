   cst -128 -> R6
   add R6 -> R1
   cmp R6, R1
   gotoLT ko
   cst -96 -> R7
   cmp R1, R7
   gotoLE ko
   store R0 -> *R1
ko:halt R0
