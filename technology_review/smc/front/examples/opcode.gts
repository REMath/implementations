     cst new -> R2
     cst tgt -> R4
     cmp R0, R1
     gotoLE mod
tgt: add R1 -> R0  (* may be overwritten *)
     hlt R0
mod: load *R2 -> R3
     store R3 -> *R4
     goto tgt
new: mul R1 -> R0
