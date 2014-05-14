.macro restore_eflags
.ifdef enforce_save_eflags
sahf
#addl $0x7f000000, %gs:0x58
.endif
.endm

