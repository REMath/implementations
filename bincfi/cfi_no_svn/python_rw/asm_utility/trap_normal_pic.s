#include "asm_define.h"
.p2align 5
tram_enter:
	movl	%eax,%gs:0x44
	movl	%ecx,%gs:0x48
	movl	%edx,%gs:0x4c	
	movl	%esi,%gs:0x50
	movl	%edi,%gs:0x54
	.ifdef  only_local_lookup
	jmp	binsearch
	.endif
	.ifdef  use_far_jmp
	ljmp	$0x6f,$0x0
	.else
	movl	$0x03000000, %eax
	jmp	*%eax
	.endif
.p2align 5
#redirect control to tram_enter
signal_handler:
.p2align 5
	pushl	%ebp
	movl	%esp, %ebp
	subl	$16, %esp
	movl	16(%ebp), %eax
	movl	76(%eax),%ecx
	dec	%ecx
	movl	%ecx,%gs:0x40
	movl	%eax, -4(%ebp)
	
	
	.ifdef pic_change_stack
	movl	%esp, %eax
	movl	%gs:0x5c, %esp
	call	get_pic_base_ecx
	movl	%eax, %esp
	.else
	call	get_pic_base_ecx
	.endif
	addl	$tram_enter, %ecx
	movl	-4(%ebp), %eax
	movl	%ecx, 76(%eax)
	leave
	ret
.p2align 5

signal_handler_segv:
.p2align 5
	pushl	%ebp
	movl	%esp, %ebp
	subl	$16, %esp

	movl	16(%ebp), %eax /* 3rd param */
	mov	12(%ebp), %edx /* 2nd param */
	cmpl	$0x2, 0x8(%edx)
	jne	UNKNOWN_SEGV
	cmpl	$0x15, 0x48(%eax)
	jne	UNKNOWN_SEGV
	movl	76(%eax),%ecx
	#dec	%ecx
	movl	%ecx,%gs:0x40
	movl	%eax, -4(%ebp)
	.ifdef pic_change_stack
	movl	%esp, %eax
	movl	%gs:0x5c, %esp
	call	get_pic_base_ecx
	movl	%eax, %esp
	.else
	call	get_pic_base_ecx
	.endif
	addl	$tram_enter, %ecx
	movl	-4(%ebp), %eax
	movl	%ecx, 76(%eax)
	leave
	ret
UNKNOWN_SEGV:
	subl	$200, %esp
	SIGACTION($11, $0)
	leave
	ret
.p2align 5

