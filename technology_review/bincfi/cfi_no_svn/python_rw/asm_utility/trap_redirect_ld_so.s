#include "asm_define.h"
.p2align 5
__my_trap_redirector:
	pushl	%ebp
	movl	%esp, %ebp
	andl	$-16, %esp
	subl	$200, %esp
	movl	%eax, 196(%esp)
	movl	%ecx, 192(%esp)
	movl	%edx, 188(%esp)
	movl	%ebx, 184(%esp)
	movl	%esi, 180(%esp)
	movl	%edi, 176(%esp)
	#call	get_pic_base_ecx
	#addl	$signal_handler, %ecx
	#movl	$4, 152(%esp)
	#movl	%ecx, 20(%esp)
	#leal	20(%esp), %eax
	#movl	$0, 8(%esp)
	#movl	%eax, 4(%esp)
	#movl	$5, (%esp)
	#call	__my_sigaction
	SET_ABS_ADDR_ECX($signal_handler)
	SIGACTION($5, %ecx)
	#call	get_pic_base_ecx
	#addl	$signal_handler_segv, %ecx
	#movl	$4, 152(%esp)
	#movl	%ecx, 20(%esp)
	#leal	20(%esp), %eax
	#movl	$0, 8(%esp)
	#movl	%eax, 4(%esp)
	#movl	$11, (%esp)
	#call	__my_sigaction
	SET_ABS_ADDR_ECX($signal_handler_segv)
	SIGACTION($11, %ecx)
#__my_trap_L5:
	#movl	$0, %eax
	movl	176(%esp), %edi
	movl	180(%esp), %esi
	movl	184(%esp), %ebx
	movl	188(%esp), %edx
	movl	192(%esp), %ecx
	movl	196(%esp), %eax
	leave
	ret
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
	nop
.p2align 6
get_pic_base_ecx:
	call	___search_next1
___search_next1:
	pop %ecx
	subl $___search_next1, %ecx
	ret

.p2align 5
