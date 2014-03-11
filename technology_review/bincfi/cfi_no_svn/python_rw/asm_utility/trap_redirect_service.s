#include "asm_define.h"
.p2align 5
__my_trap_redirector_old:
	pushl	%ebp
	movl	%esp, %ebp
	andl	$-16, %esp
	subl	$160, %esp
	movl	$4, 152(%esp)
	movl	$signal_handler, 20(%esp)
	movl	$0, 8(%esp)
	leal	20(%esp), %eax
	movl	%eax, 4(%esp)
	movl	$5, (%esp)
	call	__my_sigaction
	leave
	ret

.p2align 5
__my_trap_redirector:
	.ifdef init_gs
	subl	$16, %esp
	call	alloc_page
	movl	$6, 4(%esp)#$6 is the entry number
	movl	%eax, (%esp)
	call	my_setup_ldt_entry
	addl	$16, %esp
	xor	%eax, %eax
	mov	$0x37, %ax #0x37 = 6 << 3 + 7
	mov	%eax, %gs
	#assign page to gs
	.endif
	pushl	%ebp
	movl	%esp, %ebp
	andl	$-16, %esp
	subl	$160, %esp
	leal	20(%esp), %eax
	movl	%eax, 8(%esp)
	movl	$0, 4(%esp)
	movl	SIGNO, (%esp)
	call	__my_sigaction
	movl	20(%esp), %edx
	movl	SIGNAL_HANDLER, %eax
	cmpl	%eax, %edx
	je	__my_trap_L5
	movl	$4, 152(%esp)
	movl	SIGNAL_HANDLER, 20(%esp)
	leal	20(%esp), %eax
	movl	$0, 8(%esp)
	movl	%eax, 4(%esp)
	movl	SIGNO, (%esp)
	call	__my_sigaction
__my_trap_L5:


	movl	$0, %eax
	leave
	ret


.p2align 5
