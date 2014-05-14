#include "asm_define.h"
.p2align 5
__my_trap_redirector_old:
	pushl	%ebp
	movl	%esp, %ebp
	andl	$-16, %esp
	subl	$160, %esp
	movl	$4, 152(%esp)
	movl	SIGNAL_HANDLER, 20(%esp)
	movl	$0, 8(%esp)
	leal	20(%esp), %eax
	movl	%eax, 4(%esp)
	movl	$5, (%esp)
	call	__my_sigaction
	leave
	ret

.p2align 5
__my_trap_redirector:
	.ifdef transparent_entry
	#include "modify_entry.S"
	.endif
	pusha
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
	/*initialize stack for service function */
	.ifdef pic_change_stack
	call	init_my_stack
	.endif
	leal	20(%esp), %eax
	movl	%eax, 8(%esp)
	movl	$0, 4(%esp)
	movl	SIGNO, (%esp)
	/* first check whether our signal handler 
	 has already been registered  */
	call	__my_sigaction
	movl	20(%esp), %edx
	.ifdef pic_change_stack
	movl	%esp, %eax
	movl	%gs:0x5c, %esp	
	call	get_pic_base_ecx
	movl	%eax, %esp
	.else
	call	get_pic_base_ecx
	.endif

	addl	SIGNAL_HANDLER, %ecx
	cmpl	%ecx, %edx
	je	__my_trap_L5
	/* check if signal_handle has been registered,
	 if .. register our signal handler if not */
	movl	$4, 152(%esp)
	movl	%ecx, 20(%esp)
	leal	20(%esp), %eax
	movl	$0, 8(%esp)
	movl	%eax, 4(%esp)
	movl	$5, (%esp)
	call	__my_sigaction
__my_trap_L5:
	movl	$0, %eax
	leave
	popa
	.ifdef code_is_shared_library
	ret
	/*jmp	__REAL_INIT_FUNC*/
	.else
	ret
	.endif
.p2align 5
get_pic_base_ecx:
	call	___search_next1
___search_next1:
	pop %ecx
	subl $___search_next1, %ecx
	ret

.p2align 5

init_my_stack:
	call	alloc_stack_page
	addl	$0x800,%eax /*stack pointer pointing the page middle */
	movl	%eax, %gs:0x5c
	ret

.p2align 5

/* a stack for service function to get base address in PIC code */
alloc_stack_page:
	subl	$48,%esp
	movl	$0, 20(%esp)
	movl	$-1, 16(%esp)
	movl	$34, 12(%esp)
	movl	$3, 8(%esp)
	movl	$4096, 4(%esp)
	movl	$0, (%esp)
	call	my_mmap
	addl	$48,%esp
	ret
.p2align 5
my_mmap:
	push   %ebp
	push   %ebx
	push   %esi
	push   %edi
	mov    0x14(%esp),%ebx
	mov    0x18(%esp),%ecx
	mov    0x1c(%esp),%edx
	mov    0x20(%esp),%esi
	mov    0x24(%esp),%edi
	mov    0x28(%esp),%ebp
	mov    $0xc0,%eax
	int    $0x80
	pop    %edi
	pop    %esi
	pop    %ebx
	pop    %ebp
	ret

