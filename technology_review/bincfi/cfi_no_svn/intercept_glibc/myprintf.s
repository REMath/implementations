	.file	"myprintf.c"
	.local	libc_handle
	.comm	libc_handle,4,4
	.local	handler
	.comm	handler,4,4
	.section	.rodata
.LC0:
	.string	"libc.so"
.LC1:
	.string	"printf"
	.text
	.globl	printf
	.type	printf, @function
printf:
.LFB0:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	subl	$20, %esp
	call	__i686.get_pc_thunk.bx
	addl	$_GLOBAL_OFFSET_TABLE_, %ebx
	movl	$2, 4(%esp)
	leal	.LC0@GOTOFF(%ebx), %eax
	movl	%eax, (%esp)
	call	dlopen@PLT
	movl	%eax, libc_handle@GOTOFF(%ebx)
	leal	.LC1@GOTOFF(%ebx), %edx
	movl	libc_handle@GOTOFF(%ebx), %eax
	movl	%edx, 4(%esp)
	movl	%eax, (%esp)
	call	dlsym@PLT
	movl	%eax, handler@GOTOFF(%ebx)
	addl	$20, %esp
	popl	%ebx
	popl	%ebp
	ret
.LFE0:
	.size	printf, .-printf
	.globl	puts
	.type	puts, @function
puts:
.LFB1:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	subl	$20, %esp
	call	__i686.get_pc_thunk.bx
	addl	$_GLOBAL_OFFSET_TABLE_, %ebx
	movl	$2, 4(%esp)
	leal	.LC0@GOTOFF(%ebx), %eax
	movl	%eax, (%esp)
	call	dlopen@PLT
	movl	%eax, libc_handle@GOTOFF(%ebx)
	leal	.LC1@GOTOFF(%ebx), %edx
	movl	libc_handle@GOTOFF(%ebx), %eax
	movl	%edx, 4(%esp)
	movl	%eax, (%esp)
	call	dlsym@PLT
	movl	%eax, handler@GOTOFF(%ebx)
	addl	$20, %esp
	popl	%ebx
	popl	%ebp
	jmp	*%eax
	ret
.LFE1:
	.size	puts, .-puts
	.globl	main
	.type	main, @function
main:
.LFB2:
	pushl	%ebp
	movl	%esp, %ebp
	popl	%ebp
	ret
.LFE2:
	.size	main, .-main
	.section	.text.__i686.get_pc_thunk.bx,"axG",@progbits,__i686.get_pc_thunk.bx,comdat
	.globl	__i686.get_pc_thunk.bx
	.hidden	__i686.get_pc_thunk.bx
	.type	__i686.get_pc_thunk.bx, @function
__i686.get_pc_thunk.bx:
.LFB3:
	movl	(%esp), %ebx
	ret
.LFE3:
	.ident	"GCC: (Ubuntu/Linaro 4.6.1-9ubuntu3) 4.6.1"
	.section	.note.GNU-stack,"",@progbits
