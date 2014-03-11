	.file	"segfault.c"
	.section	.rodata
	.align 4
.LC0:
	.string	"|0| everything looks fine. lets produce a SIGSEGV\n"
	.align 4
.LC1:
	.string	"|1| after first provocated SIGSEGV\n"
	.align 4
.LC2:
	.string	"|2| after second provocated SIGSEGV\n"
	.align 4
.LC3:
	.string	"|X| We survived - enough played today.\n"
	.text
	.globl	main
	.type	main, @function
main:
.LFB0:
	.cfi_startproc
	pushl	%ebp
	.cfi_def_cfa_offset 8
	.cfi_offset 5, -8
	movl	%esp, %ebp
	.cfi_def_cfa_register 5
	andl	$-16, %esp
	subl	$32, %esp
	movl	$0, 28(%esp)
	movl	stderr, %eax
	movl	%eax, %edx
	movl	$.LC0, %eax
	movl	%edx, 12(%esp)
	movl	$50, 8(%esp)
	movl	$1, 4(%esp)
	movl	%eax, (%esp)
	call	fwrite
	movl	28(%esp), %eax
	movb	$1, (%eax)
	movl	stderr, %eax
	movl	%eax, %edx
	movl	$.LC1, %eax
	movl	%edx, 12(%esp)
	movl	$35, 8(%esp)
	movl	$1, 4(%esp)
	movl	%eax, (%esp)
	call	fwrite
	movl	28(%esp), %eax
	movb	$1, (%eax)
	movl	stderr, %eax
	movl	%eax, %edx
	movl	$.LC2, %eax
	movl	%edx, 12(%esp)
	movl	$36, 8(%esp)
	movl	$1, 4(%esp)
	movl	%eax, (%esp)
	call	fwrite
	movl	stderr, %eax
	movl	%eax, %edx
	movl	$.LC3, %eax
	movl	%edx, 12(%esp)
	movl	$39, 8(%esp)
	movl	$1, 4(%esp)
	movl	%eax, (%esp)
	call	fwrite
	movl	$0, %eax
	leave
	.cfi_restore 5
	.cfi_def_cfa 4, 4
	ret
	.cfi_endproc
.LFE0:
	.size	main, .-main
	.ident	"GCC: (Ubuntu/Linaro 4.6.1-9ubuntu3) 4.6.1"
	.section	.note.GNU-stack,"",@progbits
