	.section	.rodata
_ZZZ$$$$:
	.string	"$$$$"
	.text
	.globl	$malloc
	.type	$$$$, @function
$$$$:
	subl	$16, %esp
	movl	$_ZZZ$$$$, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	$$$$, .-$malloc

