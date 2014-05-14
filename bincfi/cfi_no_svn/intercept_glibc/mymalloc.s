	.section	.rodata
_ZZZmalloc:
	.string	"malloc"
	.text
	.globl	malloc
	.type	malloc, @function
malloc:
	subl	$16, %esp
	movl	$_ZZZmalloc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	malloc, .-malloc

