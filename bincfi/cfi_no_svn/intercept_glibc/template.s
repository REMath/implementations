	.section	.rodata
_ZZZtemplate:
	.string	"template"
	.text
	.globl	template
	.type	template, @function
template:
	subl	$16, %esp
	movl	$_ZZZtemplate, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	template, .-template

