	.section	.rodata
_ZZZsigaction:
	.string	"sigaction"
	.text
	.globl	sigaction
	.type	sigaction, @function
sigaction:
	cmpl	$0x5,0x04(%esp)
	je	sigaction_fake_success
	subl	$16, %esp
	movl	$_ZZZsigaction, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
sigaction_fake_success:
	movl	$0x0,%eax
	ret
	.size	sigaction, .-sigaction

