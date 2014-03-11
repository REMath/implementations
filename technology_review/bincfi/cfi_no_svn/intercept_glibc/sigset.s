	.section	.rodata
_ZZZsigset:
	.string	"sigset"
	.text
	.globl	sigset
	.type	sigset, @function
sigset:
	cmpl	$0x5,$0x4(%esp)
	je	sigset_fake_success
	subl	$16, %esp
	movl	$_ZZZsigset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
sigset_fake_success:
	movl	$0x0,%eax
	ret
	.size	sigset, .-sigset

