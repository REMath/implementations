#	.text
#	.globl _start
#	.type _start, @function	
#_start:
#	ret
#	.size _start, .-_start

	.text
	.globl main
	.type main, @function	
main:
	ret
	.size main, .-main


	.section	.rodata
_ZZZsigaction:
	.string	"sigaction"
	.text
	.globl	sigaction
	.type	sigaction, @function
sigaction:
	#jmp	sigaction_fake_success
	cmpl	$0x5,0x04(%esp)
	je	sigaction_fake_success
	cmpl	$0xb,0x04(%esp)
	je	sigaction_fake_success
	cmpl	$0x11,0x04(%esp)
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

	.section	.rodata
_ZZZsigset:
	.string	"sigset"
	.text
	.globl	sigset
	.type	sigset, @function
sigset:
	cmpl	$0x5,0x04(%esp)
	je	sigset_fake_success
	cmpl	$0xb,0x04(%esp)
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
_ZZZsignal:
	.string	"signal"
	.text
	.globl	signal
	.type	signal, @function

signal:
	cmpl	$0x5,0x04(%esp)
	je	signal_fake_success
	cmpl	$0xb,0x04(%esp)
	je	signal_fake_success
	subl	$16, %esp
	movl	$_ZZZsignal, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
signal_fake_success:
	movl	$0x0,%eax
	ret
	.size	signal, .-signal
_ZZZpthread_sigmask:
	.string	"pthread_sigmask"
	.text
	.globl	pthread_sigmask
	.type	pthread_sigmask, @function
	.globl	sigprocmask
	.type	sigprocmask, @function

sigprocmask:
pthread_sigmask:
	cmpl	$0x0,0x04(%esp)
	je	pthread_sigmask_fake_success	
	cmpl	$0x2,0x04(%esp)
	je	pthread_sigmask_fake_success

	subl	$16, %esp
	movl	$_ZZZpthread_sigmask, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
pthread_sigmask_fake_success:
	movl	$0x0,%eax
	ret
	.size	pthread_sigmask, .-pthread_sigmask
	.size	sigprocmask, .-sigprocmask

