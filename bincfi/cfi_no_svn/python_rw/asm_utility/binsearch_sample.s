binsearch:
	movl	-0x0c(%esp), %eax
	cmpl	$1, %eax
	jne	.L9
	jmp	.L10
.L10:
	movl	-0x18(%esp), %eax
	movl	-0x1c(%esp), %ecx
	movl	-0x20(%esp), %edx
.L9:
	jmp	*-0x04(%esp)
