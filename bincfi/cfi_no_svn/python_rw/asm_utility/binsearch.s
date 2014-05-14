binsearch:
	movl	$size, %eax
	subl	$1, %eax
	movl	%eax, %gs:0x54
	movl	$0, %gs:0x50
	jmp	.Label2
.Label6:
	movl	%gs:0x50, %edx
	movl	%gs:0x54, %eax
	addl	%edx, %eax
	movl	%eax, %edx
	shrl	$31, %edx
	addl	%edx, %eax
	sarl	%eax
	movl	array(,%eax,8), %edx
	movl	%gs:0x40, %eax
	cmpl	%eax, %edx
	jne	.Label3
	movl	%gs:0x50, %edx
	movl	%gs:0x54, %eax
	addl	%edx, %eax
	movl	%eax, %edx
	shrl	$31, %edx
	addl	%edx, %eax
	sarl	%eax
	movl	$array, %edx
	addl	$4, %edx
	movl	(%edx,%eax,8), %eax
	movl	%eax, %gs:0x40
	nop
.Label4:
	movl	%gs:0x3c, %eax
	cmpl	$1, %eax
	jne	.Label9
	jmp	.Label10
.Label3:
	movl	%gs:0x50, %edx
	movl	%gs:0x54, %eax
	addl	%edx, %eax
	movl	%eax, %edx
	shrl	$31, %edx
	addl	%edx, %eax
	sarl	%eax
	movl	array(,%eax,8), %edx
	movl	%gs:0x40, %eax
	cmpl	%eax, %edx
	jge	.Label5
	movl	%gs:0x50, %edx
	movl	%gs:0x54, %eax
	addl	%edx, %eax
	movl	%eax, %edx
	shrl	$31, %edx
	addl	%edx, %eax
	sarl	%eax
	addl	$1, %eax
	movl	%eax, %gs:0x50
	jmp	.Label2
.Label5:
	movl	%gs:0x50, %edx
	movl	%gs:0x54, %eax
	addl	%edx, %eax
	movl	%eax, %edx
	shrl	$31, %edx
	addl	%edx, %eax
	sarl	%eax
	subl	$1, %eax
	movl	%eax, %gs:0x54
.Label2:
	movl	%gs:0x50, %edx
	movl	%gs:0x54, %eax
	cmpl	%eax, %edx
	jle	.Label6
.Label7:
#error:
	#hlt
	jmp	.Label8
	
.Label10:
	movl	%gs:0x44, %eax
	movl	%gs:0x4c, %edx
.Label9:
.Label8:
	jmp	*%gs:0x40
