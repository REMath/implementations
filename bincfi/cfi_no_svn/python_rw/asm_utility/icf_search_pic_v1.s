	#.comm	array,8000,32
	#.comm	insn_begin,4,4
	#.comm	insn_end,4,4
	#old_addr:	%gs:0x40,4,4
	#.comm	insn_mask,4,4
	#.comm	size,4,4
	#idx	%esi,4,4
	#i	%edi,4,4
	#code base: %gs:0x3c
binsearch:
	movl	%gs:0x40, %edx

	.ifdef pic_change_stack
	movl	%esp, %eax
	movl	%gs:0x5c, %esp
	call	__binsearch_next
__binsearch_next:
	pop	%ecx
	subl	$__binsearch_next, %ecx
	movl	%eax, %esp
	.else
	call	__binsearch_next
__binsearch_next:
	pop	%ecx
	subl	$__binsearch_next, %ecx
	.endif

	movl	%ecx, %gs:0x3c
	subl	%ecx, %edx

	movl	$insn_begin, %eax
	cmpl	%eax, %edx
	jb	binsearch_L8
	movl	$insn_end, %eax
	cmpl	%eax, %edx
	ja	binsearch_L8
	movl	%edx, %gs:0x40
	movl	$insn_begin, %eax
	subl	%eax, %edx
	movl	$insn_mask, %eax
	andl	%edx, %eax
	movl	%eax, %esi
	movl	$0x0, %edi
	jmp	binsearch_L4
binsearch_L7:
	movl	%esi, %eax
	movl	%gs:0x3c, %ecx
	movl	array(%ecx,%eax,8), %edx
	movl	%gs:0x40, %ecx
	cmpl	%ecx, %edx
	je	binsearch_L5
	movl	%edi, %eax
	addl	$1, %eax
	movl	%eax,%edi
	movl	%esi, %eax
	leal	1(%eax), %edx
	movl	$insn_mask, %eax
	andl	%edx, %eax
	movl	%eax, %esi
	jmp	binsearch_L4
binsearch_L5:
	movl	%esi, %eax
	movl	%gs:0x3c, %ecx
	addl	$array,%ecx
	addl	$0x4,%ecx
	movl	(%ecx,%eax,8), %eax
	#dec	%eax
	addl	%gs:0x3c,%eax
	movl	%eax,%gs:0x40
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx
	movl	%gs:0x50, %esi
	movl	%gs:0x54, %edi
	jmp 	*%gs:0x40
binsearch_L4:
	movl	%edi, %edx
	movl	$size, %eax
	cmpl	%eax, %edx
	jl	binsearch_L7	
	xor %eax,%eax
	inc %eax
	xor %ebx,%ebx
	mov $0x40, %ebx
	int $0x80
binsearch_L8:
	nop
binsearch_L2:
	#xor %eax,%eax
	#inc %eax
	#movl %gs:0x40,%ebx
	
	#int $0x80
	#hlt
	#check if jmp to translated code
	movl	$local_insn_begin, %eax
	cmpl	%eax, %edx
	jb	binsearch_L9
	movl	$local_insn_end, %eax
	cmpl	%eax, %edx
	ja	binsearch_L9
	jmp	local_search

binsearch_L9:
	addl	%gs:0x3c,%edx
	movl	%edx,%gs:0x40
	.ifdef only_local_lookup
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx	
	movl	%gs:0x50, %esi
	movl	%gs:0x54, %edi
	#here, we go to the global lookup
	jmp 	*%gs:0x40
	.endif
	.ifdef use_far_jmp
	ljmp	$0x006f,$global_lookup
	.else
	movl	$0x03000000, %eax
	jmp	*%eax
	.endif
.p2align 5
