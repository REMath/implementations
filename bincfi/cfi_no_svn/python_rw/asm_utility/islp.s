.p2align 6
.macro restore_and_jmp
.ifdef use_ret
	movl	%eax, (%esp)
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx
	ret
.else
	movl	%eax,%gs:0x40
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx
	addl	$4,%esp
	jmp 	*%gs:0x40
.endif
.endm

local_search:
movl	%gs:0x40, %eax
	movl	%esp, %edx
	movl	%gs:0x5c, %esp
	call	___search_next2
___search_next2:
	pop	%ecx
	subl	$___search_next2, %ecx
	movl	%edx, %esp
	
	movl	%ecx, %gs:0x3c
	subl	%ecx, %eax

	movl	$local_insn_begin, %edx
	cmpl	%edx, %eax
	jl	Local8
	movl	$local_insn_end, %edx
	cmpl	%edx, %eax
	jg	Local8
	movl	%edx,%gs:0x40
	movl	$local_insn_begin, %edx
	subl	%edx, %eax
	movl	$insn_mask, %edx
	andl	%edx, %eax
	movl	%eax, %gs:0x50
	movl	$0x0, %gs:0x54
	jmp	Local4
Local7:
	movl	%gs:0x50, %eax
	movl	%gs:0x3c, %ecx
	movl	local_array(%ecx,%eax,4), %edx
	movl	%gs:0x40, %ecx
	cmpl	%ecx, %edx
	je	Local5
	movl	%gs:0x54, %eax
	addl	$1, %eax
	movl	%eax,%gs:0x54
	movl	%gs:0x50, %eax
	leal	1(%eax), %edx
	movl	$insn_mask, %eax
	andl	%edx, %eax
	movl	%eax, %gs:0x50
	jmp	Local4
Local5:
	addl	%gs:0x3c,%edx
	movl	%edx, %eax
	restore_and_jmp
	
Local4:
	movl	%gs:0x54, %edx
	movl	$size, %eax
	cmpl	%eax, %edx
	jl	Local7	
	xor %eax,%eax
	inc %eax
	movl $0x41,%ebx
	int $0x80

Local8:
	nop
Local2:
	#xor %eax,%eax
	#inc %eax
	#movl %gs:0x40,%ebx
	#int $0x80
	#hlt
	add  %gs:0x3c, %eax
	restore_and_jmp


