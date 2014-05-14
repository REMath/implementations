.p2align 6

.macro restore_and_jmp
.ifdef use_ret
	subl	$4, %esp
	movl	%eax, (%esp)
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx	
	movl	%gs:0x50, %esi
	movl	%gs:0x54, %edi
	ret
.else
	movl	%eax,%gs:0x40
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx	
	movl	%gs:0x50, %esi
	movl	%gs:0x54, %edi

	jmp 	*%gs:0x40
.endif
.endm

local_search:
movl	%gs:0x40, %eax

	.ifdef pic_change_stack
	#get base address
	movl	%esp, %edx
	movl	%gs:0x5c, %esp
	call	__local_search_next2
__local_search_next2:
	pop	%ecx
	subl	$__local_search_next2, %ecx
	movl	%edx, %esp
	.else
	call	__local_search_next2
__local_search_next2:
	pop	%ecx
	subl	$__local_search_next2, %ecx
	.endif

	movl	%ecx, %gs:0x3c
	subl	%ecx, %eax

	#bound checking
	movl	$local_insn_begin, %edx
	cmpl	%edx, %eax
	jb	local_search_L8
	movl	$local_insn_end, %edx
	cmpl	%edx, %eax
	ja	local_search_L8
	#save jmp target
	movl	%eax, %gs:0x40

	#compute hash index in eax
	movl	$local_insn_begin, %edx
	subl	%edx, %eax
	movl	$insn_mask, %edx
	andl	%edx, %eax	
	movl	%eax, %esi
	movl	$0x0, %edi
	jmp	local_search_L4
local_search_L7:
	movl	%esi, %eax
	movl	%gs:0x3c, %ecx
	movl	local_array(%ecx,%eax,4), %edx
	movl	%gs:0x40, %eax
	cmpl	%eax, %edx
	je	local_search_L5
	movl	%edi, %eax
	addl	$1, %eax
	movl	%eax,%edi
	movl	%esi, %eax
	leal	1(%eax), %edx
	movl	$insn_mask, %eax
	andl	%edx, %eax
	movl	%eax, %esi
	jmp	local_search_L4
local_search_L5:
	movl	%esi, %eax
	movl	%gs:0x3c, %ecx
	movl	local_array(%ecx,%eax,4), %eax
	addl	%gs:0x3c, %eax
	restore_and_jmp

local_search_L4:
	movl	%edi, %edx
	movl	$size, %eax
	cmpl	%eax, %edx
	jl	local_search_L7	
	xor %eax,%eax
	inc %eax
	movl $0x41,%ebx
	#int $0x80
	hlt

local_search_L8:
	nop
local_search_L2:
	#xor %eax,%eax
	#inc %eax
	#movl %gs:0x40,%ebx
	#int $0x80
	#hlt

	.ifdef ret_to_orig
	#check if ret uses an original address
	movl	$insn_begin, %edx
	cmpl	%edx, %eax
	jb	local_search_L9
	movl	$insn_end, %edx
	cmpl	%edx, %eax
	ja	local_search_L9
	add  %gs:0x3c, %eax
	movl	%eax,%gs:0x40
	jmp	binsearch
local_search_L9:
	.endif

	add  %gs:0x3c, %eax
	movl	%eax,%gs:0x40
	.ifdef only_local_lookup
	movl	%gs:0x44, %eax
	movl	%gs:0x48, %ecx
	movl	%gs:0x4c, %edx	
	movl	%gs:0x50, %esi
	movl	%gs:0x54, %edi
	jmp 	*%gs:0x40
	.endif
	.ifdef	use_far_jmp
	ljmp	$0x006f,$0x200
	.else
	movl	$0x03000200, %eax
	jmp	*%eax
	.endif
