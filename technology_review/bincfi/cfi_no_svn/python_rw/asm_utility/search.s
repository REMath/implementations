	.file	"search.c"
	.globl	array
	.data
	.align 32
	.type	array, @object
	.size	array, 8192
array:
	.long	0
	.long	2
	.long	1025
	.long	3
	.long	1026
	.long	5
	.long	1027
	.long	7
	.zero	8160
	.comm	insn_begin,4,4
	.comm	insn_end,4,4
	.comm	old_addr,4,4
	.comm	insn_mask,4,4
	.comm	mapping_size,4,4
	.comm	idx,4,4
	.comm	i,4,4
	.section	.rodata
.LC0:
	.string	"search addr %d, new addr:%d\n"
	.text
	.globl	main
	.type	main, @function
main:
.LFB0:
	pushl	%ebp
	movl	%esp, %ebp
	andl	$-16, %esp
	subl	$32, %esp
	movl	$0, i
	movl	$1024, mapping_size
	movl	$0, insn_begin
	movl	$2000, insn_end
	movl	$512, insn_mask
	movl	$1026, old_addr
	movl	old_addr, %eax
	movl	%eax, 28(%esp)
	movl	$search, %eax
	call	*%eax
	movl	old_addr, %edx
	movl	$.LC0, %eax
	movl	%edx, 8(%esp)
	movl	28(%esp), %edx
	movl	%edx, 4(%esp)
	movl	%eax, (%esp)
	call	printf
	movl	$0, old_addr
	movl	old_addr, %eax
	movl	%eax, 28(%esp)
	movl	$search, %eax
	call	*%eax
	movl	old_addr, %edx
	movl	$.LC0, %eax
	movl	%edx, 8(%esp)
	movl	28(%esp), %edx
	movl	%edx, 4(%esp)
	movl	%eax, (%esp)
	call	printf
	movl	$1027, old_addr
	movl	old_addr, %eax
	movl	%eax, 28(%esp)
	movl	$search, %eax
	call	*%eax
	movl	old_addr, %edx
	movl	$.LC0, %eax
	movl	%edx, 8(%esp)
	movl	28(%esp), %edx
	movl	%edx, 4(%esp)
	movl	%eax, (%esp)
	call	printf
	leave
	ret
.LFE0:
	.size	main, .-main
	.globl	search
	.type	search, @function
search:
	movl	old_addr, %edx
	movl	insn_begin, %eax
	cmpl	%eax, %edx
	jl	.L8
	movl	old_addr, %edx
	movl	insn_end, %eax
	cmpl	%eax, %edx
	jg	.L8
	movl	old_addr, %edx
	movl	insn_begin, %eax
	subl	%eax, %edx
	movl	insn_mask, %eax
	andl	%edx, %eax
	movl	%eax, idx
	movl	$0, i
	jmp	.L4
.L7:
	movl	idx, %eax
	movl	array(,%eax,8), %edx
	movl	old_addr, %eax
	cmpl	%eax, %edx
	je	.L5
	movl	i, %eax
	addl	$1, %eax
	movl	%eax, i
	movl	idx, %eax
	leal	1(%eax), %edx
	movl	insn_mask, %eax
	andl	%edx, %eax
	movl	%eax, idx
	jmp	.L4
.L5:
	movl	idx, %eax
	movl	array+4(,%eax,8), %eax
	movl	%eax, old_addr
	jmp	.L2
.L4:
	movl	i, %edx
	movl	mapping_size, %eax
	cmpl	%eax, %edx
	jl	.L7
.L3:
.L8:
	nop
.L2:
	ret
.LFE1:
	.size	search, .-search
	.ident	"GCC: (Ubuntu/Linaro 4.6.1-9ubuntu3) 4.6.1"
	.section	.note.GNU-stack,"",@progbits
