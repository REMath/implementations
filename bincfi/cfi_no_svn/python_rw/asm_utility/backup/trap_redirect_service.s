.p2align 5
y8049510:
	sub    $0x128,%esp
	xor    %ecx,%ecx
	mov    %esi,0x11c(%esp)
	mov    0x130(%esp),%esi
	mov    %ebp,0x124(%esp)
	mov    0x134(%esp),%ebp
	mov    %ebx,0x118(%esp)
	mov    %edi,0x120(%esp)
	test   %esi,%esi
	je     y8049570 
	mov    (%esi),%eax
	lea    0xc(%esp),%edi
	mov    $0x20,%cl
	mov    %eax,(%esp)
	mov    0x84(%esi),%eax
	add    $0x4,%esi
	mov    %eax,0x4(%esp)
	rep movsl %ds:(%esi),%es:(%edi)
	movl    $0x0,%edx
	test   %edx,%edx
	je     y8049600 
y804956e:
	mov    %esp,%ecx
y8049570:
	lea    0x8c(%esp),%eax
	xor    %edx,%edx
	mov    0x12c(%esp),%ebx
	test   %ebp,%ebp
	mov    $0x8,%esi
	cmovne %eax,%edx
	mov    $0xae,%eax
	int    $0x80
	nop
	nop
	nop
	nop
	cmp    $0xfffff000,%eax
	ja     y8049624 
	test   %eax,%eax
	js     y80495dd 
	test   %ebp,%ebp
	je     y80495dd 
	mov    0x8c(%esp),%edx
	lea    0x4(%ebp),%edi
	mov    $0x20,%ecx
	lea    0x98(%esp),%esi
	mov    %edx,0x0(%ebp)
	rep movsl %ds:(%esi),%es:(%edi)
	mov    0x90(%esp),%edx
	mov    %edx,0x84(%ebp)
	mov    0x94(%esp),%edx
	mov    %edx,0x88(%ebp)
y80495dd:
	mov    0x118(%esp),%ebx
	mov    0x11c(%esp),%esi
	mov    0x120(%esp),%edi
	mov    0x124(%esp),%ebp
	add    $0x128,%esp
	ret    
y8049600:
	mov    %eax,%edx
	or     $0x4000000,%edx
	test   $0x4,%al
	mov    %edx,0x4(%esp)
	mov    $__my_restore,%eax
	mov    $__my_restore_rt,%edx
	cmove  %eax,%edx
	mov    %edx,0x8(%esp)
	jmp    y804956e 
y8049624:
	mov    $0xffffffe8,%edx
	neg    %eax
	mov    %gs:0x0,%ecx
	mov    %eax,(%ecx,%edx,1)
	or     $0xffffffff,%eax
	jmp    y80495dd 
	nop
.p2align 5

__my_sigaction:
	push   %ebx
	mov    0x8(%esp),%eax
	mov    0xc(%esp),%ecx
	mov    0x10(%esp),%ebx
	lea    -0x20(%eax),%edx
	cmp    $0x1,%edx
	jbe    y8049667 
	mov    %ebx,0x10(%esp)
	mov    %ecx,0xc(%esp)
	mov    %eax,0x8(%esp)
	pop    %ebx
	jmp    y8049510 
y8049667:
	mov    $0xffffffe8,%eax
	mov    %gs:0x0,%edx
	movl   $0x16,(%edx,%eax,1)
	or     $0xffffffff,%eax
	pop    %ebx
	ret    
	nop

.p2align 5
__my_restore_rt:
	mov    $0xad,%eax
	int    $0x80
	nop

.p2align 5
__my_restore:
	pop    %eax
	mov    $0x77,%eax
	int    $0x80

.p2align 5
__my_trap_redirector_old:
	pushl	%ebp
	movl	%esp, %ebp
	andl	$-16, %esp
	subl	$160, %esp
	movl	$4, 152(%esp)
	movl	$signal_handler, 20(%esp)
	movl	$0, 8(%esp)
	leal	20(%esp), %eax
	movl	%eax, 4(%esp)
	movl	$5, (%esp)
	call	__my_sigaction
	leave
	ret

.p2align 5
__my_trap_redirector:
	.ifdef link_type_static
	subl	$16, %esp
	call	alloc_page
	movl	$6, 4(%esp)#$6 is the entry number
	movl	%eax, (%esp)
	call	my_setup_ldt_entry
	addl	$16, %esp
	xor	%eax, %eax
	mov	$0x37, %ax #0x37 = 6 << 3 + 7
	mov	%eax, %gs
	#assign page to gs
	.endif
	pushl	%ebp
	movl	%esp, %ebp
	andl	$-16, %esp
	subl	$160, %esp
	leal	20(%esp), %eax
	movl	%eax, 8(%esp)
	movl	$0, 4(%esp)
	movl	$5, (%esp)
	call	__my_sigaction
	movl	20(%esp), %edx
	movl	$signal_handler, %eax
	cmpl	%eax, %edx
	je	__my_trap_L5
	movl	$4, 152(%esp)
	movl	$signal_handler, 20(%esp)
	leal	20(%esp), %eax
	movl	$0, 8(%esp)
	movl	%eax, 4(%esp)
	movl	$5, (%esp)
	call	__my_sigaction
__my_trap_L5:


	movl	$0, %eax
	leave
	ret


.p2align 5
