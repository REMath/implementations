.text
.p2align 4
alloc_page:
	subl	$48,%esp
	movl	$0, 20(%esp)
	movl	$-1, 16(%esp)
	movl	$34, 12(%esp)
	movl	$3, 8(%esp)
	movl	$4096, 4(%esp)
	movl	$0, (%esp)
	call	__Zmmap
	addl	$48,%esp
	ret
.p2align 5
__Zmmap:
	push   %ebp
	push   %ebx
	push   %esi
	push   %edi
	mov    0x14(%esp),%ebx
	mov    0x18(%esp),%ecx
	mov    0x1c(%esp),%edx
	mov    0x20(%esp),%esi
	mov    0x24(%esp),%edi
	mov    0x28(%esp),%ebp
	mov    $0xc0,%eax
	int    $0x80
	pop    %edi
	pop    %esi
	pop    %ebx
	pop    %ebp
	ret
.p2align 4
#please check /PROJ_ROOT/modify_ldt/setup_ldt_entry/modify.c
#for source code of my_setup_ldt_entry:
#parameter1: base address
#parameter2: entry number
my_setup_ldt_entry:
	push   %ebp
	mov    %esp,%ebp
	sub    $0x48,%esp
	mov    0xc(%ebp),%eax
	mov    %ax,-0x2c(%ebp)
	movzwl -0x2c(%ebp),%eax
	mov    %eax,-0x1c(%ebp)
	mov    0x8(%ebp),%eax
	mov    %eax,-0x18(%ebp)
	movl   $0xfffff,-0x14(%ebp)
	movzbl -0x10(%ebp),%eax
	or     $0x1,%eax
	mov    %al,-0x10(%ebp)
	movzbl -0x10(%ebp),%eax
	and    $0xfffffff9,%eax
	mov    %al,-0x10(%ebp)
	movzbl -0x10(%ebp),%eax
	and    $0xfffffff7,%eax
	mov    %al,-0x10(%ebp)
	movzbl -0x10(%ebp),%eax
	or     $0x10,%eax
	mov    %al,-0x10(%ebp)
	movzbl -0x10(%ebp),%eax
	and    $0xffffffdf,%eax
	mov    %al,-0x10(%ebp)
	movzbl -0x10(%ebp),%eax
	or     $0x40,%eax
	mov    %al,-0x10(%ebp)
	movl   $0x10,0x8(%esp)
	lea    -0x1c(%ebp),%eax
	mov    %eax,0x4(%esp)
	movl   $0x1,(%esp)
	call   __Z_modify_ldt
	mov    %eax,-0xc(%ebp)
	mov    -0xc(%ebp),%eax
	leave  
	ret    
__Z_modify_ldt:
	push   %ebx
	mov    0x10(%esp),%edx
	mov    0xc(%esp),%ecx
	mov    0x8(%esp),%ebx
	mov    $0x7b,%eax
	int    $0x80
	pop    %ebx
	cmp    $0xfffff001,%eax
	jae    __Z_modify_ldt_err
	ret    
__Z_modify_ldt_err:
	movl $0x30, %ebx
	movl $0x1, %eax
	int  $0x80
