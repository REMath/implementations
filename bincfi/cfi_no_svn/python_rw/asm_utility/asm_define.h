#define MOV_ADDR_TO_REG(value, reg)	\
.ifdef is_pic;				\
	pushl  %ecx;			\
	call   get_pic_base_ecx;	\
	addl   value, %ecx;		\
	movl   %ecx, reg;		\
	popl   %ecx;			\
.else;					\
	mov    value, reg;		\
.endif

#define SET_ABS_ADDR_ECX(value)		\
	call	get_pic_base_ecx;	\
	addl	value, %ecx;

#define SIGACTION(sig, func)		\
	movl	$4, 152(%esp);		\
	movl	func, 20(%esp);		\
	leal	20(%esp), %eax;		\
	movl	$0, 8(%esp);		\
	movl	%eax, 4(%esp);		\
	movl	sig, (%esp);		\
	call	__my_sigaction


#ifdef USE_SIGSEGV
	#define SIGNO $11
	#define SIGNAL_HANDLER	$signal_handler_segv
#else
	#define SIGNO $5
	#define SIGNAL_HANDLER	$signal_handler
#endif
