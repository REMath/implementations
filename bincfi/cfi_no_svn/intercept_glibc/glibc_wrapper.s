	.section	.rodata
_ZZZputwchar:
	.string	"putwchar"
	.text
	.globl	putwchar
	.type	putwchar, @function
putwchar:
	subl	$16, %esp
	movl	$_ZZZputwchar, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putwchar, .-putwchar

	.section	.rodata
_ZZZsetrpcent:
	.string	"setrpcent"
	.text
	.globl	setrpcent
	.type	setrpcent, @function
setrpcent:
	subl	$16, %esp
	movl	$_ZZZsetrpcent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setrpcent, .-setrpcent

	.section	.rodata
_ZZZepoll_create:
	.string	"epoll_create"
	.text
	.globl	epoll_create
	.type	epoll_create, @function
epoll_create:
	subl	$16, %esp
	movl	$_ZZZepoll_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	epoll_create, .-epoll_create

	.section	.rodata
_ZZZklogctl:
	.string	"klogctl"
	.text
	.globl	klogctl
	.type	klogctl, @function
klogctl:
	subl	$16, %esp
	movl	$_ZZZklogctl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	klogctl, .-klogctl

	.section	.rodata
_ZZZdprintf:
	.string	"dprintf"
	.text
	.globl	dprintf
	.type	dprintf, @function
dprintf:
	subl	$16, %esp
	movl	$_ZZZdprintf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	dprintf, .-dprintf

	.section	.rodata
_ZZZchroot:
	.string	"chroot"
	.text
	.globl	chroot
	.type	chroot, @function
chroot:
	subl	$16, %esp
	movl	$_ZZZchroot, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	chroot, .-chroot

	.section	.rodata
_ZZZgetdate:
	.string	"getdate"
	.text
	.globl	getdate
	.type	getdate, @function
getdate:
	subl	$16, %esp
	movl	$_ZZZgetdate, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getdate, .-getdate

	.section	.rodata
_ZZZpthread_cond_signal:
	.string	"pthread_cond_signal"
	.text
	.globl	pthread_cond_signal
	.type	pthread_cond_signal, @function
pthread_cond_signal:
	subl	$16, %esp
	movl	$_ZZZpthread_cond_signal, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_cond_signal, .-pthread_cond_signal

	.section	.rodata
_ZZZxdr_short:
	.string	"xdr_short"
	.text
	.globl	xdr_short
	.type	xdr_short, @function
xdr_short:
	subl	$16, %esp
	movl	$_ZZZxdr_short, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_short, .-xdr_short

	.section	.rodata
_ZZZlfind:
	.string	"lfind"
	.text
	.globl	lfind
	.type	lfind, @function
lfind:
	subl	$16, %esp
	movl	$_ZZZlfind, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lfind, .-lfind

	.section	.rodata
_ZZZxdr_int64_t:
	.string	"xdr_int64_t"
	.text
	.globl	xdr_int64_t
	.type	xdr_int64_t, @function
xdr_int64_t:
	subl	$16, %esp
	movl	$_ZZZxdr_int64_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_int64_t, .-xdr_int64_t

	.section	.rodata
_ZZZkey_encryptsession_pk:
	.string	"key_encryptsession_pk"
	.text
	.globl	key_encryptsession_pk
	.type	key_encryptsession_pk, @function
key_encryptsession_pk:
	subl	$16, %esp
	movl	$_ZZZkey_encryptsession_pk, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	key_encryptsession_pk, .-key_encryptsession_pk

	.section	.rodata
_ZZZputchar_unlocked:
	.string	"putchar_unlocked"
	.text
	.globl	putchar_unlocked
	.type	putchar_unlocked, @function
putchar_unlocked:
	subl	$16, %esp
	movl	$_ZZZputchar_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putchar_unlocked, .-putchar_unlocked

	.section	.rodata
_ZZZxdr_pmaplist:
	.string	"xdr_pmaplist"
	.text
	.globl	xdr_pmaplist
	.type	xdr_pmaplist, @function
xdr_pmaplist:
	subl	$16, %esp
	movl	$_ZZZxdr_pmaplist, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_pmaplist, .-xdr_pmaplist

	.section	.rodata
_ZZZmkdtemp:
	.string	"mkdtemp"
	.text
	.globl	mkdtemp
	.type	mkdtemp, @function
mkdtemp:
	subl	$16, %esp
	movl	$_ZZZmkdtemp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkdtemp, .-mkdtemp

	.section	.rodata
_ZZZsighold:
	.string	"sighold"
	.text
	.globl	sighold
	.type	sighold, @function
sighold:
	subl	$16, %esp
	movl	$_ZZZsighold, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sighold, .-sighold

	.section	.rodata
_ZZZiruserok:
	.string	"iruserok"
	.text
	.globl	iruserok
	.type	iruserok, @function
iruserok:
	subl	$16, %esp
	movl	$_ZZZiruserok, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	iruserok, .-iruserok

	.section	.rodata
_ZZZcuserid:
	.string	"cuserid"
	.text
	.globl	cuserid
	.type	cuserid, @function
cuserid:
	subl	$16, %esp
	movl	$_ZZZcuserid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	cuserid, .-cuserid

	.section	.rodata
_ZZZwmemset:
	.string	"wmemset"
	.text
	.globl	wmemset
	.type	wmemset, @function
wmemset:
	subl	$16, %esp
	movl	$_ZZZwmemset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wmemset, .-wmemset

	.section	.rodata
_ZZZglobfree64:
	.string	"globfree64"
	.text
	.globl	globfree64
	.type	globfree64, @function
globfree64:
	subl	$16, %esp
	movl	$_ZZZglobfree64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	globfree64, .-globfree64

	.section	.rodata
_ZZZtimerfd_gettime:
	.string	"timerfd_gettime"
	.text
	.globl	timerfd_gettime
	.type	timerfd_gettime, @function
timerfd_gettime:
	subl	$16, %esp
	movl	$_ZZZtimerfd_gettime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	timerfd_gettime, .-timerfd_gettime

	.section	.rodata
_ZZZgetspnam_r:
	.string	"getspnam_r"
	.text
	.globl	getspnam_r
	.type	getspnam_r, @function
getspnam_r:
	subl	$16, %esp
	movl	$_ZZZgetspnam_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getspnam_r, .-getspnam_r

	.section	.rodata
_ZZZl64a:
	.string	"l64a"
	.text
	.globl	l64a
	.type	l64a, @function
l64a:
	subl	$16, %esp
	movl	$_ZZZl64a, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	l64a, .-l64a

	.section	.rodata
_ZZZgetrpcbyname:
	.string	"getrpcbyname"
	.text
	.globl	getrpcbyname
	.type	getrpcbyname, @function
getrpcbyname:
	subl	$16, %esp
	movl	$_ZZZgetrpcbyname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getrpcbyname, .-getrpcbyname

	.section	.rodata
_ZZZputc_unlocked:
	.string	"putc_unlocked"
	.text
	.globl	putc_unlocked
	.type	putc_unlocked, @function
putc_unlocked:
	subl	$16, %esp
	movl	$_ZZZputc_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putc_unlocked, .-putc_unlocked

	.section	.rodata
_ZZZhcreate:
	.string	"hcreate"
	.text
	.globl	hcreate
	.type	hcreate, @function
hcreate:
	subl	$16, %esp
	movl	$_ZZZhcreate, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	hcreate, .-hcreate

	.section	.rodata
_ZZZstrcpy:
	.string	"strcpy"
	.text
	.globl	strcpy
	.type	strcpy, @function
strcpy:
	subl	$16, %esp
	movl	$_ZZZstrcpy, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strcpy, .-strcpy

	.section	.rodata
_ZZZa64l:
	.string	"a64l"
	.text
	.globl	a64l
	.type	a64l, @function
a64l:
	subl	$16, %esp
	movl	$_ZZZa64l, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	a64l, .-a64l

	.section	.rodata
_ZZZxdr_long:
	.string	"xdr_long"
	.text
	.globl	xdr_long
	.type	xdr_long, @function
xdr_long:
	subl	$16, %esp
	movl	$_ZZZxdr_long, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_long, .-xdr_long

	.section	.rodata
_ZZZshmget:
	.string	"shmget"
	.text
	.globl	shmget
	.type	shmget, @function
shmget:
	subl	$16, %esp
	movl	$_ZZZshmget, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	shmget, .-shmget

	.section	.rodata
_ZZZgetw:
	.string	"getw"
	.text
	.globl	getw
	.type	getw, @function
getw:
	subl	$16, %esp
	movl	$_ZZZgetw, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getw, .-getw

	.section	.rodata
_ZZZgethostid:
	.string	"gethostid"
	.text
	.globl	gethostid
	.type	gethostid, @function
gethostid:
	subl	$16, %esp
	movl	$_ZZZgethostid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gethostid, .-gethostid

	.section	.rodata
_ZZZinotify_init1:
	.string	"inotify_init1"
	.text
	.globl	inotify_init1
	.type	inotify_init1, @function
inotify_init1:
	subl	$16, %esp
	movl	$_ZZZinotify_init1, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inotify_init1, .-inotify_init1

	.section	.rodata
_ZZZauthunix_create:
	.string	"authunix_create"
	.text
	.globl	authunix_create
	.type	authunix_create, @function
authunix_create:
	subl	$16, %esp
	movl	$_ZZZauthunix_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	authunix_create, .-authunix_create

	.section	.rodata
_ZZZwmemcmp:
	.string	"wmemcmp"
	.text
	.globl	wmemcmp
	.type	wmemcmp, @function
wmemcmp:
	subl	$16, %esp
	movl	$_ZZZwmemcmp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wmemcmp, .-wmemcmp

	.section	.rodata
_ZZZsetgrent:
	.string	"setgrent"
	.text
	.globl	setgrent
	.type	setgrent, @function
setgrent:
	subl	$16, %esp
	movl	$_ZZZsetgrent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setgrent, .-setgrent

	.section	.rodata
_ZZZacct:
	.string	"acct"
	.text
	.globl	acct
	.type	acct, @function
acct:
	subl	$16, %esp
	movl	$_ZZZacct, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	acct, .-acct

	.section	.rodata
_ZZZexit:
	.string	"exit"
	.text
	.globl	exit
	.type	exit, @function
exit:
	subl	$16, %esp
	movl	$_ZZZexit, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	exit, .-exit

	.section	.rodata
_ZZZexecl:
	.string	"execl"
	.text
	.globl	execl
	.type	execl, @function
execl:
	subl	$16, %esp
	movl	$_ZZZexecl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	execl, .-execl

	.section	.rodata
_ZZZhtonl:
	.string	"htonl"
	.text
	.globl	htonl
	.type	htonl, @function
htonl:
	subl	$16, %esp
	movl	$_ZZZhtonl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	htonl, .-htonl

	.section	.rodata
_ZZZgetprotobynumber_r:
	.string	"getprotobynumber_r"
	.text
	.globl	getprotobynumber_r
	.type	getprotobynumber_r, @function
getprotobynumber_r:
	subl	$16, %esp
	movl	$_ZZZgetprotobynumber_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getprotobynumber_r, .-getprotobynumber_r

	.section	.rodata
_ZZZwordexp:
	.string	"wordexp"
	.text
	.globl	wordexp
	.type	wordexp, @function
wordexp:
	subl	$16, %esp
	movl	$_ZZZwordexp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wordexp, .-wordexp

	.section	.rodata
_ZZZgetprotobynumber_r:
	.string	"getprotobynumber_r"
	.text
	.globl	getprotobynumber_r
	.type	getprotobynumber_r, @function
getprotobynumber_r:
	subl	$16, %esp
	movl	$_ZZZgetprotobynumber_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getprotobynumber_r, .-getprotobynumber_r

	.section	.rodata
_ZZZendprotoent:
	.string	"endprotoent"
	.text
	.globl	endprotoent
	.type	endprotoent, @function
endprotoent:
	subl	$16, %esp
	movl	$_ZZZendprotoent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endprotoent, .-endprotoent

	.section	.rodata
_ZZZclearerr_unlocked:
	.string	"clearerr_unlocked"
	.text
	.globl	clearerr_unlocked
	.type	clearerr_unlocked, @function
clearerr_unlocked:
	subl	$16, %esp
	movl	$_ZZZclearerr_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clearerr_unlocked, .-clearerr_unlocked

	.section	.rodata
_ZZZfnmatch:
	.string	"fnmatch"
	.text
	.globl	fnmatch
	.type	fnmatch, @function
fnmatch:
	subl	$16, %esp
	movl	$_ZZZfnmatch, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fnmatch, .-fnmatch

	.section	.rodata
_ZZZxdr_keybuf:
	.string	"xdr_keybuf"
	.text
	.globl	xdr_keybuf
	.type	xdr_keybuf, @function
xdr_keybuf:
	subl	$16, %esp
	movl	$_ZZZxdr_keybuf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_keybuf, .-xdr_keybuf

	.section	.rodata
_ZZZgnu_dev_major:
	.string	"gnu_dev_major"
	.text
	.globl	gnu_dev_major
	.type	gnu_dev_major, @function
gnu_dev_major:
	subl	$16, %esp
	movl	$_ZZZgnu_dev_major, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gnu_dev_major, .-gnu_dev_major

	.section	.rodata
_ZZZxdr_uint32_t:
	.string	"xdr_uint32_t"
	.text
	.globl	xdr_uint32_t
	.type	xdr_uint32_t, @function
xdr_uint32_t:
	subl	$16, %esp
	movl	$_ZZZxdr_uint32_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_uint32_t, .-xdr_uint32_t

	.section	.rodata
_ZZZhtons:
	.string	"htons"
	.text
	.globl	htons
	.type	htons, @function
htons:
	subl	$16, %esp
	movl	$_ZZZhtons, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	htons, .-htons

	.section	.rodata
_ZZZsigrelse:
	.string	"sigrelse"
	.text
	.globl	sigrelse
	.type	sigrelse, @function
sigrelse:
	subl	$16, %esp
	movl	$_ZZZsigrelse, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigrelse, .-sigrelse

	.section	.rodata
_ZZZpsiginfo:
	.string	"psiginfo"
	.text
	.globl	psiginfo
	.type	psiginfo, @function
psiginfo:
	subl	$16, %esp
	movl	$_ZZZpsiginfo, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	psiginfo, .-psiginfo

	.section	.rodata
_ZZZexecv:
	.string	"execv"
	.text
	.globl	execv
	.type	execv, @function
execv:
	subl	$16, %esp
	movl	$_ZZZexecv, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	execv, .-execv

	.section	.rodata
_ZZZsprintf:
	.string	"sprintf"
	.text
	.globl	sprintf
	.type	sprintf, @function
sprintf:
	subl	$16, %esp
	movl	$_ZZZsprintf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sprintf, .-sprintf

	.section	.rodata
_ZZZnfsservctl:
	.string	"nfsservctl"
	.text
	.globl	nfsservctl
	.type	nfsservctl, @function
nfsservctl:
	subl	$16, %esp
	movl	$_ZZZnfsservctl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	nfsservctl, .-nfsservctl

	.section	.rodata
_ZZZenvz_merge:
	.string	"envz_merge"
	.text
	.globl	envz_merge
	.type	envz_merge, @function
envz_merge:
	subl	$16, %esp
	movl	$_ZZZenvz_merge, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	envz_merge, .-envz_merge

	.section	.rodata
_ZZZsetlocale:
	.string	"setlocale"
	.text
	.globl	setlocale
	.type	setlocale, @function
setlocale:
	subl	$16, %esp
	movl	$_ZZZsetlocale, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setlocale, .-setlocale

	.section	.rodata
_ZZZmemfrob:
	.string	"memfrob"
	.text
	.globl	memfrob
	.type	memfrob, @function
memfrob:
	subl	$16, %esp
	movl	$_ZZZmemfrob, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	memfrob, .-memfrob

	.section	.rodata
_ZZZtr_break:
	.string	"tr_break"
	.text
	.globl	tr_break
	.type	tr_break, @function
tr_break:
	subl	$16, %esp
	movl	$_ZZZtr_break, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tr_break, .-tr_break

	.section	.rodata
_ZZZfgetws_unlocked:
	.string	"fgetws_unlocked"
	.text
	.globl	fgetws_unlocked
	.type	fgetws_unlocked, @function
fgetws_unlocked:
	subl	$16, %esp
	movl	$_ZZZfgetws_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fgetws_unlocked, .-fgetws_unlocked

	.section	.rodata
_ZZZtowlower:
	.string	"towlower"
	.text
	.globl	towlower
	.type	towlower, @function
towlower:
	subl	$16, %esp
	movl	$_ZZZtowlower, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	towlower, .-towlower

	.section	.rodata
_ZZZfopen:
	.string	"fopen"
	.text
	.globl	fopen
	.type	fopen, @function
fopen:
	subl	$16, %esp
	movl	$_ZZZfopen, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fopen, .-fopen

	.section	.rodata
_ZZZgai_strerror:
	.string	"gai_strerror"
	.text
	.globl	gai_strerror
	.type	gai_strerror, @function
gai_strerror:
	subl	$16, %esp
	movl	$_ZZZgai_strerror, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gai_strerror, .-gai_strerror

	.section	.rodata
_ZZZfgetspent:
	.string	"fgetspent"
	.text
	.globl	fgetspent
	.type	fgetspent, @function
fgetspent:
	subl	$16, %esp
	movl	$_ZZZfgetspent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fgetspent, .-fgetspent

	.section	.rodata
_ZZZstrsignal:
	.string	"strsignal"
	.text
	.globl	strsignal
	.type	strsignal, @function
strsignal:
	subl	$16, %esp
	movl	$_ZZZstrsignal, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strsignal, .-strsignal

	.section	.rodata
_ZZZgetnetbyname_r:
	.string	"getnetbyname_r"
	.text
	.globl	getnetbyname_r
	.type	getnetbyname_r, @function
getnetbyname_r:
	subl	$16, %esp
	movl	$_ZZZgetnetbyname_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getnetbyname_r, .-getnetbyname_r

	.section	.rodata
_ZZZstrncmp:
	.string	"strncmp"
	.text
	.globl	strncmp
	.type	strncmp, @function
strncmp:
	subl	$16, %esp
	movl	$_ZZZstrncmp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strncmp, .-strncmp

	.section	.rodata
_ZZZgetnetbyname_r:
	.string	"getnetbyname_r"
	.text
	.globl	getnetbyname_r
	.type	getnetbyname_r, @function
getnetbyname_r:
	subl	$16, %esp
	movl	$_ZZZgetnetbyname_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getnetbyname_r, .-getnetbyname_r

	.section	.rodata
_ZZZgetprotoent_r:
	.string	"getprotoent_r"
	.text
	.globl	getprotoent_r
	.type	getprotoent_r, @function
getprotoent_r:
	subl	$16, %esp
	movl	$_ZZZgetprotoent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getprotoent_r, .-getprotoent_r

	.section	.rodata
_ZZZsvcfd_create:
	.string	"svcfd_create"
	.text
	.globl	svcfd_create
	.type	svcfd_create, @function
svcfd_create:
	subl	$16, %esp
	movl	$_ZZZsvcfd_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcfd_create, .-svcfd_create

	.section	.rodata
_ZZZgetprotoent_r:
	.string	"getprotoent_r"
	.text
	.globl	getprotoent_r
	.type	getprotoent_r, @function
getprotoent_r:
	subl	$16, %esp
	movl	$_ZZZgetprotoent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getprotoent_r, .-getprotoent_r

	.section	.rodata
_ZZZxdr_unixcred:
	.string	"xdr_unixcred"
	.text
	.globl	xdr_unixcred
	.type	xdr_unixcred, @function
xdr_unixcred:
	subl	$16, %esp
	movl	$_ZZZxdr_unixcred, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_unixcred, .-xdr_unixcred

	.section	.rodata
_ZZZxdr_rmtcallres:
	.string	"xdr_rmtcallres"
	.text
	.globl	xdr_rmtcallres
	.type	xdr_rmtcallres, @function
xdr_rmtcallres:
	subl	$16, %esp
	movl	$_ZZZxdr_rmtcallres, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_rmtcallres, .-xdr_rmtcallres

	.section	.rodata
_ZZZinet_nsap_addr:
	.string	"inet_nsap_addr"
	.text
	.globl	inet_nsap_addr
	.type	inet_nsap_addr, @function
inet_nsap_addr:
	subl	$16, %esp
	movl	$_ZZZinet_nsap_addr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet_nsap_addr, .-inet_nsap_addr

	.section	.rodata
_ZZZttyslot:
	.string	"ttyslot"
	.text
	.globl	ttyslot
	.type	ttyslot, @function
ttyslot:
	subl	$16, %esp
	movl	$_ZZZttyslot, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ttyslot, .-ttyslot

	.section	.rodata
_ZZZwordfree:
	.string	"wordfree"
	.text
	.globl	wordfree
	.type	wordfree, @function
wordfree:
	subl	$16, %esp
	movl	$_ZZZwordfree, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wordfree, .-wordfree

	.section	.rodata
_ZZZposix_spawn_file_actions_:
	.string	"posix_spawn_file_actions_"
	.text
	.globl	posix_spawn_file_actions_
	.type	posix_spawn_file_actions_, @function
posix_spawn_file_actions_:
	subl	$16, %esp
	movl	$_ZZZposix_spawn_file_actions_, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawn_file_actions_, .-posix_spawn_file_actions_

	.section	.rodata
_ZZZgetdirentries:
	.string	"getdirentries"
	.text
	.globl	getdirentries
	.type	getdirentries, @function
getdirentries:
	subl	$16, %esp
	movl	$_ZZZgetdirentries, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getdirentries, .-getdirentries

	.section	.rodata
_ZZZerand48:
	.string	"erand48"
	.text
	.globl	erand48
	.type	erand48, @function
erand48:
	subl	$16, %esp
	movl	$_ZZZerand48, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	erand48, .-erand48

	.section	.rodata
_ZZZisfdtype:
	.string	"isfdtype"
	.text
	.globl	isfdtype
	.type	isfdtype, @function
isfdtype:
	subl	$16, %esp
	movl	$_ZZZisfdtype, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isfdtype, .-isfdtype

	.section	.rodata
_ZZZgetfsfile:
	.string	"getfsfile"
	.text
	.globl	getfsfile
	.type	getfsfile, @function
getfsfile:
	subl	$16, %esp
	movl	$_ZZZgetfsfile, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getfsfile, .-getfsfile

	.section	.rodata
_ZZZlcong48:
	.string	"lcong48"
	.text
	.globl	lcong48
	.type	lcong48, @function
lcong48:
	subl	$16, %esp
	movl	$_ZZZlcong48, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lcong48, .-lcong48

	.section	.rodata
_ZZZgetpwent:
	.string	"getpwent"
	.text
	.globl	getpwent
	.type	getpwent, @function
getpwent:
	subl	$16, %esp
	movl	$_ZZZgetpwent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpwent, .-getpwent

	.section	.rodata
_ZZZputgrent:
	.string	"putgrent"
	.text
	.globl	putgrent
	.type	putgrent, @function
putgrent:
	subl	$16, %esp
	movl	$_ZZZputgrent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putgrent, .-putgrent

	.section	.rodata
_ZZZgetservent_r:
	.string	"getservent_r"
	.text
	.globl	getservent_r
	.type	getservent_r, @function
getservent_r:
	subl	$16, %esp
	movl	$_ZZZgetservent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getservent_r, .-getservent_r

	.section	.rodata
_ZZZopen_wmemstream:
	.string	"open_wmemstream"
	.text
	.globl	open_wmemstream
	.type	open_wmemstream, @function
open_wmemstream:
	subl	$16, %esp
	movl	$_ZZZopen_wmemstream, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	open_wmemstream, .-open_wmemstream

	.section	.rodata
_ZZZinet6_opt_append:
	.string	"inet6_opt_append"
	.text
	.globl	inet6_opt_append
	.type	inet6_opt_append, @function
inet6_opt_append:
	subl	$16, %esp
	movl	$_ZZZinet6_opt_append, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_opt_append, .-inet6_opt_append

	.section	.rodata
_ZZZsetservent:
	.string	"setservent"
	.text
	.globl	setservent
	.type	setservent, @function
setservent:
	subl	$16, %esp
	movl	$_ZZZsetservent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setservent, .-setservent

	.section	.rodata
_ZZZtimerfd_create:
	.string	"timerfd_create"
	.text
	.globl	timerfd_create
	.type	timerfd_create, @function
timerfd_create:
	subl	$16, %esp
	movl	$_ZZZtimerfd_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	timerfd_create, .-timerfd_create

	.section	.rodata
_ZZZstrrchr:
	.string	"strrchr"
	.text
	.globl	strrchr
	.type	strrchr, @function
strrchr:
	subl	$16, %esp
	movl	$_ZZZstrrchr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strrchr, .-strrchr

	.section	.rodata
_ZZZsvcerr_systemerr:
	.string	"svcerr_systemerr"
	.text
	.globl	svcerr_systemerr
	.type	svcerr_systemerr, @function
svcerr_systemerr:
	subl	$16, %esp
	movl	$_ZZZsvcerr_systemerr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcerr_systemerr, .-svcerr_systemerr

	.section	.rodata
_ZZZfflush_unlocked:
	.string	"fflush_unlocked"
	.text
	.globl	fflush_unlocked
	.type	fflush_unlocked, @function
fflush_unlocked:
	subl	$16, %esp
	movl	$_ZZZfflush_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fflush_unlocked, .-fflush_unlocked

	.section	.rodata
_ZZZvwprintf:
	.string	"vwprintf"
	.text
	.globl	vwprintf
	.type	vwprintf, @function
vwprintf:
	subl	$16, %esp
	movl	$_ZZZvwprintf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vwprintf, .-vwprintf

	.section	.rodata
_ZZZposix_spawnattr_setschedp:
	.string	"posix_spawnattr_setschedp"
	.text
	.globl	posix_spawnattr_setschedp
	.type	posix_spawnattr_setschedp, @function
posix_spawnattr_setschedp:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_setschedp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_setschedp, .-posix_spawnattr_setschedp

	.section	.rodata
_ZZZgetipv4sourcefilter:
	.string	"getipv4sourcefilter"
	.text
	.globl	getipv4sourcefilter
	.type	getipv4sourcefilter, @function
getipv4sourcefilter:
	subl	$16, %esp
	movl	$_ZZZgetipv4sourcefilter, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getipv4sourcefilter, .-getipv4sourcefilter

	.section	.rodata
_ZZZtempnam:
	.string	"tempnam"
	.text
	.globl	tempnam
	.type	tempnam, @function
tempnam:
	subl	$16, %esp
	movl	$_ZZZtempnam, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tempnam, .-tempnam

	.section	.rodata
_ZZZisalpha:
	.string	"isalpha"
	.text
	.globl	isalpha
	.type	isalpha, @function
isalpha:
	subl	$16, %esp
	movl	$_ZZZisalpha, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isalpha, .-isalpha

	.section	.rodata
_ZZZregexec:
	.string	"regexec"
	.text
	.globl	regexec
	.type	regexec, @function
regexec:
	subl	$16, %esp
	movl	$_ZZZregexec, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	regexec, .-regexec

	.section	.rodata
_ZZZrevoke:
	.string	"revoke"
	.text
	.globl	revoke
	.type	revoke, @function
revoke:
	subl	$16, %esp
	movl	$_ZZZrevoke, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	revoke, .-revoke

	.section	.rodata
_ZZZregexec:
	.string	"regexec"
	.text
	.globl	regexec
	.type	regexec, @function
regexec:
	subl	$16, %esp
	movl	$_ZZZregexec, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	regexec, .-regexec

	.section	.rodata
_ZZZreadlinkat:
	.string	"readlinkat"
	.text
	.globl	readlinkat
	.type	readlinkat, @function
readlinkat:
	subl	$16, %esp
	movl	$_ZZZreadlinkat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	readlinkat, .-readlinkat

	.section	.rodata
_ZZZauthunix_create_default:
	.string	"authunix_create_default"
	.text
	.globl	authunix_create_default
	.type	authunix_create_default, @function
authunix_create_default:
	subl	$16, %esp
	movl	$_ZZZauthunix_create_default, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	authunix_create_default, .-authunix_create_default

	.section	.rodata
_ZZZgetrpcbynumber:
	.string	"getrpcbynumber"
	.text
	.globl	getrpcbynumber
	.type	getrpcbynumber, @function
getrpcbynumber:
	subl	$16, %esp
	movl	$_ZZZgetrpcbynumber, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getrpcbynumber, .-getrpcbynumber

	.section	.rodata
_ZZZsetipv4sourcefilter:
	.string	"setipv4sourcefilter"
	.text
	.globl	setipv4sourcefilter
	.type	setipv4sourcefilter, @function
setipv4sourcefilter:
	subl	$16, %esp
	movl	$_ZZZsetipv4sourcefilter, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setipv4sourcefilter, .-setipv4sourcefilter

	.section	.rodata
_ZZZwcstold:
	.string	"wcstold"
	.text
	.globl	wcstold
	.type	wcstold, @function
wcstold:
	subl	$16, %esp
	movl	$_ZZZwcstold, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcstold, .-wcstold

	.section	.rodata
_ZZZcfmakeraw:
	.string	"cfmakeraw"
	.text
	.globl	cfmakeraw
	.type	cfmakeraw, @function
cfmakeraw:
	subl	$16, %esp
	movl	$_ZZZcfmakeraw, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	cfmakeraw, .-cfmakeraw

	.section	.rodata
_ZZZperror:
	.string	"perror"
	.text
	.globl	perror
	.type	perror, @function
perror:
	subl	$16, %esp
	movl	$_ZZZperror, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	perror, .-perror

	.section	.rodata
_ZZZshmat:
	.string	"shmat"
	.text
	.globl	shmat
	.type	shmat, @function
shmat:
	subl	$16, %esp
	movl	$_ZZZshmat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	shmat, .-shmat

	.section	.rodata
_ZZZrpmatch:
	.string	"rpmatch"
	.text
	.globl	rpmatch
	.type	rpmatch, @function
rpmatch:
	subl	$16, %esp
	movl	$_ZZZrpmatch, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rpmatch, .-rpmatch

	.section	.rodata
_ZZZregisterrpc:
	.string	"registerrpc"
	.text
	.globl	registerrpc
	.type	registerrpc, @function
registerrpc:
	subl	$16, %esp
	movl	$_ZZZregisterrpc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	registerrpc, .-registerrpc

	.section	.rodata
_ZZZwcstoll:
	.string	"wcstoll"
	.text
	.globl	wcstoll
	.type	wcstoll, @function
wcstoll:
	subl	$16, %esp
	movl	$_ZZZwcstoll, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcstoll, .-wcstoll

	.section	.rodata
_ZZZposix_spawnattr_setpgroup:
	.string	"posix_spawnattr_setpgroup"
	.text
	.globl	posix_spawnattr_setpgroup
	.type	posix_spawnattr_setpgroup, @function
posix_spawnattr_setpgroup:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_setpgroup, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_setpgroup, .-posix_spawnattr_setpgroup

	.section	.rodata
_ZZZqecvt_r:
	.string	"qecvt_r"
	.text
	.globl	qecvt_r
	.type	qecvt_r, @function
qecvt_r:
	subl	$16, %esp
	movl	$_ZZZqecvt_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	qecvt_r, .-qecvt_r

	.section	.rodata
_ZZZecvt_r:
	.string	"ecvt_r"
	.text
	.globl	ecvt_r
	.type	ecvt_r, @function
ecvt_r:
	subl	$16, %esp
	movl	$_ZZZecvt_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ecvt_r, .-ecvt_r

	.section	.rodata
_ZZZgetutxid:
	.string	"getutxid"
	.text
	.globl	getutxid
	.type	getutxid, @function
getutxid:
	subl	$16, %esp
	movl	$_ZZZgetutxid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getutxid, .-getutxid

	.section	.rodata
_ZZZsync_file_range:
	.string	"sync_file_range"
	.text
	.globl	sync_file_range
	.type	sync_file_range, @function
sync_file_range:
	subl	$16, %esp
	movl	$_ZZZsync_file_range, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sync_file_range, .-sync_file_range

	.section	.rodata
_ZZZgetnetbyaddr:
	.string	"getnetbyaddr"
	.text
	.globl	getnetbyaddr
	.type	getnetbyaddr, @function
getnetbyaddr:
	subl	$16, %esp
	movl	$_ZZZgetnetbyaddr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getnetbyaddr, .-getnetbyaddr

	.section	.rodata
_ZZZwcspbrk:
	.string	"wcspbrk"
	.text
	.globl	wcspbrk
	.type	wcspbrk, @function
wcspbrk:
	subl	$16, %esp
	movl	$_ZZZwcspbrk, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcspbrk, .-wcspbrk

	.section	.rodata
_ZZZenvz_remove:
	.string	"envz_remove"
	.text
	.globl	envz_remove
	.type	envz_remove, @function
envz_remove:
	subl	$16, %esp
	movl	$_ZZZenvz_remove, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	envz_remove, .-envz_remove

	.section	.rodata
_ZZZlutimes:
	.string	"lutimes"
	.text
	.globl	lutimes
	.type	lutimes, @function
lutimes:
	subl	$16, %esp
	movl	$_ZZZlutimes, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lutimes, .-lutimes

	.section	.rodata
_ZZZmunlock:
	.string	"munlock"
	.text
	.globl	munlock
	.type	munlock, @function
munlock:
	subl	$16, %esp
	movl	$_ZZZmunlock, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	munlock, .-munlock

	.section	.rodata
_ZZZgetpwuid:
	.string	"getpwuid"
	.text
	.globl	getpwuid
	.type	getpwuid, @function
getpwuid:
	subl	$16, %esp
	movl	$_ZZZgetpwuid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpwuid, .-getpwuid

	.section	.rodata
_ZZZkey_get_conv:
	.string	"key_get_conv"
	.text
	.globl	key_get_conv
	.type	key_get_conv, @function
key_get_conv:
	subl	$16, %esp
	movl	$_ZZZkey_get_conv, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	key_get_conv, .-key_get_conv

	.section	.rodata
_ZZZgetpwent_r:
	.string	"getpwent_r"
	.text
	.globl	getpwent_r
	.type	getpwent_r, @function
getpwent_r:
	subl	$16, %esp
	movl	$_ZZZgetpwent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpwent_r, .-getpwent_r

	.section	.rodata
_ZZZsendfile:
	.string	"sendfile"
	.text
	.globl	sendfile
	.type	sendfile, @function
sendfile:
	subl	$16, %esp
	movl	$_ZZZsendfile, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sendfile, .-sendfile

	.section	.rodata
_ZZZgetpwent_r:
	.string	"getpwent_r"
	.text
	.globl	getpwent_r
	.type	getpwent_r, @function
getpwent_r:
	subl	$16, %esp
	movl	$_ZZZgetpwent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpwent_r, .-getpwent_r

	.section	.rodata
_ZZZinet6_rth_init:
	.string	"inet6_rth_init"
	.text
	.globl	inet6_rth_init
	.type	inet6_rth_init, @function
inet6_rth_init:
	subl	$16, %esp
	movl	$_ZZZinet6_rth_init, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_rth_init, .-inet6_rth_init

	.section	.rodata
_ZZZinet6_opt_next:
	.string	"inet6_opt_next"
	.text
	.globl	inet6_opt_next
	.type	inet6_opt_next, @function
inet6_opt_next:
	subl	$16, %esp
	movl	$_ZZZinet6_opt_next, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_opt_next, .-inet6_opt_next

	.section	.rodata
_ZZZungetwc:
	.string	"ungetwc"
	.text
	.globl	ungetwc
	.type	ungetwc, @function
ungetwc:
	subl	$16, %esp
	movl	$_ZZZungetwc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ungetwc, .-ungetwc

	.section	.rodata
_ZZZecb_crypt:
	.string	"ecb_crypt"
	.text
	.globl	ecb_crypt
	.type	ecb_crypt, @function
ecb_crypt:
	subl	$16, %esp
	movl	$_ZZZecb_crypt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ecb_crypt, .-ecb_crypt

	.section	.rodata
_ZZZversionsort:
	.string	"versionsort"
	.text
	.globl	versionsort
	.type	versionsort, @function
versionsort:
	subl	$16, %esp
	movl	$_ZZZversionsort, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	versionsort, .-versionsort

	.section	.rodata
_ZZZxdr_longlong_t:
	.string	"xdr_longlong_t"
	.text
	.globl	xdr_longlong_t
	.type	xdr_longlong_t, @function
xdr_longlong_t:
	subl	$16, %esp
	movl	$_ZZZxdr_longlong_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_longlong_t, .-xdr_longlong_t

	.section	.rodata
_ZZZrecvmmsg:
	.string	"recvmmsg"
	.text
	.globl	recvmmsg
	.type	recvmmsg, @function
recvmmsg:
	subl	$16, %esp
	movl	$_ZZZrecvmmsg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	recvmmsg, .-recvmmsg

	.section	.rodata
_ZZZposix_spawnattr_init:
	.string	"posix_spawnattr_init"
	.text
	.globl	posix_spawnattr_init
	.type	posix_spawnattr_init, @function
posix_spawnattr_init:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_init, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_init, .-posix_spawnattr_init

	.section	.rodata
_ZZZget_current_dir_name:
	.string	"get_current_dir_name"
	.text
	.globl	get_current_dir_name
	.type	get_current_dir_name, @function
get_current_dir_name:
	subl	$16, %esp
	movl	$_ZZZget_current_dir_name, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	get_current_dir_name, .-get_current_dir_name

	.section	.rodata
_ZZZsemctl:
	.string	"semctl"
	.text
	.globl	semctl
	.type	semctl, @function
semctl:
	subl	$16, %esp
	movl	$_ZZZsemctl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	semctl, .-semctl

	.section	.rodata
_ZZZfputc_unlocked:
	.string	"fputc_unlocked"
	.text
	.globl	fputc_unlocked
	.type	fputc_unlocked, @function
fputc_unlocked:
	subl	$16, %esp
	movl	$_ZZZfputc_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fputc_unlocked, .-fputc_unlocked

	.section	.rodata
_ZZZverr:
	.string	"verr"
	.text
	.globl	verr
	.type	verr, @function
verr:
	subl	$16, %esp
	movl	$_ZZZverr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	verr, .-verr

	.section	.rodata
_ZZZgetprotobynumber:
	.string	"getprotobynumber"
	.text
	.globl	getprotobynumber
	.type	getprotobynumber, @function
getprotobynumber:
	subl	$16, %esp
	movl	$_ZZZgetprotobynumber, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getprotobynumber, .-getprotobynumber

	.section	.rodata
_ZZZfgetsgent:
	.string	"fgetsgent"
	.text
	.globl	fgetsgent
	.type	fgetsgent, @function
fgetsgent:
	subl	$16, %esp
	movl	$_ZZZfgetsgent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fgetsgent, .-fgetsgent

	.section	.rodata
_ZZZgetsecretkey:
	.string	"getsecretkey"
	.text
	.globl	getsecretkey
	.type	getsecretkey, @function
getsecretkey:
	subl	$16, %esp
	movl	$_ZZZgetsecretkey, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getsecretkey, .-getsecretkey

	.section	.rodata
_ZZZunlinkat:
	.string	"unlinkat"
	.text
	.globl	unlinkat
	.type	unlinkat, @function
unlinkat:
	subl	$16, %esp
	movl	$_ZZZunlinkat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	unlinkat, .-unlinkat

	.section	.rodata
_ZZZxdr_authdes_verf:
	.string	"xdr_authdes_verf"
	.text
	.globl	xdr_authdes_verf
	.type	xdr_authdes_verf, @function
xdr_authdes_verf:
	subl	$16, %esp
	movl	$_ZZZxdr_authdes_verf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_authdes_verf, .-xdr_authdes_verf

	.section	.rodata
_ZZZinitgroups:
	.string	"initgroups"
	.text
	.globl	initgroups
	.type	initgroups, @function
initgroups:
	subl	$16, %esp
	movl	$_ZZZinitgroups, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	initgroups, .-initgroups

	.section	.rodata
_ZZZinet_ntoa:
	.string	"inet_ntoa"
	.text
	.globl	inet_ntoa
	.type	inet_ntoa, @function
inet_ntoa:
	subl	$16, %esp
	movl	$_ZZZinet_ntoa, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet_ntoa, .-inet_ntoa

	.section	.rodata
_ZZZglob64:
	.string	"glob64"
	.text
	.globl	glob64
	.type	glob64, @function
glob64:
	subl	$16, %esp
	movl	$_ZZZglob64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	glob64, .-glob64

	.section	.rodata
_ZZZpmap_rmtcall:
	.string	"pmap_rmtcall"
	.text
	.globl	pmap_rmtcall
	.type	pmap_rmtcall, @function
pmap_rmtcall:
	subl	$16, %esp
	movl	$_ZZZpmap_rmtcall, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pmap_rmtcall, .-pmap_rmtcall

	.section	.rodata
_ZZZglob64:
	.string	"glob64"
	.text
	.globl	glob64
	.type	glob64, @function
glob64:
	subl	$16, %esp
	movl	$_ZZZglob64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	glob64, .-glob64

	.section	.rodata
_ZZZsetspent:
	.string	"setspent"
	.text
	.globl	setspent
	.type	setspent, @function
setspent:
	subl	$16, %esp
	movl	$_ZZZsetspent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setspent, .-setspent

	.section	.rodata
_ZZZxdr_char:
	.string	"xdr_char"
	.text
	.globl	xdr_char
	.type	xdr_char, @function
xdr_char:
	subl	$16, %esp
	movl	$_ZZZxdr_char, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_char, .-xdr_char

	.section	.rodata
_ZZZfopencookie:
	.string	"fopencookie"
	.text
	.globl	fopencookie
	.type	fopencookie, @function
fopencookie:
	subl	$16, %esp
	movl	$_ZZZfopencookie, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fopencookie, .-fopencookie

	.section	.rodata
_ZZZendaliasent:
	.string	"endaliasent"
	.text
	.globl	endaliasent
	.type	endaliasent, @function
endaliasent:
	subl	$16, %esp
	movl	$_ZZZendaliasent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endaliasent, .-endaliasent

	.section	.rodata
_ZZZfeof_unlocked:
	.string	"feof_unlocked"
	.text
	.globl	feof_unlocked
	.type	feof_unlocked, @function
feof_unlocked:
	subl	$16, %esp
	movl	$_ZZZfeof_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	feof_unlocked, .-feof_unlocked

	.section	.rodata
_ZZZisblank:
	.string	"isblank"
	.text
	.globl	isblank
	.type	isblank, @function
isblank:
	subl	$16, %esp
	movl	$_ZZZisblank, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isblank, .-isblank

	.section	.rodata
_ZZZgetusershell:
	.string	"getusershell"
	.text
	.globl	getusershell
	.type	getusershell, @function
getusershell:
	subl	$16, %esp
	movl	$_ZZZgetusershell, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getusershell, .-getusershell

	.section	.rodata
_ZZZsvc_sendreply:
	.string	"svc_sendreply"
	.text
	.globl	svc_sendreply
	.type	svc_sendreply, @function
svc_sendreply:
	subl	$16, %esp
	movl	$_ZZZsvc_sendreply, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svc_sendreply, .-svc_sendreply

	.section	.rodata
_ZZZgetgrgid:
	.string	"getgrgid"
	.text
	.globl	getgrgid
	.type	getgrgid, @function
getgrgid:
	subl	$16, %esp
	movl	$_ZZZgetgrgid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getgrgid, .-getgrgid

	.section	.rodata
_ZZZsiginterrupt:
	.string	"siginterrupt"
	.text
	.globl	siginterrupt
	.type	siginterrupt, @function
siginterrupt:
	subl	$16, %esp
	movl	$_ZZZsiginterrupt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	siginterrupt, .-siginterrupt

	.section	.rodata
_ZZZepoll_wait:
	.string	"epoll_wait"
	.text
	.globl	epoll_wait
	.type	epoll_wait, @function
epoll_wait:
	subl	$16, %esp
	movl	$_ZZZepoll_wait, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	epoll_wait, .-epoll_wait

	.section	.rodata
_ZZZfputwc:
	.string	"fputwc"
	.text
	.globl	fputwc
	.type	fputwc, @function
fputwc:
	subl	$16, %esp
	movl	$_ZZZfputwc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fputwc, .-fputwc

	.section	.rodata
_ZZZmkfifoat:
	.string	"mkfifoat"
	.text
	.globl	mkfifoat
	.type	mkfifoat, @function
mkfifoat:
	subl	$16, %esp
	movl	$_ZZZmkfifoat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkfifoat, .-mkfifoat

	.section	.rodata
_ZZZget_kernel_syms:
	.string	"get_kernel_syms"
	.text
	.globl	get_kernel_syms
	.type	get_kernel_syms, @function
get_kernel_syms:
	subl	$16, %esp
	movl	$_ZZZget_kernel_syms, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	get_kernel_syms, .-get_kernel_syms

	.section	.rodata
_ZZZgetrpcent_r:
	.string	"getrpcent_r"
	.text
	.globl	getrpcent_r
	.type	getrpcent_r, @function
getrpcent_r:
	subl	$16, %esp
	movl	$_ZZZgetrpcent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getrpcent_r, .-getrpcent_r

	.section	.rodata
_ZZZinet_ntop:
	.string	"inet_ntop"
	.text
	.globl	inet_ntop
	.type	inet_ntop, @function
inet_ntop:
	subl	$16, %esp
	movl	$_ZZZinet_ntop, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet_ntop, .-inet_ntop

	.section	.rodata
_ZZZstrncpy:
	.string	"strncpy"
	.text
	.globl	strncpy
	.type	strncpy, @function
strncpy:
	subl	$16, %esp
	movl	$_ZZZstrncpy, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strncpy, .-strncpy

	.section	.rodata
_ZZZgetdomainname:
	.string	"getdomainname"
	.text
	.globl	getdomainname
	.type	getdomainname, @function
getdomainname:
	subl	$16, %esp
	movl	$_ZZZgetdomainname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getdomainname, .-getdomainname

	.section	.rodata
_ZZZmbstowcs:
	.string	"mbstowcs"
	.text
	.globl	mbstowcs
	.type	mbstowcs, @function
mbstowcs:
	subl	$16, %esp
	movl	$_ZZZmbstowcs, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mbstowcs, .-mbstowcs

	.section	.rodata
_ZZZgetpriority:
	.string	"getpriority"
	.text
	.globl	getpriority
	.type	getpriority, @function
getpriority:
	subl	$16, %esp
	movl	$_ZZZgetpriority, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpriority, .-getpriority

	.section	.rodata
_ZZZgetsubopt:
	.string	"getsubopt"
	.text
	.globl	getsubopt
	.type	getsubopt, @function
getsubopt:
	subl	$16, %esp
	movl	$_ZZZgetsubopt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getsubopt, .-getsubopt

	.section	.rodata
_ZZZtcgetsid:
	.string	"tcgetsid"
	.text
	.globl	tcgetsid
	.type	tcgetsid, @function
tcgetsid:
	subl	$16, %esp
	movl	$_ZZZtcgetsid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tcgetsid, .-tcgetsid

	.section	.rodata
_ZZZputw:
	.string	"putw"
	.text
	.globl	putw
	.type	putw, @function
putw:
	subl	$16, %esp
	movl	$_ZZZputw, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putw, .-putw

	.section	.rodata
_ZZZioperm:
	.string	"ioperm"
	.text
	.globl	ioperm
	.type	ioperm, @function
ioperm:
	subl	$16, %esp
	movl	$_ZZZioperm, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ioperm, .-ioperm

	.section	.rodata
_ZZZwarnx:
	.string	"warnx"
	.text
	.globl	warnx
	.type	warnx, @function
warnx:
	subl	$16, %esp
	movl	$_ZZZwarnx, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	warnx, .-warnx

	.section	.rodata
_ZZZpmap_unset:
	.string	"pmap_unset"
	.text
	.globl	pmap_unset
	.type	pmap_unset, @function
pmap_unset:
	subl	$16, %esp
	movl	$_ZZZpmap_unset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pmap_unset, .-pmap_unset

	.section	.rodata
_ZZZisastream:
	.string	"isastream"
	.text
	.globl	isastream
	.type	isastream, @function
isastream:
	subl	$16, %esp
	movl	$_ZZZisastream, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isastream, .-isastream

	.section	.rodata
_ZZZvwscanf:
	.string	"vwscanf"
	.text
	.globl	vwscanf
	.type	vwscanf, @function
vwscanf:
	subl	$16, %esp
	movl	$_ZZZvwscanf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vwscanf, .-vwscanf

	.section	.rodata
_ZZZfputws:
	.string	"fputws"
	.text
	.globl	fputws
	.type	fputws, @function
fputws:
	subl	$16, %esp
	movl	$_ZZZfputws, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fputws, .-fputws

	.section	.rodata
_ZZZlistxattr:
	.string	"listxattr"
	.text
	.globl	listxattr
	.type	listxattr, @function
listxattr:
	subl	$16, %esp
	movl	$_ZZZlistxattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	listxattr, .-listxattr

	.section	.rodata
_ZZZinet_netof:
	.string	"inet_netof"
	.text
	.globl	inet_netof
	.type	inet_netof, @function
inet_netof:
	subl	$16, %esp
	movl	$_ZZZinet_netof, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet_netof, .-inet_netof

	.section	.rodata
_ZZZcallrpc:
	.string	"callrpc"
	.text
	.globl	callrpc
	.type	callrpc, @function
callrpc:
	subl	$16, %esp
	movl	$_ZZZcallrpc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	callrpc, .-callrpc

	.section	.rodata
_ZZZsigfillset:
	.string	"sigfillset"
	.text
	.globl	sigfillset
	.type	sigfillset, @function
sigfillset:
	subl	$16, %esp
	movl	$_ZZZsigfillset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigfillset, .-sigfillset

	.section	.rodata
_ZZZgtty:
	.string	"gtty"
	.text
	.globl	gtty
	.type	gtty, @function
gtty:
	subl	$16, %esp
	movl	$_ZZZgtty, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gtty, .-gtty

	.section	.rodata
_ZZZtime:
	.string	"time"
	.text
	.globl	time
	.type	time, @function
time:
	subl	$16, %esp
	movl	$_ZZZtime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	time, .-time

	.section	.rodata
_ZZZgetgrent:
	.string	"getgrent"
	.text
	.globl	getgrent
	.type	getgrent, @function
getgrent:
	subl	$16, %esp
	movl	$_ZZZgetgrent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getgrent, .-getgrent

	.section	.rodata
_ZZZsigorset:
	.string	"sigorset"
	.text
	.globl	sigorset
	.type	sigorset, @function
sigorset:
	subl	$16, %esp
	movl	$_ZZZsigorset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigorset, .-sigorset

	.section	.rodata
_ZZZdrand48_r:
	.string	"drand48_r"
	.text
	.globl	drand48_r
	.type	drand48_r, @function
drand48_r:
	subl	$16, %esp
	movl	$_ZZZdrand48_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	drand48_r, .-drand48_r

	.section	.rodata
_ZZZendnetent:
	.string	"endnetent"
	.text
	.globl	endnetent
	.type	endnetent, @function
endnetent:
	subl	$16, %esp
	movl	$_ZZZendnetent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endnetent, .-endnetent

	.section	.rodata
_ZZZfsetpos64:
	.string	"fsetpos64"
	.text
	.globl	fsetpos64
	.type	fsetpos64, @function
fsetpos64:
	subl	$16, %esp
	movl	$_ZZZfsetpos64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fsetpos64, .-fsetpos64

	.section	.rodata
_ZZZhsearch_r:
	.string	"hsearch_r"
	.text
	.globl	hsearch_r
	.type	hsearch_r, @function
hsearch_r:
	subl	$16, %esp
	movl	$_ZZZhsearch_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	hsearch_r, .-hsearch_r

	.section	.rodata
_ZZZkey_setsecret:
	.string	"key_setsecret"
	.text
	.globl	key_setsecret
	.type	key_setsecret, @function
key_setsecret:
	subl	$16, %esp
	movl	$_ZZZkey_setsecret, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	key_setsecret, .-key_setsecret

	.section	.rodata
_ZZZdaemon:
	.string	"daemon"
	.text
	.globl	daemon
	.type	daemon, @function
daemon:
	subl	$16, %esp
	movl	$_ZZZdaemon, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	daemon, .-daemon

	.section	.rodata
_ZZZsvc_run:
	.string	"svc_run"
	.text
	.globl	svc_run
	.type	svc_run, @function
svc_run:
	subl	$16, %esp
	movl	$_ZZZsvc_run, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svc_run, .-svc_run

	.section	.rodata
_ZZZshmctl:
	.string	"shmctl"
	.text
	.globl	shmctl
	.type	shmctl, @function
shmctl:
	subl	$16, %esp
	movl	$_ZZZshmctl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	shmctl, .-shmctl

	.section	.rodata
_ZZZinotify_rm_watch:
	.string	"inotify_rm_watch"
	.text
	.globl	inotify_rm_watch
	.type	inotify_rm_watch, @function
inotify_rm_watch:
	subl	$16, %esp
	movl	$_ZZZinotify_rm_watch, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inotify_rm_watch, .-inotify_rm_watch

	.section	.rodata
_ZZZxdr_quad_t:
	.string	"xdr_quad_t"
	.text
	.globl	xdr_quad_t
	.type	xdr_quad_t, @function
xdr_quad_t:
	subl	$16, %esp
	movl	$_ZZZxdr_quad_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_quad_t, .-xdr_quad_t

	.section	.rodata
_ZZZputchar:
	.string	"putchar"
	.text
	.globl	putchar
	.type	putchar, @function
putchar:
	subl	$16, %esp
	movl	$_ZZZputchar, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putchar, .-putchar

	.section	.rodata
_ZZZxdrmem_create:
	.string	"xdrmem_create"
	.text
	.globl	xdrmem_create
	.type	xdrmem_create, @function
xdrmem_create:
	subl	$16, %esp
	movl	$_ZZZxdrmem_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdrmem_create, .-xdrmem_create

	.section	.rodata
_ZZZpthread_mutex_lock:
	.string	"pthread_mutex_lock"
	.text
	.globl	pthread_mutex_lock
	.type	pthread_mutex_lock, @function
pthread_mutex_lock:
	subl	$16, %esp
	movl	$_ZZZpthread_mutex_lock, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_mutex_lock, .-pthread_mutex_lock

	.section	.rodata
_ZZZlisten:
	.string	"listen"
	.text
	.globl	listen
	.type	listen, @function
listen:
	subl	$16, %esp
	movl	$_ZZZlisten, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	listen, .-listen

	.section	.rodata
_ZZZfgets_unlocked:
	.string	"fgets_unlocked"
	.text
	.globl	fgets_unlocked
	.type	fgets_unlocked, @function
fgets_unlocked:
	subl	$16, %esp
	movl	$_ZZZfgets_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fgets_unlocked, .-fgets_unlocked

	.section	.rodata
_ZZZputspent:
	.string	"putspent"
	.text
	.globl	putspent
	.type	putspent, @function
putspent:
	subl	$16, %esp
	movl	$_ZZZputspent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putspent, .-putspent

	.section	.rodata
_ZZZxdr_int32_t:
	.string	"xdr_int32_t"
	.text
	.globl	xdr_int32_t
	.type	xdr_int32_t, @function
xdr_int32_t:
	subl	$16, %esp
	movl	$_ZZZxdr_int32_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_int32_t, .-xdr_int32_t

	.section	.rodata
_ZZZgetrpcent:
	.string	"getrpcent"
	.text
	.globl	getrpcent
	.type	getrpcent, @function
getrpcent:
	subl	$16, %esp
	movl	$_ZZZgetrpcent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getrpcent, .-getrpcent

	.section	.rodata
_ZZZgetsgent_r:
	.string	"getsgent_r"
	.text
	.globl	getsgent_r
	.type	getsgent_r, @function
getsgent_r:
	subl	$16, %esp
	movl	$_ZZZgetsgent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getsgent_r, .-getsgent_r

	.section	.rodata
_ZZZshmdt:
	.string	"shmdt"
	.text
	.globl	shmdt
	.type	shmdt, @function
shmdt:
	subl	$16, %esp
	movl	$_ZZZshmdt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	shmdt, .-shmdt

	.section	.rodata
_ZZZrealloc:
	.string	"realloc"
	.text
	.globl	realloc
	.type	realloc, @function
realloc:
	subl	$16, %esp
	movl	$_ZZZrealloc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	realloc, .-realloc

	.section	.rodata
_ZZZif_nameindex:
	.string	"if_nameindex"
	.text
	.globl	if_nameindex
	.type	if_nameindex, @function
if_nameindex:
	subl	$16, %esp
	movl	$_ZZZif_nameindex, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	if_nameindex, .-if_nameindex

	.section	.rodata
_ZZZrewinddir:
	.string	"rewinddir"
	.text
	.globl	rewinddir
	.type	rewinddir, @function
rewinddir:
	subl	$16, %esp
	movl	$_ZZZrewinddir, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rewinddir, .-rewinddir

	.section	.rodata
_ZZZstrtold:
	.string	"strtold"
	.text
	.globl	strtold
	.type	strtold, @function
strtold:
	subl	$16, %esp
	movl	$_ZZZstrtold, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strtold, .-strtold

	.section	.rodata
_ZZZxdr_key_netstres:
	.string	"xdr_key_netstres"
	.text
	.globl	xdr_key_netstres
	.type	xdr_key_netstres, @function
xdr_key_netstres:
	subl	$16, %esp
	movl	$_ZZZxdr_key_netstres, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_key_netstres, .-xdr_key_netstres

	.section	.rodata
_ZZZgetaliasent_r:
	.string	"getaliasent_r"
	.text
	.globl	getaliasent_r
	.type	getaliasent_r, @function
getaliasent_r:
	subl	$16, %esp
	movl	$_ZZZgetaliasent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getaliasent_r, .-getaliasent_r

	.section	.rodata
_ZZZprlimit:
	.string	"prlimit"
	.text
	.globl	prlimit
	.type	prlimit, @function
prlimit:
	subl	$16, %esp
	movl	$_ZZZprlimit, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	prlimit, .-prlimit

	.section	.rodata
_ZZZclock:
	.string	"clock"
	.text
	.globl	clock
	.type	clock, @function
clock:
	subl	$16, %esp
	movl	$_ZZZclock, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clock, .-clock

	.section	.rodata
_ZZZtowupper:
	.string	"towupper"
	.text
	.globl	towupper
	.type	towupper, @function
towupper:
	subl	$16, %esp
	movl	$_ZZZtowupper, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	towupper, .-towupper

	.section	.rodata
_ZZZsockatmark:
	.string	"sockatmark"
	.text
	.globl	sockatmark
	.type	sockatmark, @function
sockatmark:
	subl	$16, %esp
	movl	$_ZZZsockatmark, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sockatmark, .-sockatmark

	.section	.rodata
_ZZZxdr_replymsg:
	.string	"xdr_replymsg"
	.text
	.globl	xdr_replymsg
	.type	xdr_replymsg, @function
xdr_replymsg:
	subl	$16, %esp
	movl	$_ZZZxdr_replymsg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_replymsg, .-xdr_replymsg

	.section	.rodata
_ZZZputmsg:
	.string	"putmsg"
	.text
	.globl	putmsg
	.type	putmsg, @function
putmsg:
	subl	$16, %esp
	movl	$_ZZZputmsg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putmsg, .-putmsg

	.section	.rodata
_ZZZabort:
	.string	"abort"
	.text
	.globl	abort
	.type	abort, @function
abort:
	subl	$16, %esp
	movl	$_ZZZabort, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	abort, .-abort

	.section	.rodata
_ZZZxdr_u_short:
	.string	"xdr_u_short"
	.text
	.globl	xdr_u_short
	.type	xdr_u_short, @function
xdr_u_short:
	subl	$16, %esp
	movl	$_ZZZxdr_u_short, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_u_short, .-xdr_u_short

	.section	.rodata
_ZZZstrtoll:
	.string	"strtoll"
	.text
	.globl	strtoll
	.type	strtoll, @function
strtoll:
	subl	$16, %esp
	movl	$_ZZZstrtoll, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strtoll, .-strtoll

	.section	.rodata
_ZZZsvc_getreq_common:
	.string	"svc_getreq_common"
	.text
	.globl	svc_getreq_common
	.type	svc_getreq_common, @function
svc_getreq_common:
	subl	$16, %esp
	movl	$_ZZZsvc_getreq_common, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svc_getreq_common, .-svc_getreq_common

	.section	.rodata
_ZZZwcstoumax:
	.string	"wcstoumax"
	.text
	.globl	wcstoumax
	.type	wcstoumax, @function
wcstoumax:
	subl	$16, %esp
	movl	$_ZZZwcstoumax, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcstoumax, .-wcstoumax

	.section	.rodata
_ZZZdiv:
	.string	"div"
	.text
	.globl	div
	.type	div, @function
div:
	subl	$16, %esp
	movl	$_ZZZdiv, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	div, .-div

	.section	.rodata
_ZZZstrpbrk:
	.string	"strpbrk"
	.text
	.globl	strpbrk
	.type	strpbrk, @function
strpbrk:
	subl	$16, %esp
	movl	$_ZZZstrpbrk, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strpbrk, .-strpbrk

	.section	.rodata
_ZZZether_aton:
	.string	"ether_aton"
	.text
	.globl	ether_aton
	.type	ether_aton, @function
ether_aton:
	subl	$16, %esp
	movl	$_ZZZether_aton, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ether_aton, .-ether_aton

	.section	.rodata
_ZZZtolower:
	.string	"tolower"
	.text
	.globl	tolower
	.type	tolower, @function
tolower:
	subl	$16, %esp
	movl	$_ZZZtolower, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tolower, .-tolower

	.section	.rodata
_ZZZpopen:
	.string	"popen"
	.text
	.globl	popen
	.type	popen, @function
popen:
	subl	$16, %esp
	movl	$_ZZZpopen, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	popen, .-popen

	.section	.rodata
_ZZZruserok_af:
	.string	"ruserok_af"
	.text
	.globl	ruserok_af
	.type	ruserok_af, @function
ruserok_af:
	subl	$16, %esp
	movl	$_ZZZruserok_af, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ruserok_af, .-ruserok_af

	.section	.rodata
_ZZZlsetxattr:
	.string	"lsetxattr"
	.text
	.globl	lsetxattr
	.type	lsetxattr, @function
lsetxattr:
	subl	$16, %esp
	movl	$_ZZZlsetxattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lsetxattr, .-lsetxattr

	.section	.rodata
_ZZZsetttyent:
	.string	"setttyent"
	.text
	.globl	setttyent
	.type	setttyent, @function
setttyent:
	subl	$16, %esp
	movl	$_ZZZsetttyent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setttyent, .-setttyent

	.section	.rodata
_ZZZmalloc_info:
	.string	"malloc_info"
	.text
	.globl	malloc_info
	.type	malloc_info, @function
malloc_info:
	subl	$16, %esp
	movl	$_ZZZmalloc_info, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	malloc_info, .-malloc_info

	.section	.rodata
_ZZZsetsgent:
	.string	"setsgent"
	.text
	.globl	setsgent
	.type	setsgent, @function
setsgent:
	subl	$16, %esp
	movl	$_ZZZsetsgent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setsgent, .-setsgent

	.section	.rodata
_ZZZgetpid:
	.string	"getpid"
	.text
	.globl	getpid
	.type	getpid, @function
getpid:
	subl	$16, %esp
	movl	$_ZZZgetpid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpid, .-getpid

	.section	.rodata
_ZZZstrspn:
	.string	"strspn"
	.text
	.globl	strspn
	.type	strspn, @function
strspn:
	subl	$16, %esp
	movl	$_ZZZstrspn, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strspn, .-strspn

	.section	.rodata
_ZZZpthread_condattr_init:
	.string	"pthread_condattr_init"
	.text
	.globl	pthread_condattr_init
	.type	pthread_condattr_init, @function
pthread_condattr_init:
	subl	$16, %esp
	movl	$_ZZZpthread_condattr_init, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_condattr_init, .-pthread_condattr_init

	.section	.rodata
_ZZZposix_fallocate64:
	.string	"posix_fallocate64"
	.text
	.globl	posix_fallocate64
	.type	posix_fallocate64, @function
posix_fallocate64:
	subl	$16, %esp
	movl	$_ZZZposix_fallocate64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_fallocate64, .-posix_fallocate64

	.section	.rodata
_ZZZsvcraw_create:
	.string	"svcraw_create"
	.text
	.globl	svcraw_create
	.type	svcraw_create, @function
svcraw_create:
	subl	$16, %esp
	movl	$_ZZZsvcraw_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcraw_create, .-svcraw_create

	.section	.rodata
_ZZZposix_fallocate64:
	.string	"posix_fallocate64"
	.text
	.globl	posix_fallocate64
	.type	posix_fallocate64, @function
posix_fallocate64:
	subl	$16, %esp
	movl	$_ZZZposix_fallocate64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_fallocate64, .-posix_fallocate64

	.section	.rodata
_ZZZfanotify_init:
	.string	"fanotify_init"
	.text
	.globl	fanotify_init
	.type	fanotify_init, @function
fanotify_init:
	subl	$16, %esp
	movl	$_ZZZfanotify_init, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fanotify_init, .-fanotify_init

	.section	.rodata
_ZZZfgetpos:
	.string	"fgetpos"
	.text
	.globl	fgetpos
	.type	fgetpos, @function
fgetpos:
	subl	$16, %esp
	movl	$_ZZZfgetpos, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fgetpos, .-fgetpos

	.section	.rodata
_ZZZsvc_exit:
	.string	"svc_exit"
	.text
	.globl	svc_exit
	.type	svc_exit, @function
svc_exit:
	subl	$16, %esp
	movl	$_ZZZsvc_exit, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svc_exit, .-svc_exit

	.section	.rodata
_ZZZcreat64:
	.string	"creat64"
	.text
	.globl	creat64
	.type	creat64, @function
creat64:
	subl	$16, %esp
	movl	$_ZZZcreat64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	creat64, .-creat64

	.section	.rodata
_ZZZinet_pton:
	.string	"inet_pton"
	.text
	.globl	inet_pton
	.type	inet_pton, @function
inet_pton:
	subl	$16, %esp
	movl	$_ZZZinet_pton, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet_pton, .-inet_pton

	.section	.rodata
_ZZZstrftime:
	.string	"strftime"
	.text
	.globl	strftime
	.type	strftime, @function
strftime:
	subl	$16, %esp
	movl	$_ZZZstrftime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strftime, .-strftime

	.section	.rodata
_ZZZlockf64:
	.string	"lockf64"
	.text
	.globl	lockf64
	.type	lockf64, @function
lockf64:
	subl	$16, %esp
	movl	$_ZZZlockf64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lockf64, .-lockf64

	.section	.rodata
_ZZZxencrypt:
	.string	"xencrypt"
	.text
	.globl	xencrypt
	.type	xencrypt, @function
xencrypt:
	subl	$16, %esp
	movl	$_ZZZxencrypt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xencrypt, .-xencrypt

	.section	.rodata
_ZZZputpmsg:
	.string	"putpmsg"
	.text
	.globl	putpmsg
	.type	putpmsg, @function
putpmsg:
	subl	$16, %esp
	movl	$_ZZZputpmsg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putpmsg, .-putpmsg

	.section	.rodata
_ZZZxdr_uint16_t:
	.string	"xdr_uint16_t"
	.text
	.globl	xdr_uint16_t
	.type	xdr_uint16_t, @function
xdr_uint16_t:
	subl	$16, %esp
	movl	$_ZZZxdr_uint16_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_uint16_t, .-xdr_uint16_t

	.section	.rodata
_ZZZpthread_attr_getschedpara:
	.string	"pthread_attr_getschedpara"
	.text
	.globl	pthread_attr_getschedpara
	.type	pthread_attr_getschedpara, @function
pthread_attr_getschedpara:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_getschedpara, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_getschedpara, .-pthread_attr_getschedpara

	.section	.rodata
_ZZZpthread_mutex_destroy:
	.string	"pthread_mutex_destroy"
	.text
	.globl	pthread_mutex_destroy
	.type	pthread_mutex_destroy, @function
pthread_mutex_destroy:
	subl	$16, %esp
	movl	$_ZZZpthread_mutex_destroy, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_mutex_destroy, .-pthread_mutex_destroy

	.section	.rodata
_ZZZvlimit:
	.string	"vlimit"
	.text
	.globl	vlimit
	.type	vlimit, @function
vlimit:
	subl	$16, %esp
	movl	$_ZZZvlimit, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vlimit, .-vlimit

	.section	.rodata
_ZZZclntunix_create:
	.string	"clntunix_create"
	.text
	.globl	clntunix_create
	.type	clntunix_create, @function
clntunix_create:
	subl	$16, %esp
	movl	$_ZZZclntunix_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clntunix_create, .-clntunix_create

	.section	.rodata
_ZZZprintf:
	.string	"printf"
	.text
	.globl	printf
	.type	printf, @function
printf:
	subl	$16, %esp
	movl	$_ZZZprintf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	printf, .-printf

	.section	.rodata
_ZZZether_ntoa_r:
	.string	"ether_ntoa_r"
	.text
	.globl	ether_ntoa_r
	.type	ether_ntoa_r, @function
ether_ntoa_r:
	subl	$16, %esp
	movl	$_ZZZether_ntoa_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ether_ntoa_r, .-ether_ntoa_r

	.section	.rodata
_ZZZquick_exit:
	.string	"quick_exit"
	.text
	.globl	quick_exit
	.type	quick_exit, @function
quick_exit:
	subl	$16, %esp
	movl	$_ZZZquick_exit, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	quick_exit, .-quick_exit

	.section	.rodata
_ZZZgetnetbyname:
	.string	"getnetbyname"
	.text
	.globl	getnetbyname
	.type	getnetbyname, @function
getnetbyname:
	subl	$16, %esp
	movl	$_ZZZgetnetbyname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getnetbyname, .-getnetbyname

	.section	.rodata
_ZZZmkstemp:
	.string	"mkstemp"
	.text
	.globl	mkstemp
	.type	mkstemp, @function
mkstemp:
	subl	$16, %esp
	movl	$_ZZZmkstemp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkstemp, .-mkstemp

	.section	.rodata
_ZZZstatvfs:
	.string	"statvfs"
	.text
	.globl	statvfs
	.type	statvfs, @function
statvfs:
	subl	$16, %esp
	movl	$_ZZZstatvfs, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	statvfs, .-statvfs

	.section	.rodata
_ZZZrewind:
	.string	"rewind"
	.text
	.globl	rewind
	.type	rewind, @function
rewind:
	subl	$16, %esp
	movl	$_ZZZrewind, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rewind, .-rewind

	.section	.rodata
_ZZZllabs:
	.string	"llabs"
	.text
	.globl	llabs
	.type	llabs, @function
llabs:
	subl	$16, %esp
	movl	$_ZZZllabs, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	llabs, .-llabs

	.section	.rodata
_ZZZwcscspn:
	.string	"wcscspn"
	.text
	.globl	wcscspn
	.type	wcscspn, @function
wcscspn:
	subl	$16, %esp
	movl	$_ZZZwcscspn, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcscspn, .-wcscspn

	.section	.rodata
_ZZZvtimes:
	.string	"vtimes"
	.text
	.globl	vtimes
	.type	vtimes, @function
vtimes:
	subl	$16, %esp
	movl	$_ZZZvtimes, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vtimes, .-vtimes

	.section	.rodata
_ZZZinet6_opt_finish:
	.string	"inet6_opt_finish"
	.text
	.globl	inet6_opt_finish
	.type	inet6_opt_finish, @function
inet6_opt_finish:
	subl	$16, %esp
	movl	$_ZZZinet6_opt_finish, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_opt_finish, .-inet6_opt_finish

	.section	.rodata
_ZZZsetjmp:
	.string	"setjmp"
	.text
	.globl	setjmp
	.type	setjmp, @function
setjmp:
	subl	$16, %esp
	movl	$_ZZZsetjmp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setjmp, .-setjmp

	.section	.rodata
_ZZZisspace:
	.string	"isspace"
	.text
	.globl	isspace
	.type	isspace, @function
isspace:
	subl	$16, %esp
	movl	$_ZZZisspace, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isspace, .-isspace

	.section	.rodata
_ZZZstrtod:
	.string	"strtod"
	.text
	.globl	strtod
	.type	strtod, @function
strtod:
	subl	$16, %esp
	movl	$_ZZZstrtod, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strtod, .-strtod

	.section	.rodata
_ZZZtmpnam_r:
	.string	"tmpnam_r"
	.text
	.globl	tmpnam_r
	.type	tmpnam_r, @function
tmpnam_r:
	subl	$16, %esp
	movl	$_ZZZtmpnam_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tmpnam_r, .-tmpnam_r

	.section	.rodata
_ZZZfallocate:
	.string	"fallocate"
	.text
	.globl	fallocate
	.type	fallocate, @function
fallocate:
	subl	$16, %esp
	movl	$_ZZZfallocate, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fallocate, .-fallocate

	.section	.rodata
_ZZZsetutxent:
	.string	"setutxent"
	.text
	.globl	setutxent
	.type	setutxent, @function
setutxent:
	subl	$16, %esp
	movl	$_ZZZsetutxent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setutxent, .-setutxent

	.section	.rodata
_ZZZfgetws:
	.string	"fgetws"
	.text
	.globl	fgetws
	.type	fgetws, @function
fgetws:
	subl	$16, %esp
	movl	$_ZZZfgetws, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fgetws, .-fgetws

	.section	.rodata
_ZZZstrtof:
	.string	"strtof"
	.text
	.globl	strtof
	.type	strtof, @function
strtof:
	subl	$16, %esp
	movl	$_ZZZstrtof, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strtof, .-strtof

	.section	.rodata
_ZZZgmtime:
	.string	"gmtime"
	.text
	.globl	gmtime
	.type	gmtime, @function
gmtime:
	subl	$16, %esp
	movl	$_ZZZgmtime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gmtime, .-gmtime

	.section	.rodata
_ZZZffs:
	.string	"ffs"
	.text
	.globl	ffs
	.type	ffs, @function
ffs:
	subl	$16, %esp
	movl	$_ZZZffs, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ffs, .-ffs

	.section	.rodata
_ZZZxdr_opaque_auth:
	.string	"xdr_opaque_auth"
	.text
	.globl	xdr_opaque_auth
	.type	xdr_opaque_auth, @function
xdr_opaque_auth:
	subl	$16, %esp
	movl	$_ZZZxdr_opaque_auth, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_opaque_auth, .-xdr_opaque_auth

	.section	.rodata
_ZZZenvz_add:
	.string	"envz_add"
	.text
	.globl	envz_add
	.type	envz_add, @function
envz_add:
	subl	$16, %esp
	movl	$_ZZZenvz_add, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	envz_add, .-envz_add

	.section	.rodata
_ZZZputsgent:
	.string	"putsgent"
	.text
	.globl	putsgent
	.type	putsgent, @function
putsgent:
	subl	$16, %esp
	movl	$_ZZZputsgent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putsgent, .-putsgent

	.section	.rodata
_ZZZstrtok:
	.string	"strtok"
	.text
	.globl	strtok
	.type	strtok, @function
strtok:
	subl	$16, %esp
	movl	$_ZZZstrtok, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strtok, .-strtok

	.section	.rodata
_ZZZendpwent:
	.string	"endpwent"
	.text
	.globl	endpwent
	.type	endpwent, @function
endpwent:
	subl	$16, %esp
	movl	$_ZZZendpwent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endpwent, .-endpwent

	.section	.rodata
_ZZZstrtol:
	.string	"strtol"
	.text
	.globl	strtol
	.type	strtol, @function
strtol:
	subl	$16, %esp
	movl	$_ZZZstrtol, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strtol, .-strtol

	.section	.rodata
_ZZZfts_close:
	.string	"fts_close"
	.text
	.globl	fts_close
	.type	fts_close, @function
fts_close:
	subl	$16, %esp
	movl	$_ZZZfts_close, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fts_close, .-fts_close

	.section	.rodata
_ZZZendnetgrent:
	.string	"endnetgrent"
	.text
	.globl	endnetgrent
	.type	endnetgrent, @function
endnetgrent:
	subl	$16, %esp
	movl	$_ZZZendnetgrent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endnetgrent, .-endnetgrent

	.section	.rodata
_ZZZsetsourcefilter:
	.string	"setsourcefilter"
	.text
	.globl	setsourcefilter
	.type	setsourcefilter, @function
setsourcefilter:
	subl	$16, %esp
	movl	$_ZZZsetsourcefilter, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setsourcefilter, .-setsourcefilter

	.section	.rodata
_ZZZctime_r:
	.string	"ctime_r"
	.text
	.globl	ctime_r
	.type	ctime_r, @function
ctime_r:
	subl	$16, %esp
	movl	$_ZZZctime_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ctime_r, .-ctime_r

	.section	.rodata
_ZZZgetgrnam_r:
	.string	"getgrnam_r"
	.text
	.globl	getgrnam_r
	.type	getgrnam_r, @function
getgrnam_r:
	subl	$16, %esp
	movl	$_ZZZgetgrnam_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getgrnam_r, .-getgrnam_r

	.section	.rodata
_ZZZxdr_u_quad_t:
	.string	"xdr_u_quad_t"
	.text
	.globl	xdr_u_quad_t
	.type	xdr_u_quad_t, @function
xdr_u_quad_t:
	subl	$16, %esp
	movl	$_ZZZxdr_u_quad_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_u_quad_t, .-xdr_u_quad_t

	.section	.rodata
_ZZZfstatvfs:
	.string	"fstatvfs"
	.text
	.globl	fstatvfs
	.type	fstatvfs, @function
fstatvfs:
	subl	$16, %esp
	movl	$_ZZZfstatvfs, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fstatvfs, .-fstatvfs

	.section	.rodata
_ZZZpthread_attr_setscope:
	.string	"pthread_attr_setscope"
	.text
	.globl	pthread_attr_setscope
	.type	pthread_attr_setscope, @function
pthread_attr_setscope:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_setscope, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_setscope, .-pthread_attr_setscope

	.section	.rodata
_ZZZsvcudp_create:
	.string	"svcudp_create"
	.text
	.globl	svcudp_create
	.type	svcudp_create, @function
svcudp_create:
	subl	$16, %esp
	movl	$_ZZZsvcudp_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcudp_create, .-svcudp_create

	.section	.rodata
_ZZZsyslog:
	.string	"syslog"
	.text
	.globl	syslog
	.type	syslog, @function
syslog:
	subl	$16, %esp
	movl	$_ZZZsyslog, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	syslog, .-syslog

	.section	.rodata
_ZZZposix_spawnattr_destroy:
	.string	"posix_spawnattr_destroy"
	.text
	.globl	posix_spawnattr_destroy
	.type	posix_spawnattr_destroy, @function
posix_spawnattr_destroy:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_destroy, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_destroy, .-posix_spawnattr_destroy

	.section	.rodata
_ZZZfsetpos:
	.string	"fsetpos"
	.text
	.globl	fsetpos
	.type	fsetpos, @function
fsetpos:
	subl	$16, %esp
	movl	$_ZZZfsetpos, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fsetpos, .-fsetpos

	.section	.rodata
_ZZZinet6_option_alloc:
	.string	"inet6_option_alloc"
	.text
	.globl	inet6_option_alloc
	.type	inet6_option_alloc, @function
inet6_option_alloc:
	subl	$16, %esp
	movl	$_ZZZinet6_option_alloc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_option_alloc, .-inet6_option_alloc

	.section	.rodata
_ZZZdysize:
	.string	"dysize"
	.text
	.globl	dysize
	.type	dysize, @function
dysize:
	subl	$16, %esp
	movl	$_ZZZdysize, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	dysize, .-dysize

	.section	.rodata
_ZZZgetspent:
	.string	"getspent"
	.text
	.globl	getspent
	.type	getspent, @function
getspent:
	subl	$16, %esp
	movl	$_ZZZgetspent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getspent, .-getspent

	.section	.rodata
_ZZZpthread_attr_setdetachsta:
	.string	"pthread_attr_setdetachsta"
	.text
	.globl	pthread_attr_setdetachsta
	.type	pthread_attr_setdetachsta, @function
pthread_attr_setdetachsta:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_setdetachsta, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_setdetachsta, .-pthread_attr_setdetachsta

	.section	.rodata
_ZZZfgetxattr:
	.string	"fgetxattr"
	.text
	.globl	fgetxattr
	.type	fgetxattr, @function
fgetxattr:
	subl	$16, %esp
	movl	$_ZZZfgetxattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fgetxattr, .-fgetxattr

	.section	.rodata
_ZZZisprint:
	.string	"isprint"
	.text
	.globl	isprint
	.type	isprint, @function
isprint:
	subl	$16, %esp
	movl	$_ZZZisprint, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isprint, .-isprint

	.section	.rodata
_ZZZposix_fadvise:
	.string	"posix_fadvise"
	.text
	.globl	posix_fadvise
	.type	posix_fadvise, @function
posix_fadvise:
	subl	$16, %esp
	movl	$_ZZZposix_fadvise, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_fadvise, .-posix_fadvise

	.section	.rodata
_ZZZgetloadavg:
	.string	"getloadavg"
	.text
	.globl	getloadavg
	.type	getloadavg, @function
getloadavg:
	subl	$16, %esp
	movl	$_ZZZgetloadavg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getloadavg, .-getloadavg

	.section	.rodata
_ZZZexecle:
	.string	"execle"
	.text
	.globl	execle
	.type	execle, @function
execle:
	subl	$16, %esp
	movl	$_ZZZexecle, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	execle, .-execle

	.section	.rodata
_ZZZwcsftime:
	.string	"wcsftime"
	.text
	.globl	wcsftime
	.type	wcsftime, @function
wcsftime:
	subl	$16, %esp
	movl	$_ZZZwcsftime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcsftime, .-wcsftime

	.section	.rodata
_ZZZxdr_void:
	.string	"xdr_void"
	.text
	.globl	xdr_void
	.type	xdr_void, @function
xdr_void:
	subl	$16, %esp
	movl	$_ZZZxdr_void, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_void, .-xdr_void

	.section	.rodata
_ZZZldiv:
	.string	"ldiv"
	.text
	.globl	ldiv
	.type	ldiv, @function
ldiv:
	subl	$16, %esp
	movl	$_ZZZldiv, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ldiv, .-ldiv

	.section	.rodata
_ZZZcfsetispeed:
	.string	"cfsetispeed"
	.text
	.globl	cfsetispeed
	.type	cfsetispeed, @function
cfsetispeed:
	subl	$16, %esp
	movl	$_ZZZcfsetispeed, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	cfsetispeed, .-cfsetispeed

	.section	.rodata
_ZZZether_ntoa:
	.string	"ether_ntoa"
	.text
	.globl	ether_ntoa
	.type	ether_ntoa, @function
ether_ntoa:
	subl	$16, %esp
	movl	$_ZZZether_ntoa, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ether_ntoa, .-ether_ntoa

	.section	.rodata
_ZZZxdr_key_netstarg:
	.string	"xdr_key_netstarg"
	.text
	.globl	xdr_key_netstarg
	.type	xdr_key_netstarg, @function
xdr_key_netstarg:
	subl	$16, %esp
	movl	$_ZZZxdr_key_netstarg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_key_netstarg, .-xdr_key_netstarg

	.section	.rodata
_ZZZtee:
	.string	"tee"
	.text
	.globl	tee
	.type	tee, @function
tee:
	subl	$16, %esp
	movl	$_ZZZtee, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tee, .-tee

	.section	.rodata
_ZZZparse_printf_format:
	.string	"parse_printf_format"
	.text
	.globl	parse_printf_format
	.type	parse_printf_format, @function
parse_printf_format:
	subl	$16, %esp
	movl	$_ZZZparse_printf_format, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	parse_printf_format, .-parse_printf_format

	.section	.rodata
_ZZZstrfry:
	.string	"strfry"
	.text
	.globl	strfry
	.type	strfry, @function
strfry:
	subl	$16, %esp
	movl	$_ZZZstrfry, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strfry, .-strfry

	.section	.rodata
_ZZZreboot:
	.string	"reboot"
	.text
	.globl	reboot
	.type	reboot, @function
reboot:
	subl	$16, %esp
	movl	$_ZZZreboot, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	reboot, .-reboot

	.section	.rodata
_ZZZgetaliasbyname_r:
	.string	"getaliasbyname_r"
	.text
	.globl	getaliasbyname_r
	.type	getaliasbyname_r, @function
getaliasbyname_r:
	subl	$16, %esp
	movl	$_ZZZgetaliasbyname_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getaliasbyname_r, .-getaliasbyname_r

	.section	.rodata
_ZZZjrand48:
	.string	"jrand48"
	.text
	.globl	jrand48
	.type	jrand48, @function
jrand48:
	subl	$16, %esp
	movl	$_ZZZjrand48, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	jrand48, .-jrand48

	.section	.rodata
_ZZZexeclp:
	.string	"execlp"
	.text
	.globl	execlp
	.type	execlp, @function
execlp:
	subl	$16, %esp
	movl	$_ZZZexeclp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	execlp, .-execlp

	.section	.rodata
_ZZZgethostbyname_r:
	.string	"gethostbyname_r"
	.text
	.globl	gethostbyname_r
	.type	gethostbyname_r, @function
gethostbyname_r:
	subl	$16, %esp
	movl	$_ZZZgethostbyname_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gethostbyname_r, .-gethostbyname_r

	.section	.rodata
_ZZZswab:
	.string	"swab"
	.text
	.globl	swab
	.type	swab, @function
swab:
	subl	$16, %esp
	movl	$_ZZZswab, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	swab, .-swab

	.section	.rodata
_ZZZseekdir:
	.string	"seekdir"
	.text
	.globl	seekdir
	.type	seekdir, @function
seekdir:
	subl	$16, %esp
	movl	$_ZZZseekdir, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	seekdir, .-seekdir

	.section	.rodata
_ZZZalphasort64:
	.string	"alphasort64"
	.text
	.globl	alphasort64
	.type	alphasort64, @function
alphasort64:
	subl	$16, %esp
	movl	$_ZZZalphasort64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	alphasort64, .-alphasort64

	.section	.rodata
_ZZZpmap_getport:
	.string	"pmap_getport"
	.text
	.globl	pmap_getport
	.type	pmap_getport, @function
pmap_getport:
	subl	$16, %esp
	movl	$_ZZZpmap_getport, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pmap_getport, .-pmap_getport

	.section	.rodata
_ZZZalphasort64:
	.string	"alphasort64"
	.text
	.globl	alphasort64
	.type	alphasort64, @function
alphasort64:
	subl	$16, %esp
	movl	$_ZZZalphasort64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	alphasort64, .-alphasort64

	.section	.rodata
_ZZZfdatasync:
	.string	"fdatasync"
	.text
	.globl	fdatasync
	.type	fdatasync, @function
fdatasync:
	subl	$16, %esp
	movl	$_ZZZfdatasync, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fdatasync, .-fdatasync

	.section	.rodata
_ZZZauthdes_getucred:
	.string	"authdes_getucred"
	.text
	.globl	authdes_getucred
	.type	authdes_getucred, @function
authdes_getucred:
	subl	$16, %esp
	movl	$_ZZZauthdes_getucred, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	authdes_getucred, .-authdes_getucred

	.section	.rodata
_ZZZtruncate64:
	.string	"truncate64"
	.text
	.globl	truncate64
	.type	truncate64, @function
truncate64:
	subl	$16, %esp
	movl	$_ZZZtruncate64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	truncate64, .-truncate64

	.section	.rodata
_ZZZstrtoumax:
	.string	"strtoumax"
	.text
	.globl	strtoumax
	.type	strtoumax, @function
strtoumax:
	subl	$16, %esp
	movl	$_ZZZstrtoumax, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strtoumax, .-strtoumax

	.section	.rodata
_ZZZgetnetent_r:
	.string	"getnetent_r"
	.text
	.globl	getnetent_r
	.type	getnetent_r, @function
getnetent_r:
	subl	$16, %esp
	movl	$_ZZZgetnetent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getnetent_r, .-getnetent_r

	.section	.rodata
_ZZZposix_spawnattr_setflags:
	.string	"posix_spawnattr_setflags"
	.text
	.globl	posix_spawnattr_setflags
	.type	posix_spawnattr_setflags, @function
posix_spawnattr_setflags:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_setflags, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_setflags, .-posix_spawnattr_setflags

	.section	.rodata
_ZZZgetnetent_r:
	.string	"getnetent_r"
	.text
	.globl	getnetent_r
	.type	getnetent_r, @function
getnetent_r:
	subl	$16, %esp
	movl	$_ZZZgetnetent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getnetent_r, .-getnetent_r

	.section	.rodata
_ZZZsched_setaffinity:
	.string	"sched_setaffinity"
	.text
	.globl	sched_setaffinity
	.type	sched_setaffinity, @function
sched_setaffinity:
	subl	$16, %esp
	movl	$_ZZZsched_setaffinity, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sched_setaffinity, .-sched_setaffinity

	.section	.rodata
_ZZZgetpwnam:
	.string	"getpwnam"
	.text
	.globl	getpwnam
	.type	getpwnam, @function
getpwnam:
	subl	$16, %esp
	movl	$_ZZZgetpwnam, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpwnam, .-getpwnam

	.section	.rodata
_ZZZinet6_option_append:
	.string	"inet6_option_append"
	.text
	.globl	inet6_option_append
	.type	inet6_option_append, @function
inet6_option_append:
	subl	$16, %esp
	movl	$_ZZZinet6_option_append, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_option_append, .-inet6_option_append

	.section	.rodata
_ZZZgetmsg:
	.string	"getmsg"
	.text
	.globl	getmsg
	.type	getmsg, @function
getmsg:
	subl	$16, %esp
	movl	$_ZZZgetmsg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getmsg, .-getmsg

	.section	.rodata
_ZZZrenameat:
	.string	"renameat"
	.text
	.globl	renameat
	.type	renameat, @function
renameat:
	subl	$16, %esp
	movl	$_ZZZrenameat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	renameat, .-renameat

	.section	.rodata
_ZZZfutimens:
	.string	"futimens"
	.text
	.globl	futimens
	.type	futimens, @function
futimens:
	subl	$16, %esp
	movl	$_ZZZfutimens, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	futimens, .-futimens

	.section	.rodata
_ZZZstrlen:
	.string	"strlen"
	.text
	.globl	strlen
	.type	strlen, @function
strlen:
	subl	$16, %esp
	movl	$_ZZZstrlen, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strlen, .-strlen

	.section	.rodata
_ZZZwcschr:
	.string	"wcschr"
	.text
	.globl	wcschr
	.type	wcschr, @function
wcschr:
	subl	$16, %esp
	movl	$_ZZZwcschr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcschr, .-wcschr

	.section	.rodata
_ZZZisxdigit:
	.string	"isxdigit"
	.text
	.globl	isxdigit
	.type	isxdigit, @function
isxdigit:
	subl	$16, %esp
	movl	$_ZZZisxdigit, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isxdigit, .-isxdigit

	.section	.rodata
_ZZZlockf:
	.string	"lockf"
	.text
	.globl	lockf
	.type	lockf, @function
lockf:
	subl	$16, %esp
	movl	$_ZZZlockf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lockf, .-lockf

	.section	.rodata
_ZZZether_line:
	.string	"ether_line"
	.text
	.globl	ether_line
	.type	ether_line, @function
ether_line:
	subl	$16, %esp
	movl	$_ZZZether_line, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ether_line, .-ether_line

	.section	.rodata
_ZZZxdr_authdes_cred:
	.string	"xdr_authdes_cred"
	.text
	.globl	xdr_authdes_cred
	.type	xdr_authdes_cred, @function
xdr_authdes_cred:
	subl	$16, %esp
	movl	$_ZZZxdr_authdes_cred, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_authdes_cred, .-xdr_authdes_cred

	.section	.rodata
_ZZZqecvt:
	.string	"qecvt"
	.text
	.globl	qecvt
	.type	qecvt, @function
qecvt:
	subl	$16, %esp
	movl	$_ZZZqecvt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	qecvt, .-qecvt

	.section	.rodata
_ZZZxdr_int8_t:
	.string	"xdr_int8_t"
	.text
	.globl	xdr_int8_t
	.type	xdr_int8_t, @function
xdr_int8_t:
	subl	$16, %esp
	movl	$_ZZZxdr_int8_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_int8_t, .-xdr_int8_t

	.section	.rodata
_ZZZtmpfile:
	.string	"tmpfile"
	.text
	.globl	tmpfile
	.type	tmpfile, @function
tmpfile:
	subl	$16, %esp
	movl	$_ZZZtmpfile, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tmpfile, .-tmpfile

	.section	.rodata
_ZZZenvz_entry:
	.string	"envz_entry"
	.text
	.globl	envz_entry
	.type	envz_entry, @function
envz_entry:
	subl	$16, %esp
	movl	$_ZZZenvz_entry, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	envz_entry, .-envz_entry

	.section	.rodata
_ZZZpivot_root:
	.string	"pivot_root"
	.text
	.globl	pivot_root
	.type	pivot_root, @function
pivot_root:
	subl	$16, %esp
	movl	$_ZZZpivot_root, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pivot_root, .-pivot_root

	.section	.rodata
_ZZZrexec_af:
	.string	"rexec_af"
	.text
	.globl	rexec_af
	.type	rexec_af, @function
rexec_af:
	subl	$16, %esp
	movl	$_ZZZrexec_af, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rexec_af, .-rexec_af

	.section	.rodata
_ZZZxprt_unregister:
	.string	"xprt_unregister"
	.text
	.globl	xprt_unregister
	.type	xprt_unregister, @function
xprt_unregister:
	subl	$16, %esp
	movl	$_ZZZxprt_unregister, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xprt_unregister, .-xprt_unregister

	.section	.rodata
_ZZZxdr_authunix_parms:
	.string	"xdr_authunix_parms"
	.text
	.globl	xdr_authunix_parms
	.type	xdr_authunix_parms, @function
xdr_authunix_parms:
	subl	$16, %esp
	movl	$_ZZZxdr_authunix_parms, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_authunix_parms, .-xdr_authunix_parms

	.section	.rodata
_ZZZgetaliasbyname:
	.string	"getaliasbyname"
	.text
	.globl	getaliasbyname
	.type	getaliasbyname, @function
getaliasbyname:
	subl	$16, %esp
	movl	$_ZZZgetaliasbyname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getaliasbyname, .-getaliasbyname

	.section	.rodata
_ZZZsvcerr_progvers:
	.string	"svcerr_progvers"
	.text
	.globl	svcerr_progvers
	.type	svcerr_progvers, @function
svcerr_progvers:
	subl	$16, %esp
	movl	$_ZZZsvcerr_progvers, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcerr_progvers, .-svcerr_progvers

	.section	.rodata
_ZZZinet6_opt_get_val:
	.string	"inet6_opt_get_val"
	.text
	.globl	inet6_opt_get_val
	.type	inet6_opt_get_val, @function
inet6_opt_get_val:
	subl	$16, %esp
	movl	$_ZZZinet6_opt_get_val, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_opt_get_val, .-inet6_opt_get_val

	.section	.rodata
_ZZZgethostbyname2_r:
	.string	"gethostbyname2_r"
	.text
	.globl	gethostbyname2_r
	.type	gethostbyname2_r, @function
gethostbyname2_r:
	subl	$16, %esp
	movl	$_ZZZgethostbyname2_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gethostbyname2_r, .-gethostbyname2_r

	.section	.rodata
_ZZZposix_spawn_file_actions_:
	.string	"posix_spawn_file_actions_"
	.text
	.globl	posix_spawn_file_actions_
	.type	posix_spawn_file_actions_, @function
posix_spawn_file_actions_:
	subl	$16, %esp
	movl	$_ZZZposix_spawn_file_actions_, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawn_file_actions_, .-posix_spawn_file_actions_

	.section	.rodata
_ZZZgethostbyname2_r:
	.string	"gethostbyname2_r"
	.text
	.globl	gethostbyname2_r
	.type	gethostbyname2_r, @function
gethostbyname2_r:
	subl	$16, %esp
	movl	$_ZZZgethostbyname2_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gethostbyname2_r, .-gethostbyname2_r

	.section	.rodata
_ZZZsetlogmask:
	.string	"setlogmask"
	.text
	.globl	setlogmask
	.type	setlogmask, @function
setlogmask:
	subl	$16, %esp
	movl	$_ZZZsetlogmask, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setlogmask, .-setlogmask

	.section	.rodata
_ZZZxdr_enum:
	.string	"xdr_enum"
	.text
	.globl	xdr_enum
	.type	xdr_enum, @function
xdr_enum:
	subl	$16, %esp
	movl	$_ZZZxdr_enum, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_enum, .-xdr_enum

	.section	.rodata
_ZZZunshare:
	.string	"unshare"
	.text
	.globl	unshare
	.type	unshare, @function
unshare:
	subl	$16, %esp
	movl	$_ZZZunshare, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	unshare, .-unshare

	.section	.rodata
_ZZZfread_unlocked:
	.string	"fread_unlocked"
	.text
	.globl	fread_unlocked
	.type	fread_unlocked, @function
fread_unlocked:
	subl	$16, %esp
	movl	$_ZZZfread_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fread_unlocked, .-fread_unlocked

	.section	.rodata
_ZZZsignalfd:
	.string	"signalfd"
	.text
	.globl	signalfd
	.type	signalfd, @function
signalfd:
	subl	$16, %esp
	movl	$_ZZZsignalfd, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	signalfd, .-signalfd

	.section	.rodata
_ZZZsigemptyset:
	.string	"sigemptyset"
	.text
	.globl	sigemptyset
	.type	sigemptyset, @function
sigemptyset:
	subl	$16, %esp
	movl	$_ZZZsigemptyset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigemptyset, .-sigemptyset

	.section	.rodata
_ZZZinet6_option_next:
	.string	"inet6_option_next"
	.text
	.globl	inet6_option_next
	.type	inet6_option_next, @function
inet6_option_next:
	subl	$16, %esp
	movl	$_ZZZinet6_option_next, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_option_next, .-inet6_option_next

	.section	.rodata
_ZZZopenlog:
	.string	"openlog"
	.text
	.globl	openlog
	.type	openlog, @function
openlog:
	subl	$16, %esp
	movl	$_ZZZopenlog, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	openlog, .-openlog

	.section	.rodata
_ZZZgetaddrinfo:
	.string	"getaddrinfo"
	.text
	.globl	getaddrinfo
	.type	getaddrinfo, @function
getaddrinfo:
	subl	$16, %esp
	movl	$_ZZZgetaddrinfo, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getaddrinfo, .-getaddrinfo

	.section	.rodata
_ZZZgetchar_unlocked:
	.string	"getchar_unlocked"
	.text
	.globl	getchar_unlocked
	.type	getchar_unlocked, @function
getchar_unlocked:
	subl	$16, %esp
	movl	$_ZZZgetchar_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getchar_unlocked, .-getchar_unlocked

	.section	.rodata
_ZZZmemset:
	.string	"memset"
	.text
	.globl	memset
	.type	memset, @function
memset:
	subl	$16, %esp
	movl	$_ZZZmemset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	memset, .-memset

	.section	.rodata
_ZZZdirname:
	.string	"dirname"
	.text
	.globl	dirname
	.type	dirname, @function
dirname:
	subl	$16, %esp
	movl	$_ZZZdirname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	dirname, .-dirname

	.section	.rodata
_ZZZlocaleconv:
	.string	"localeconv"
	.text
	.globl	localeconv
	.type	localeconv, @function
localeconv:
	subl	$16, %esp
	movl	$_ZZZlocaleconv, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	localeconv, .-localeconv

	.section	.rodata
_ZZZcfgetospeed:
	.string	"cfgetospeed"
	.text
	.globl	cfgetospeed
	.type	cfgetospeed, @function
cfgetospeed:
	subl	$16, %esp
	movl	$_ZZZcfgetospeed, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	cfgetospeed, .-cfgetospeed

	.section	.rodata
_ZZZisalnum:
	.string	"isalnum"
	.text
	.globl	isalnum
	.type	isalnum, @function
isalnum:
	subl	$16, %esp
	movl	$_ZZZisalnum, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isalnum, .-isalnum

	.section	.rodata
_ZZZinet6_rth_add:
	.string	"inet6_rth_add"
	.text
	.globl	inet6_rth_add
	.type	inet6_rth_add, @function
inet6_rth_add:
	subl	$16, %esp
	movl	$_ZZZinet6_rth_add, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_rth_add, .-inet6_rth_add

	.section	.rodata
_ZZZswprintf:
	.string	"swprintf"
	.text
	.globl	swprintf
	.type	swprintf, @function
swprintf:
	subl	$16, %esp
	movl	$_ZZZswprintf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	swprintf, .-swprintf

	.section	.rodata
_ZZZgetchar:
	.string	"getchar"
	.text
	.globl	getchar
	.type	getchar, @function
getchar:
	subl	$16, %esp
	movl	$_ZZZgetchar, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getchar, .-getchar

	.section	.rodata
_ZZZwarn:
	.string	"warn"
	.text
	.globl	warn
	.type	warn, @function
warn:
	subl	$16, %esp
	movl	$_ZZZwarn, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	warn, .-warn

	.section	.rodata
_ZZZglob:
	.string	"glob"
	.text
	.globl	glob
	.type	glob, @function
glob:
	subl	$16, %esp
	movl	$_ZZZglob, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	glob, .-glob

	.section	.rodata
_ZZZstrstr:
	.string	"strstr"
	.text
	.globl	strstr
	.type	strstr, @function
strstr:
	subl	$16, %esp
	movl	$_ZZZstrstr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strstr, .-strstr

	.section	.rodata
_ZZZsemtimedop:
	.string	"semtimedop"
	.text
	.globl	semtimedop
	.type	semtimedop, @function
semtimedop:
	subl	$16, %esp
	movl	$_ZZZsemtimedop, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	semtimedop, .-semtimedop

	.section	.rodata
_ZZZstrcspn:
	.string	"strcspn"
	.text
	.globl	strcspn
	.type	strcspn, @function
strcspn:
	subl	$16, %esp
	movl	$_ZZZstrcspn, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strcspn, .-strcspn

	.section	.rodata
_ZZZislower:
	.string	"islower"
	.text
	.globl	islower
	.type	islower, @function
islower:
	subl	$16, %esp
	movl	$_ZZZislower, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	islower, .-islower

	.section	.rodata
_ZZZtcsendbreak:
	.string	"tcsendbreak"
	.text
	.globl	tcsendbreak
	.type	tcsendbreak, @function
tcsendbreak:
	subl	$16, %esp
	movl	$_ZZZtcsendbreak, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tcsendbreak, .-tcsendbreak

	.section	.rodata
_ZZZtelldir:
	.string	"telldir"
	.text
	.globl	telldir
	.type	telldir, @function
telldir:
	subl	$16, %esp
	movl	$_ZZZtelldir, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	telldir, .-telldir

	.section	.rodata
_ZZZutimensat:
	.string	"utimensat"
	.text
	.globl	utimensat
	.type	utimensat, @function
utimensat:
	subl	$16, %esp
	movl	$_ZZZutimensat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	utimensat, .-utimensat

	.section	.rodata
_ZZZfcvt:
	.string	"fcvt"
	.text
	.globl	fcvt
	.type	fcvt, @function
fcvt:
	subl	$16, %esp
	movl	$_ZZZfcvt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fcvt, .-fcvt

	.section	.rodata
_ZZZtcsetattr:
	.string	"tcsetattr"
	.text
	.globl	tcsetattr
	.type	tcsetattr, @function
tcsetattr:
	subl	$16, %esp
	movl	$_ZZZtcsetattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tcsetattr, .-tcsetattr

	.section	.rodata
_ZZZbind:
	.string	"bind"
	.text
	.globl	bind
	.type	bind, @function
bind:
	subl	$16, %esp
	movl	$_ZZZbind, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	bind, .-bind

	.section	.rodata
_ZZZfseek:
	.string	"fseek"
	.text
	.globl	fseek
	.type	fseek, @function
fseek:
	subl	$16, %esp
	movl	$_ZZZfseek, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fseek, .-fseek

	.section	.rodata
_ZZZxdr_float:
	.string	"xdr_float"
	.text
	.globl	xdr_float
	.type	xdr_float, @function
xdr_float:
	subl	$16, %esp
	movl	$_ZZZxdr_float, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_float, .-xdr_float

	.section	.rodata
_ZZZconfstr:
	.string	"confstr"
	.text
	.globl	confstr
	.type	confstr, @function
confstr:
	subl	$16, %esp
	movl	$_ZZZconfstr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	confstr, .-confstr

	.section	.rodata
_ZZZmuntrace:
	.string	"muntrace"
	.text
	.globl	muntrace
	.type	muntrace, @function
muntrace:
	subl	$16, %esp
	movl	$_ZZZmuntrace, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	muntrace, .-muntrace

	.section	.rodata
_ZZZinet6_rth_segments:
	.string	"inet6_rth_segments"
	.text
	.globl	inet6_rth_segments
	.type	inet6_rth_segments, @function
inet6_rth_segments:
	subl	$16, %esp
	movl	$_ZZZinet6_rth_segments, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_rth_segments, .-inet6_rth_segments

	.section	.rodata
_ZZZmemcmp:
	.string	"memcmp"
	.text
	.globl	memcmp
	.type	memcmp, @function
memcmp:
	subl	$16, %esp
	movl	$_ZZZmemcmp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	memcmp, .-memcmp

	.section	.rodata
_ZZZgetsgent:
	.string	"getsgent"
	.text
	.globl	getsgent
	.type	getsgent, @function
getsgent:
	subl	$16, %esp
	movl	$_ZZZgetsgent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getsgent, .-getsgent

	.section	.rodata
_ZZZgetwchar:
	.string	"getwchar"
	.text
	.globl	getwchar
	.type	getwchar, @function
getwchar:
	subl	$16, %esp
	movl	$_ZZZgetwchar, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getwchar, .-getwchar

	.section	.rodata
_ZZZgetnameinfo:
	.string	"getnameinfo"
	.text
	.globl	getnameinfo
	.type	getnameinfo, @function
getnameinfo:
	subl	$16, %esp
	movl	$_ZZZgetnameinfo, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getnameinfo, .-getnameinfo

	.section	.rodata
_ZZZxdr_sizeof:
	.string	"xdr_sizeof"
	.text
	.globl	xdr_sizeof
	.type	xdr_sizeof, @function
xdr_sizeof:
	subl	$16, %esp
	movl	$_ZZZxdr_sizeof, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_sizeof, .-xdr_sizeof

	.section	.rodata
_ZZZputwc:
	.string	"putwc"
	.text
	.globl	putwc
	.type	putwc, @function
putwc:
	subl	$16, %esp
	movl	$_ZZZputwc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putwc, .-putwc

	.section	.rodata
_ZZZgetrpcport:
	.string	"getrpcport"
	.text
	.globl	getrpcport
	.type	getrpcport, @function
getrpcport:
	subl	$16, %esp
	movl	$_ZZZgetrpcport, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getrpcport, .-getrpcport

	.section	.rodata
_ZZZendgrent:
	.string	"endgrent"
	.text
	.globl	endgrent
	.type	endgrent, @function
endgrent:
	subl	$16, %esp
	movl	$_ZZZendgrent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endgrent, .-endgrent

	.section	.rodata
_ZZZasctime:
	.string	"asctime"
	.text
	.globl	asctime
	.type	asctime, @function
asctime:
	subl	$16, %esp
	movl	$_ZZZasctime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	asctime, .-asctime

	.section	.rodata
_ZZZinit_module:
	.string	"init_module"
	.text
	.globl	init_module
	.type	init_module, @function
init_module:
	subl	$16, %esp
	movl	$_ZZZinit_module, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	init_module, .-init_module

	.section	.rodata
_ZZZmlock:
	.string	"mlock"
	.text
	.globl	mlock
	.type	mlock, @function
mlock:
	subl	$16, %esp
	movl	$_ZZZmlock, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mlock, .-mlock

	.section	.rodata
_ZZZclnt_sperrno:
	.string	"clnt_sperrno"
	.text
	.globl	clnt_sperrno
	.type	clnt_sperrno, @function
clnt_sperrno:
	subl	$16, %esp
	movl	$_ZZZclnt_sperrno, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clnt_sperrno, .-clnt_sperrno

	.section	.rodata
_ZZZxdrrec_skiprecord:
	.string	"xdrrec_skiprecord"
	.text
	.globl	xdrrec_skiprecord
	.type	xdrrec_skiprecord, @function
xdrrec_skiprecord:
	subl	$16, %esp
	movl	$_ZZZxdrrec_skiprecord, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdrrec_skiprecord, .-xdrrec_skiprecord

	.section	.rodata
_ZZZtoupper:
	.string	"toupper"
	.text
	.globl	toupper
	.type	toupper, @function
toupper:
	subl	$16, %esp
	movl	$_ZZZtoupper, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	toupper, .-toupper

	.section	.rodata
_ZZZmbtowc:
	.string	"mbtowc"
	.text
	.globl	mbtowc
	.type	mbtowc, @function
mbtowc:
	subl	$16, %esp
	movl	$_ZZZmbtowc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mbtowc, .-mbtowc

	.section	.rodata
_ZZZsetprotoent:
	.string	"setprotoent"
	.text
	.globl	setprotoent
	.type	setprotoent, @function
setprotoent:
	subl	$16, %esp
	movl	$_ZZZsetprotoent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setprotoent, .-setprotoent

	.section	.rodata
_ZZZeventfd:
	.string	"eventfd"
	.text
	.globl	eventfd
	.type	eventfd, @function
eventfd:
	subl	$16, %esp
	movl	$_ZZZeventfd, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	eventfd, .-eventfd

	.section	.rodata
_ZZZnetname2user:
	.string	"netname2user"
	.text
	.globl	netname2user
	.type	netname2user, @function
netname2user:
	subl	$16, %esp
	movl	$_ZZZnetname2user, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	netname2user, .-netname2user

	.section	.rodata
_ZZZsvctcp_create:
	.string	"svctcp_create"
	.text
	.globl	svctcp_create
	.type	svctcp_create, @function
svctcp_create:
	subl	$16, %esp
	movl	$_ZZZsvctcp_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svctcp_create, .-svctcp_create

	.section	.rodata
_ZZZsetgroups:
	.string	"setgroups"
	.text
	.globl	setgroups
	.type	setgroups, @function
setgroups:
	subl	$16, %esp
	movl	$_ZZZsetgroups, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setgroups, .-setgroups

	.section	.rodata
_ZZZsetxattr:
	.string	"setxattr"
	.text
	.globl	setxattr
	.type	setxattr, @function
setxattr:
	subl	$16, %esp
	movl	$_ZZZsetxattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setxattr, .-setxattr

	.section	.rodata
_ZZZclnt_perrno:
	.string	"clnt_perrno"
	.text
	.globl	clnt_perrno
	.type	clnt_perrno, @function
clnt_perrno:
	subl	$16, %esp
	movl	$_ZZZclnt_perrno, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clnt_perrno, .-clnt_perrno

	.section	.rodata
_ZZZlrand48:
	.string	"lrand48"
	.text
	.globl	lrand48
	.type	lrand48, @function
lrand48:
	subl	$16, %esp
	movl	$_ZZZlrand48, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lrand48, .-lrand48

	.section	.rodata
_ZZZgrantpt:
	.string	"grantpt"
	.text
	.globl	grantpt
	.type	grantpt, @function
grantpt:
	subl	$16, %esp
	movl	$_ZZZgrantpt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	grantpt, .-grantpt

	.section	.rodata
_ZZZttyname:
	.string	"ttyname"
	.text
	.globl	ttyname
	.type	ttyname, @function
ttyname:
	subl	$16, %esp
	movl	$_ZZZttyname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ttyname, .-ttyname

	.section	.rodata
_ZZZpthread_attr_init:
	.string	"pthread_attr_init"
	.text
	.globl	pthread_attr_init
	.type	pthread_attr_init, @function
pthread_attr_init:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_init, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_init, .-pthread_attr_init

	.section	.rodata
_ZZZherror:
	.string	"herror"
	.text
	.globl	herror
	.type	herror, @function
herror:
	subl	$16, %esp
	movl	$_ZZZherror, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	herror, .-herror

	.section	.rodata
_ZZZgetopt:
	.string	"getopt"
	.text
	.globl	getopt
	.type	getopt, @function
getopt:
	subl	$16, %esp
	movl	$_ZZZgetopt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getopt, .-getopt

	.section	.rodata
_ZZZwcstoul:
	.string	"wcstoul"
	.text
	.globl	wcstoul
	.type	wcstoul, @function
wcstoul:
	subl	$16, %esp
	movl	$_ZZZwcstoul, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcstoul, .-wcstoul

	.section	.rodata
_ZZZgetlogin_r:
	.string	"getlogin_r"
	.text
	.globl	getlogin_r
	.type	getlogin_r, @function
getlogin_r:
	subl	$16, %esp
	movl	$_ZZZgetlogin_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getlogin_r, .-getlogin_r

	.section	.rodata
_ZZZhcreate_r:
	.string	"hcreate_r"
	.text
	.globl	hcreate_r
	.type	hcreate_r, @function
hcreate_r:
	subl	$16, %esp
	movl	$_ZZZhcreate_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	hcreate_r, .-hcreate_r

	.section	.rodata
_ZZZtcflow:
	.string	"tcflow"
	.text
	.globl	tcflow
	.type	tcflow, @function
tcflow:
	subl	$16, %esp
	movl	$_ZZZtcflow, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tcflow, .-tcflow

	.section	.rodata
_ZZZrexec:
	.string	"rexec"
	.text
	.globl	rexec
	.type	rexec, @function
rexec:
	subl	$16, %esp
	movl	$_ZZZrexec, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rexec, .-rexec

	.section	.rodata
_ZZZmsgget:
	.string	"msgget"
	.text
	.globl	msgget
	.type	msgget, @function
msgget:
	subl	$16, %esp
	movl	$_ZZZmsgget, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	msgget, .-msgget

	.section	.rodata
_ZZZfwscanf:
	.string	"fwscanf"
	.text
	.globl	fwscanf
	.type	fwscanf, @function
fwscanf:
	subl	$16, %esp
	movl	$_ZZZfwscanf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fwscanf, .-fwscanf

	.section	.rodata
_ZZZxdr_int16_t:
	.string	"xdr_int16_t"
	.text
	.globl	xdr_int16_t
	.type	xdr_int16_t, @function
xdr_int16_t:
	subl	$16, %esp
	movl	$_ZZZxdr_int16_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_int16_t, .-xdr_int16_t

	.section	.rodata
_ZZZfchmodat:
	.string	"fchmodat"
	.text
	.globl	fchmodat
	.type	fchmodat, @function
fchmodat:
	subl	$16, %esp
	movl	$_ZZZfchmodat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fchmodat, .-fchmodat

	.section	.rodata
_ZZZenvz_strip:
	.string	"envz_strip"
	.text
	.globl	envz_strip
	.type	envz_strip, @function
envz_strip:
	subl	$16, %esp
	movl	$_ZZZenvz_strip, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	envz_strip, .-envz_strip

	.section	.rodata
_ZZZclearerr:
	.string	"clearerr"
	.text
	.globl	clearerr
	.type	clearerr, @function
clearerr:
	subl	$16, %esp
	movl	$_ZZZclearerr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clearerr, .-clearerr

	.section	.rodata
_ZZZdup3:
	.string	"dup3"
	.text
	.globl	dup3
	.type	dup3, @function
dup3:
	subl	$16, %esp
	movl	$_ZZZdup3, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	dup3, .-dup3

	.section	.rodata
_ZZZrcmd_af:
	.string	"rcmd_af"
	.text
	.globl	rcmd_af
	.type	rcmd_af, @function
rcmd_af:
	subl	$16, %esp
	movl	$_ZZZrcmd_af, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rcmd_af, .-rcmd_af

	.section	.rodata
_ZZZrand_r:
	.string	"rand_r"
	.text
	.globl	rand_r
	.type	rand_r, @function
rand_r:
	subl	$16, %esp
	movl	$_ZZZrand_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rand_r, .-rand_r

	.section	.rodata
_ZZZatexit:
	.string	"atexit"
	.text
	.globl	atexit
	.type	atexit, @function
atexit:
	subl	$16, %esp
	movl	$_ZZZatexit, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	atexit, .-atexit

	.section	.rodata
_ZZZxdr_pointer:
	.string	"xdr_pointer"
	.text
	.globl	xdr_pointer
	.type	xdr_pointer, @function
xdr_pointer:
	subl	$16, %esp
	movl	$_ZZZxdr_pointer, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_pointer, .-xdr_pointer

	.section	.rodata
_ZZZwctob:
	.string	"wctob"
	.text
	.globl	wctob
	.type	wctob, @function
wctob:
	subl	$16, %esp
	movl	$_ZZZwctob, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wctob, .-wctob

	.section	.rodata
_ZZZstrptime:
	.string	"strptime"
	.text
	.globl	strptime
	.type	strptime, @function
strptime:
	subl	$16, %esp
	movl	$_ZZZstrptime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strptime, .-strptime

	.section	.rodata
_ZZZclnt_sperror:
	.string	"clnt_sperror"
	.text
	.globl	clnt_sperror
	.type	clnt_sperror, @function
clnt_sperror:
	subl	$16, %esp
	movl	$_ZZZclnt_sperror, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clnt_sperror, .-clnt_sperror

	.section	.rodata
_ZZZfattach:
	.string	"fattach"
	.text
	.globl	fattach
	.type	fattach, @function
fattach:
	subl	$16, %esp
	movl	$_ZZZfattach, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fattach, .-fattach

	.section	.rodata
_ZZZgetpmsg:
	.string	"getpmsg"
	.text
	.globl	getpmsg
	.type	getpmsg, @function
getpmsg:
	subl	$16, %esp
	movl	$_ZZZgetpmsg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpmsg, .-getpmsg

	.section	.rodata
_ZZZptsname:
	.string	"ptsname"
	.text
	.globl	ptsname
	.type	ptsname, @function
ptsname:
	subl	$16, %esp
	movl	$_ZZZptsname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ptsname, .-ptsname

	.section	.rodata
_ZZZfexecve:
	.string	"fexecve"
	.text
	.globl	fexecve
	.type	fexecve, @function
fexecve:
	subl	$16, %esp
	movl	$_ZZZfexecve, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fexecve, .-fexecve

	.section	.rodata
_ZZZclnt_perror:
	.string	"clnt_perror"
	.text
	.globl	clnt_perror
	.type	clnt_perror, @function
clnt_perror:
	subl	$16, %esp
	movl	$_ZZZclnt_perror, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clnt_perror, .-clnt_perror

	.section	.rodata
_ZZZqgcvt:
	.string	"qgcvt"
	.text
	.globl	qgcvt
	.type	qgcvt, @function
qgcvt:
	subl	$16, %esp
	movl	$_ZZZqgcvt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	qgcvt, .-qgcvt

	.section	.rodata
_ZZZsvcerr_noproc:
	.string	"svcerr_noproc"
	.text
	.globl	svcerr_noproc
	.type	svcerr_noproc, @function
svcerr_noproc:
	subl	$16, %esp
	movl	$_ZZZsvcerr_noproc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcerr_noproc, .-svcerr_noproc

	.section	.rodata
_ZZZsigaddset:
	.string	"sigaddset"
	.text
	.globl	sigaddset
	.type	sigaddset, @function
sigaddset:
	subl	$16, %esp
	movl	$_ZZZsigaddset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigaddset, .-sigaddset

	.section	.rodata
_ZZZctime:
	.string	"ctime"
	.text
	.globl	ctime
	.type	ctime, @function
ctime:
	subl	$16, %esp
	movl	$_ZZZctime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ctime, .-ctime

	.section	.rodata
_ZZZsvcerr_noprog:
	.string	"svcerr_noprog"
	.text
	.globl	svcerr_noprog
	.type	svcerr_noprog, @function
svcerr_noprog:
	subl	$16, %esp
	movl	$_ZZZsvcerr_noprog, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcerr_noprog, .-svcerr_noprog

	.section	.rodata
_ZZZfallocate64:
	.string	"fallocate64"
	.text
	.globl	fallocate64
	.type	fallocate64, @function
fallocate64:
	subl	$16, %esp
	movl	$_ZZZfallocate64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fallocate64, .-fallocate64

	.section	.rodata
_ZZZgetgrnam:
	.string	"getgrnam"
	.text
	.globl	getgrnam
	.type	getgrnam, @function
getgrnam:
	subl	$16, %esp
	movl	$_ZZZgetgrnam, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getgrnam, .-getgrnam

	.section	.rodata
_ZZZpthread_mutex_unlock:
	.string	"pthread_mutex_unlock"
	.text
	.globl	pthread_mutex_unlock
	.type	pthread_mutex_unlock, @function
pthread_mutex_unlock:
	subl	$16, %esp
	movl	$_ZZZpthread_mutex_unlock, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_mutex_unlock, .-pthread_mutex_unlock

	.section	.rodata
_ZZZsethostname:
	.string	"sethostname"
	.text
	.globl	sethostname
	.type	sethostname, @function
sethostname:
	subl	$16, %esp
	movl	$_ZZZsethostname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sethostname, .-sethostname

	.section	.rodata
_ZZZmcheck:
	.string	"mcheck"
	.text
	.globl	mcheck
	.type	mcheck, @function
mcheck:
	subl	$16, %esp
	movl	$_ZZZmcheck, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mcheck, .-mcheck

	.section	.rodata
_ZZZxdr_reference:
	.string	"xdr_reference"
	.text
	.globl	xdr_reference
	.type	xdr_reference, @function
xdr_reference:
	subl	$16, %esp
	movl	$_ZZZxdr_reference, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_reference, .-xdr_reference

	.section	.rodata
_ZZZgetpwuid_r:
	.string	"getpwuid_r"
	.text
	.globl	getpwuid_r
	.type	getpwuid_r, @function
getpwuid_r:
	subl	$16, %esp
	movl	$_ZZZgetpwuid_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpwuid_r, .-getpwuid_r

	.section	.rodata
_ZZZendrpcent:
	.string	"endrpcent"
	.text
	.globl	endrpcent
	.type	endrpcent, @function
endrpcent:
	subl	$16, %esp
	movl	$_ZZZendrpcent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endrpcent, .-endrpcent

	.section	.rodata
_ZZZnetname2host:
	.string	"netname2host"
	.text
	.globl	netname2host
	.type	netname2host, @function
netname2host:
	subl	$16, %esp
	movl	$_ZZZnetname2host, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	netname2host, .-netname2host

	.section	.rodata
_ZZZinet_network:
	.string	"inet_network"
	.text
	.globl	inet_network
	.type	inet_network, @function
inet_network:
	subl	$16, %esp
	movl	$_ZZZinet_network, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet_network, .-inet_network

	.section	.rodata
_ZZZputenv:
	.string	"putenv"
	.text
	.globl	putenv
	.type	putenv, @function
putenv:
	subl	$16, %esp
	movl	$_ZZZputenv, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putenv, .-putenv

	.section	.rodata
_ZZZwcswidth:
	.string	"wcswidth"
	.text
	.globl	wcswidth
	.type	wcswidth, @function
wcswidth:
	subl	$16, %esp
	movl	$_ZZZwcswidth, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcswidth, .-wcswidth

	.section	.rodata
_ZZZpmap_set:
	.string	"pmap_set"
	.text
	.globl	pmap_set
	.type	pmap_set, @function
pmap_set:
	subl	$16, %esp
	movl	$_ZZZpmap_set, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pmap_set, .-pmap_set

	.section	.rodata
_ZZZpthread_cond_broadcast:
	.string	"pthread_cond_broadcast"
	.text
	.globl	pthread_cond_broadcast
	.type	pthread_cond_broadcast, @function
pthread_cond_broadcast:
	subl	$16, %esp
	movl	$_ZZZpthread_cond_broadcast, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_cond_broadcast, .-pthread_cond_broadcast

	.section	.rodata
_ZZZftok:
	.string	"ftok"
	.text
	.globl	ftok
	.type	ftok, @function
ftok:
	subl	$16, %esp
	movl	$_ZZZftok, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ftok, .-ftok

	.section	.rodata
_ZZZxdr_netobj:
	.string	"xdr_netobj"
	.text
	.globl	xdr_netobj
	.type	xdr_netobj, @function
xdr_netobj:
	subl	$16, %esp
	movl	$_ZZZxdr_netobj, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_netobj, .-xdr_netobj

	.section	.rodata
_ZZZcatopen:
	.string	"catopen"
	.text
	.globl	catopen
	.type	catopen, @function
catopen:
	subl	$16, %esp
	movl	$_ZZZcatopen, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	catopen, .-catopen

	.section	.rodata
_ZZZpreadv64:
	.string	"preadv64"
	.text
	.globl	preadv64
	.type	preadv64, @function
preadv64:
	subl	$16, %esp
	movl	$_ZZZpreadv64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	preadv64, .-preadv64

	.section	.rodata
_ZZZinet_makeaddr:
	.string	"inet_makeaddr"
	.text
	.globl	inet_makeaddr
	.type	inet_makeaddr, @function
inet_makeaddr:
	subl	$16, %esp
	movl	$_ZZZinet_makeaddr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet_makeaddr, .-inet_makeaddr

	.section	.rodata
_ZZZgetttyent:
	.string	"getttyent"
	.text
	.globl	getttyent
	.type	getttyent, @function
getttyent:
	subl	$16, %esp
	movl	$_ZZZgetttyent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getttyent, .-getttyent

	.section	.rodata
_ZZZgethostbyaddr:
	.string	"gethostbyaddr"
	.text
	.globl	gethostbyaddr
	.type	gethostbyaddr, @function
gethostbyaddr:
	subl	$16, %esp
	movl	$_ZZZgethostbyaddr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gethostbyaddr, .-gethostbyaddr

	.section	.rodata
_ZZZfputc:
	.string	"fputc"
	.text
	.globl	fputc
	.type	fputc, @function
fputc:
	subl	$16, %esp
	movl	$_ZZZfputc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fputc, .-fputc

	.section	.rodata
_ZZZgethostent_r:
	.string	"gethostent_r"
	.text
	.globl	gethostent_r
	.type	gethostent_r, @function
gethostent_r:
	subl	$16, %esp
	movl	$_ZZZgethostent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gethostent_r, .-gethostent_r

	.section	.rodata
_ZZZpsignal:
	.string	"psignal"
	.text
	.globl	psignal
	.type	psignal, @function
psignal:
	subl	$16, %esp
	movl	$_ZZZpsignal, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	psignal, .-psignal

	.section	.rodata
_ZZZverrx:
	.string	"verrx"
	.text
	.globl	verrx
	.type	verrx, @function
verrx:
	subl	$16, %esp
	movl	$_ZZZverrx, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	verrx, .-verrx

	.section	.rodata
_ZZZsetlogin:
	.string	"setlogin"
	.text
	.globl	setlogin
	.type	setlogin, @function
setlogin:
	subl	$16, %esp
	movl	$_ZZZsetlogin, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setlogin, .-setlogin

	.section	.rodata
_ZZZversionsort64:
	.string	"versionsort64"
	.text
	.globl	versionsort64
	.type	versionsort64, @function
versionsort64:
	subl	$16, %esp
	movl	$_ZZZversionsort64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	versionsort64, .-versionsort64

	.section	.rodata
_ZZZfseeko64:
	.string	"fseeko64"
	.text
	.globl	fseeko64
	.type	fseeko64, @function
fseeko64:
	subl	$16, %esp
	movl	$_ZZZfseeko64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fseeko64, .-fseeko64

	.section	.rodata
_ZZZfremovexattr:
	.string	"fremovexattr"
	.text
	.globl	fremovexattr
	.type	fremovexattr, @function
fremovexattr:
	subl	$16, %esp
	movl	$_ZZZfremovexattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fremovexattr, .-fremovexattr

	.section	.rodata
_ZZZcreate_module:
	.string	"create_module"
	.text
	.globl	create_module
	.type	create_module, @function
create_module:
	subl	$16, %esp
	movl	$_ZZZcreate_module, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	create_module, .-create_module

	.section	.rodata
_ZZZgetsid:
	.string	"getsid"
	.text
	.globl	getsid
	.type	getsid, @function
getsid:
	subl	$16, %esp
	movl	$_ZZZgetsid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getsid, .-getsid

	.section	.rodata
_ZZZmktemp:
	.string	"mktemp"
	.text
	.globl	mktemp
	.type	mktemp, @function
mktemp:
	subl	$16, %esp
	movl	$_ZZZmktemp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mktemp, .-mktemp

	.section	.rodata
_ZZZinet_addr:
	.string	"inet_addr"
	.text
	.globl	inet_addr
	.type	inet_addr, @function
inet_addr:
	subl	$16, %esp
	movl	$_ZZZinet_addr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet_addr, .-inet_addr

	.section	.rodata
_ZZZfts_read:
	.string	"fts_read"
	.text
	.globl	fts_read
	.type	fts_read, @function
fts_read:
	subl	$16, %esp
	movl	$_ZZZfts_read, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fts_read, .-fts_read

	.section	.rodata
_ZZZgetfsspec:
	.string	"getfsspec"
	.text
	.globl	getfsspec
	.type	getfsspec, @function
getfsspec:
	subl	$16, %esp
	movl	$_ZZZgetfsspec, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getfsspec, .-getfsspec

	.section	.rodata
_ZZZualarm:
	.string	"ualarm"
	.text
	.globl	ualarm
	.type	ualarm, @function
ualarm:
	subl	$16, %esp
	movl	$_ZZZualarm, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ualarm, .-ualarm

	.section	.rodata
_ZZZquery_module:
	.string	"query_module"
	.text
	.globl	query_module
	.type	query_module, @function
query_module:
	subl	$16, %esp
	movl	$_ZZZquery_module, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	query_module, .-query_module

	.section	.rodata
_ZZZposix_spawn_file_actions_:
	.string	"posix_spawn_file_actions_"
	.text
	.globl	posix_spawn_file_actions_
	.type	posix_spawn_file_actions_, @function
posix_spawn_file_actions_:
	subl	$16, %esp
	movl	$_ZZZposix_spawn_file_actions_, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawn_file_actions_, .-posix_spawn_file_actions_

	.section	.rodata
_ZZZendhostent:
	.string	"endhostent"
	.text
	.globl	endhostent
	.type	endhostent, @function
endhostent:
	subl	$16, %esp
	movl	$_ZZZendhostent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endhostent, .-endhostent

	.section	.rodata
_ZZZpthread_cond_wait:
	.string	"pthread_cond_wait"
	.text
	.globl	pthread_cond_wait
	.type	pthread_cond_wait, @function
pthread_cond_wait:
	subl	$16, %esp
	movl	$_ZZZpthread_cond_wait, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_cond_wait, .-pthread_cond_wait

	.section	.rodata
_ZZZargz_delete:
	.string	"argz_delete"
	.text
	.globl	argz_delete
	.type	argz_delete, @function
argz_delete:
	subl	$16, %esp
	movl	$_ZZZargz_delete, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	argz_delete, .-argz_delete

	.section	.rodata
_ZZZxdr_u_long:
	.string	"xdr_u_long"
	.text
	.globl	xdr_u_long
	.type	xdr_u_long, @function
xdr_u_long:
	subl	$16, %esp
	movl	$_ZZZxdr_u_long, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_u_long, .-xdr_u_long

	.section	.rodata
_ZZZstrnlen:
	.string	"strnlen"
	.text
	.globl	strnlen
	.type	strnlen, @function
strnlen:
	subl	$16, %esp
	movl	$_ZZZstrnlen, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strnlen, .-strnlen

	.section	.rodata
_ZZZnrand48:
	.string	"nrand48"
	.text
	.globl	nrand48
	.type	nrand48, @function
nrand48:
	subl	$16, %esp
	movl	$_ZZZnrand48, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	nrand48, .-nrand48

	.section	.rodata
_ZZZgetspent_r:
	.string	"getspent_r"
	.text
	.globl	getspent_r
	.type	getspent_r, @function
getspent_r:
	subl	$16, %esp
	movl	$_ZZZgetspent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getspent_r, .-getspent_r

	.section	.rodata
_ZZZxdr_string:
	.string	"xdr_string"
	.text
	.globl	xdr_string
	.type	xdr_string, @function
xdr_string:
	subl	$16, %esp
	movl	$_ZZZxdr_string, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_string, .-xdr_string

	.section	.rodata
_ZZZftime:
	.string	"ftime"
	.text
	.globl	ftime
	.type	ftime, @function
ftime:
	subl	$16, %esp
	movl	$_ZZZftime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ftime, .-ftime

	.section	.rodata
_ZZZmemcpy:
	.string	"memcpy"
	.text
	.globl	memcpy
	.type	memcpy, @function
memcpy:
	subl	$16, %esp
	movl	$_ZZZmemcpy, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	memcpy, .-memcpy

	.section	.rodata
_ZZZendusershell:
	.string	"endusershell"
	.text
	.globl	endusershell
	.type	endusershell, @function
endusershell:
	subl	$16, %esp
	movl	$_ZZZendusershell, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endusershell, .-endusershell

	.section	.rodata
_ZZZgetwd:
	.string	"getwd"
	.text
	.globl	getwd
	.type	getwd, @function
getwd:
	subl	$16, %esp
	movl	$_ZZZgetwd, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getwd, .-getwd

	.section	.rodata
_ZZZfreopen64:
	.string	"freopen64"
	.text
	.globl	freopen64
	.type	freopen64, @function
freopen64:
	subl	$16, %esp
	movl	$_ZZZfreopen64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	freopen64, .-freopen64

	.section	.rodata
_ZZZposix_spawnattr_setschedp:
	.string	"posix_spawnattr_setschedp"
	.text
	.globl	posix_spawnattr_setschedp
	.type	posix_spawnattr_setschedp, @function
posix_spawnattr_setschedp:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_setschedp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_setschedp, .-posix_spawnattr_setschedp

	.section	.rodata
_ZZZfclose:
	.string	"fclose"
	.text
	.globl	fclose
	.type	fclose, @function
fclose:
	subl	$16, %esp
	movl	$_ZZZfclose, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fclose, .-fclose

	.section	.rodata
_ZZZsymlinkat:
	.string	"symlinkat"
	.text
	.globl	symlinkat
	.type	symlinkat, @function
symlinkat:
	subl	$16, %esp
	movl	$_ZZZsymlinkat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	symlinkat, .-symlinkat

	.section	.rodata
_ZZZrand:
	.string	"rand"
	.text
	.globl	rand
	.type	rand, @function
rand:
	subl	$16, %esp
	movl	$_ZZZrand, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rand, .-rand

	.section	.rodata
_ZZZpthread_setcanceltype:
	.string	"pthread_setcanceltype"
	.text
	.globl	pthread_setcanceltype
	.type	pthread_setcanceltype, @function
pthread_setcanceltype:
	subl	$16, %esp
	movl	$_ZZZpthread_setcanceltype, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_setcanceltype, .-pthread_setcanceltype

	.section	.rodata
_ZZZtcsetpgrp:
	.string	"tcsetpgrp"
	.text
	.globl	tcsetpgrp
	.type	tcsetpgrp, @function
tcsetpgrp:
	subl	$16, %esp
	movl	$_ZZZtcsetpgrp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tcsetpgrp, .-tcsetpgrp

	.section	.rodata
_ZZZwcscmp:
	.string	"wcscmp"
	.text
	.globl	wcscmp
	.type	wcscmp, @function
wcscmp:
	subl	$16, %esp
	movl	$_ZZZwcscmp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcscmp, .-wcscmp

	.section	.rodata
_ZZZnftw64:
	.string	"nftw64"
	.text
	.globl	nftw64
	.type	nftw64, @function
nftw64:
	subl	$16, %esp
	movl	$_ZZZnftw64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	nftw64, .-nftw64

	.section	.rodata
_ZZZgetmntent:
	.string	"getmntent"
	.text
	.globl	getmntent
	.type	getmntent, @function
getmntent:
	subl	$16, %esp
	movl	$_ZZZgetmntent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getmntent, .-getmntent

	.section	.rodata
_ZZZmkostemp64:
	.string	"mkostemp64"
	.text
	.globl	mkostemp64
	.type	mkostemp64, @function
mkostemp64:
	subl	$16, %esp
	movl	$_ZZZmkostemp64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkostemp64, .-mkostemp64

	.section	.rodata
_ZZZpthread_setschedparam:
	.string	"pthread_setschedparam"
	.text
	.globl	pthread_setschedparam
	.type	pthread_setschedparam, @function
pthread_setschedparam:
	subl	$16, %esp
	movl	$_ZZZpthread_setschedparam, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_setschedparam, .-pthread_setschedparam

	.section	.rodata
_ZZZstrtoul:
	.string	"strtoul"
	.text
	.globl	strtoul
	.type	strtoul, @function
strtoul:
	subl	$16, %esp
	movl	$_ZZZstrtoul, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strtoul, .-strtoul

	.section	.rodata
_ZZZhdestroy_r:
	.string	"hdestroy_r"
	.text
	.globl	hdestroy_r
	.type	hdestroy_r, @function
hdestroy_r:
	subl	$16, %esp
	movl	$_ZZZhdestroy_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	hdestroy_r, .-hdestroy_r

	.section	.rodata
_ZZZfmemopen:
	.string	"fmemopen"
	.text
	.globl	fmemopen
	.type	fmemopen, @function
fmemopen:
	subl	$16, %esp
	movl	$_ZZZfmemopen, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fmemopen, .-fmemopen

	.section	.rodata
_ZZZendspent:
	.string	"endspent"
	.text
	.globl	endspent
	.type	endspent, @function
endspent:
	subl	$16, %esp
	movl	$_ZZZendspent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endspent, .-endspent

	.section	.rodata
_ZZZmunlockall:
	.string	"munlockall"
	.text
	.globl	munlockall
	.type	munlockall, @function
munlockall:
	subl	$16, %esp
	movl	$_ZZZmunlockall, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	munlockall, .-munlockall

	.section	.rodata
_ZZZgetutmp:
	.string	"getutmp"
	.text
	.globl	getutmp
	.type	getutmp, @function
getutmp:
	subl	$16, %esp
	movl	$_ZZZgetutmp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getutmp, .-getutmp

	.section	.rodata
_ZZZgetutmpx:
	.string	"getutmpx"
	.text
	.globl	getutmpx
	.type	getutmpx, @function
getutmpx:
	subl	$16, %esp
	movl	$_ZZZgetutmpx, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getutmpx, .-getutmpx

	.section	.rodata
_ZZZvprintf:
	.string	"vprintf"
	.text
	.globl	vprintf
	.type	vprintf, @function
vprintf:
	subl	$16, %esp
	movl	$_ZZZvprintf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vprintf, .-vprintf

	.section	.rodata
_ZZZxdr_u_int:
	.string	"xdr_u_int"
	.text
	.globl	xdr_u_int
	.type	xdr_u_int, @function
xdr_u_int:
	subl	$16, %esp
	movl	$_ZZZxdr_u_int, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_u_int, .-xdr_u_int

	.section	.rodata
_ZZZsetsockopt:
	.string	"setsockopt"
	.text
	.globl	setsockopt
	.type	setsockopt, @function
setsockopt:
	subl	$16, %esp
	movl	$_ZZZsetsockopt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setsockopt, .-setsockopt

	.section	.rodata
_ZZZmalloc:
	.string	"malloc"
	.text
	.globl	malloc
	.type	malloc, @function
malloc:
	subl	$16, %esp
	movl	$_ZZZmalloc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	malloc, .-malloc

	.section	.rodata
_ZZZeventfd_read:
	.string	"eventfd_read"
	.text
	.globl	eventfd_read
	.type	eventfd_read, @function
eventfd_read:
	subl	$16, %esp
	movl	$_ZZZeventfd_read, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	eventfd_read, .-eventfd_read

	.section	.rodata
_ZZZgetpass:
	.string	"getpass"
	.text
	.globl	getpass
	.type	getpass, @function
getpass:
	subl	$16, %esp
	movl	$_ZZZgetpass, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpass, .-getpass

	.section	.rodata
_ZZZxdr_keystatus:
	.string	"xdr_keystatus"
	.text
	.globl	xdr_keystatus
	.type	xdr_keystatus, @function
xdr_keystatus:
	subl	$16, %esp
	movl	$_ZZZxdr_keystatus, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_keystatus, .-xdr_keystatus

	.section	.rodata
_ZZZuselib:
	.string	"uselib"
	.text
	.globl	uselib
	.type	uselib, @function
uselib:
	subl	$16, %esp
	movl	$_ZZZuselib, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	uselib, .-uselib

	.section	.rodata
_ZZZsigisemptyset:
	.string	"sigisemptyset"
	.text
	.globl	sigisemptyset
	.type	sigisemptyset, @function
sigisemptyset:
	subl	$16, %esp
	movl	$_ZZZsigisemptyset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigisemptyset, .-sigisemptyset

	.section	.rodata
_ZZZstrfmon:
	.string	"strfmon"
	.text
	.globl	strfmon
	.type	strfmon, @function
strfmon:
	subl	$16, %esp
	movl	$_ZZZstrfmon, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strfmon, .-strfmon

	.section	.rodata
_ZZZkillpg:
	.string	"killpg"
	.text
	.globl	killpg
	.type	killpg, @function
killpg:
	subl	$16, %esp
	movl	$_ZZZkillpg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	killpg, .-killpg

	.section	.rodata
_ZZZstrcat:
	.string	"strcat"
	.text
	.globl	strcat
	.type	strcat, @function
strcat:
	subl	$16, %esp
	movl	$_ZZZstrcat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strcat, .-strcat

	.section	.rodata
_ZZZxdr_int:
	.string	"xdr_int"
	.text
	.globl	xdr_int
	.type	xdr_int, @function
xdr_int:
	subl	$16, %esp
	movl	$_ZZZxdr_int, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_int, .-xdr_int

	.section	.rodata
_ZZZftello64:
	.string	"ftello64"
	.text
	.globl	ftello64
	.type	ftello64, @function
ftello64:
	subl	$16, %esp
	movl	$_ZZZftello64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ftello64, .-ftello64

	.section	.rodata
_ZZZrealpath:
	.string	"realpath"
	.text
	.globl	realpath
	.type	realpath, @function
realpath:
	subl	$16, %esp
	movl	$_ZZZrealpath, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	realpath, .-realpath

	.section	.rodata
_ZZZpthread_attr_getschedpoli:
	.string	"pthread_attr_getschedpoli"
	.text
	.globl	pthread_attr_getschedpoli
	.type	pthread_attr_getschedpoli, @function
pthread_attr_getschedpoli:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_getschedpoli, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_getschedpoli, .-pthread_attr_getschedpoli

	.section	.rodata
_ZZZftello:
	.string	"ftello"
	.text
	.globl	ftello
	.type	ftello, @function
ftello:
	subl	$16, %esp
	movl	$_ZZZftello, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ftello, .-ftello

	.section	.rodata
_ZZZtimegm:
	.string	"timegm"
	.text
	.globl	timegm
	.type	timegm, @function
timegm:
	subl	$16, %esp
	movl	$_ZZZtimegm, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	timegm, .-timegm

	.section	.rodata
_ZZZraise:
	.string	"raise"
	.text
	.globl	raise
	.type	raise, @function
raise:
	subl	$16, %esp
	movl	$_ZZZraise, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	raise, .-raise

	.section	.rodata
_ZZZsetegid:
	.string	"setegid"
	.text
	.globl	setegid
	.type	setegid, @function
setegid:
	subl	$16, %esp
	movl	$_ZZZsetegid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setegid, .-setegid

	.section	.rodata
_ZZZsetfsgid:
	.string	"setfsgid"
	.text
	.globl	setfsgid
	.type	setfsgid, @function
setfsgid:
	subl	$16, %esp
	movl	$_ZZZsetfsgid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setfsgid, .-setfsgid

	.section	.rodata
_ZZZremove:
	.string	"remove"
	.text
	.globl	remove
	.type	remove, @function
remove:
	subl	$16, %esp
	movl	$_ZZZremove, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	remove, .-remove

	.section	.rodata
_ZZZpmap_getmaps:
	.string	"pmap_getmaps"
	.text
	.globl	pmap_getmaps
	.type	pmap_getmaps, @function
pmap_getmaps:
	subl	$16, %esp
	movl	$_ZZZpmap_getmaps, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pmap_getmaps, .-pmap_getmaps

	.section	.rodata
_ZZZsvcudp_bufcreate:
	.string	"svcudp_bufcreate"
	.text
	.globl	svcudp_bufcreate
	.type	svcudp_bufcreate, @function
svcudp_bufcreate:
	subl	$16, %esp
	movl	$_ZZZsvcudp_bufcreate, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcudp_bufcreate, .-svcudp_bufcreate

	.section	.rodata
_ZZZxdrrec_eof:
	.string	"xdrrec_eof"
	.text
	.globl	xdrrec_eof
	.type	xdrrec_eof, @function
xdrrec_eof:
	subl	$16, %esp
	movl	$_ZZZxdrrec_eof, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdrrec_eof, .-xdrrec_eof

	.section	.rodata
_ZZZisupper:
	.string	"isupper"
	.text
	.globl	isupper
	.type	isupper, @function
isupper:
	subl	$16, %esp
	movl	$_ZZZisupper, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isupper, .-isupper

	.section	.rodata
_ZZZvsyslog:
	.string	"vsyslog"
	.text
	.globl	vsyslog
	.type	vsyslog, @function
vsyslog:
	subl	$16, %esp
	movl	$_ZZZvsyslog, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vsyslog, .-vsyslog

	.section	.rodata
_ZZZprlimit64:
	.string	"prlimit64"
	.text
	.globl	prlimit64
	.type	prlimit64, @function
prlimit64:
	subl	$16, %esp
	movl	$_ZZZprlimit64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	prlimit64, .-prlimit64

	.section	.rodata
_ZZZsvc_getreq_poll:
	.string	"svc_getreq_poll"
	.text
	.globl	svc_getreq_poll
	.type	svc_getreq_poll, @function
svc_getreq_poll:
	subl	$16, %esp
	movl	$_ZZZsvc_getreq_poll, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svc_getreq_poll, .-svc_getreq_poll

	.section	.rodata
_ZZZpthread_attr_setinheritsc:
	.string	"pthread_attr_setinheritsc"
	.text
	.globl	pthread_attr_setinheritsc
	.type	pthread_attr_setinheritsc, @function
pthread_attr_setinheritsc:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_setinheritsc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_setinheritsc, .-pthread_attr_setinheritsc

	.section	.rodata
_ZZZnl_langinfo:
	.string	"nl_langinfo"
	.text
	.globl	nl_langinfo
	.type	nl_langinfo, @function
nl_langinfo:
	subl	$16, %esp
	movl	$_ZZZnl_langinfo, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	nl_langinfo, .-nl_langinfo

	.section	.rodata
_ZZZsetfsent:
	.string	"setfsent"
	.text
	.globl	setfsent
	.type	setfsent, @function
setfsent:
	subl	$16, %esp
	movl	$_ZZZsetfsent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setfsent, .-setfsent

	.section	.rodata
_ZZZgetnetbyaddr_r:
	.string	"getnetbyaddr_r"
	.text
	.globl	getnetbyaddr_r
	.type	getnetbyaddr_r, @function
getnetbyaddr_r:
	subl	$16, %esp
	movl	$_ZZZgetnetbyaddr_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getnetbyaddr_r, .-getnetbyaddr_r

	.section	.rodata
_ZZZwcsncat:
	.string	"wcsncat"
	.text
	.globl	wcsncat
	.type	wcsncat, @function
wcsncat:
	subl	$16, %esp
	movl	$_ZZZwcsncat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcsncat, .-wcsncat

	.section	.rodata
_ZZZgethostent:
	.string	"gethostent"
	.text
	.globl	gethostent
	.type	gethostent, @function
gethostent:
	subl	$16, %esp
	movl	$_ZZZgethostent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gethostent, .-gethostent

	.section	.rodata
_ZZZclnt_broadcast:
	.string	"clnt_broadcast"
	.text
	.globl	clnt_broadcast
	.type	clnt_broadcast, @function
clnt_broadcast:
	subl	$16, %esp
	movl	$_ZZZclnt_broadcast, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clnt_broadcast, .-clnt_broadcast

	.section	.rodata
_ZZZmcheck_check_all:
	.string	"mcheck_check_all"
	.text
	.globl	mcheck_check_all
	.type	mcheck_check_all, @function
mcheck_check_all:
	subl	$16, %esp
	movl	$_ZZZmcheck_check_all, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mcheck_check_all, .-mcheck_check_all

	.section	.rodata
_ZZZpthread_condattr_destroy:
	.string	"pthread_condattr_destroy"
	.text
	.globl	pthread_condattr_destroy
	.type	pthread_condattr_destroy, @function
pthread_condattr_destroy:
	subl	$16, %esp
	movl	$_ZZZpthread_condattr_destroy, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_condattr_destroy, .-pthread_condattr_destroy

	.section	.rodata
_ZZZgetspnam:
	.string	"getspnam"
	.text
	.globl	getspnam
	.type	getspnam, @function
getspnam:
	subl	$16, %esp
	movl	$_ZZZgetspnam, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getspnam, .-getspnam

	.section	.rodata
_ZZZinet6_option_space:
	.string	"inet6_option_space"
	.text
	.globl	inet6_option_space
	.type	inet6_option_space, @function
inet6_option_space:
	subl	$16, %esp
	movl	$_ZZZinet6_option_space, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_option_space, .-inet6_option_space

	.section	.rodata
_ZZZsched_getaffinity:
	.string	"sched_getaffinity"
	.text
	.globl	sched_getaffinity
	.type	sched_getaffinity, @function
sched_getaffinity:
	subl	$16, %esp
	movl	$_ZZZsched_getaffinity, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sched_getaffinity, .-sched_getaffinity

	.section	.rodata
_ZZZgetenv:
	.string	"getenv"
	.text
	.globl	getenv
	.type	getenv, @function
getenv:
	subl	$16, %esp
	movl	$_ZZZgetenv, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getenv, .-getenv

	.section	.rodata
_ZZZsched_getaffinity:
	.string	"sched_getaffinity"
	.text
	.globl	sched_getaffinity
	.type	sched_getaffinity, @function
sched_getaffinity:
	subl	$16, %esp
	movl	$_ZZZsched_getaffinity, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sched_getaffinity, .-sched_getaffinity

	.section	.rodata
_ZZZsscanf:
	.string	"sscanf"
	.text
	.globl	sscanf
	.type	sscanf, @function
sscanf:
	subl	$16, %esp
	movl	$_ZZZsscanf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sscanf, .-sscanf

	.section	.rodata
_ZZZpreadv:
	.string	"preadv"
	.text
	.globl	preadv
	.type	preadv, @function
preadv:
	subl	$16, %esp
	movl	$_ZZZpreadv, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	preadv, .-preadv

	.section	.rodata
_ZZZruserok:
	.string	"ruserok"
	.text
	.globl	ruserok
	.type	ruserok, @function
ruserok:
	subl	$16, %esp
	movl	$_ZZZruserok, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ruserok, .-ruserok

	.section	.rodata
_ZZZfts_set:
	.string	"fts_set"
	.text
	.globl	fts_set
	.type	fts_set, @function
fts_set:
	subl	$16, %esp
	movl	$_ZZZfts_set, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fts_set, .-fts_set

	.section	.rodata
_ZZZxdr_u_longlong_t:
	.string	"xdr_u_longlong_t"
	.text
	.globl	xdr_u_longlong_t
	.type	xdr_u_longlong_t, @function
xdr_u_longlong_t:
	subl	$16, %esp
	movl	$_ZZZxdr_u_longlong_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_u_longlong_t, .-xdr_u_longlong_t

	.section	.rodata
_ZZZnice:
	.string	"nice"
	.text
	.globl	nice
	.type	nice, @function
nice:
	subl	$16, %esp
	movl	$_ZZZnice, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	nice, .-nice

	.section	.rodata
_ZZZxdecrypt:
	.string	"xdecrypt"
	.text
	.globl	xdecrypt
	.type	xdecrypt, @function
xdecrypt:
	subl	$16, %esp
	movl	$_ZZZxdecrypt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdecrypt, .-xdecrypt

	.section	.rodata
_ZZZisgraph:
	.string	"isgraph"
	.text
	.globl	isgraph
	.type	isgraph, @function
isgraph:
	subl	$16, %esp
	movl	$_ZZZisgraph, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isgraph, .-isgraph

	.section	.rodata
_ZZZcatclose:
	.string	"catclose"
	.text
	.globl	catclose
	.type	catclose, @function
catclose:
	subl	$16, %esp
	movl	$_ZZZcatclose, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	catclose, .-catclose

	.section	.rodata
_ZZZclntudp_bufcreate:
	.string	"clntudp_bufcreate"
	.text
	.globl	clntudp_bufcreate
	.type	clntudp_bufcreate, @function
clntudp_bufcreate:
	subl	$16, %esp
	movl	$_ZZZclntudp_bufcreate, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clntudp_bufcreate, .-clntudp_bufcreate

	.section	.rodata
_ZZZgetservbyname:
	.string	"getservbyname"
	.text
	.globl	getservbyname
	.type	getservbyname, @function
getservbyname:
	subl	$16, %esp
	movl	$_ZZZgetservbyname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getservbyname, .-getservbyname

	.section	.rodata
_ZZZmsgctl:
	.string	"msgctl"
	.text
	.globl	msgctl
	.type	msgctl, @function
msgctl:
	subl	$16, %esp
	movl	$_ZZZmsgctl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	msgctl, .-msgctl

	.section	.rodata
_ZZZwcwidth:
	.string	"wcwidth"
	.text
	.globl	wcwidth
	.type	wcwidth, @function
wcwidth:
	subl	$16, %esp
	movl	$_ZZZwcwidth, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcwidth, .-wcwidth

	.section	.rodata
_ZZZmsgctl:
	.string	"msgctl"
	.text
	.globl	msgctl
	.type	msgctl, @function
msgctl:
	subl	$16, %esp
	movl	$_ZZZmsgctl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	msgctl, .-msgctl

	.section	.rodata
_ZZZinet_lnaof:
	.string	"inet_lnaof"
	.text
	.globl	inet_lnaof
	.type	inet_lnaof, @function
inet_lnaof:
	subl	$16, %esp
	movl	$_ZZZinet_lnaof, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet_lnaof, .-inet_lnaof

	.section	.rodata
_ZZZsigdelset:
	.string	"sigdelset"
	.text
	.globl	sigdelset
	.type	sigdelset, @function
sigdelset:
	subl	$16, %esp
	movl	$_ZZZsigdelset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigdelset, .-sigdelset

	.section	.rodata
_ZZZfchownat:
	.string	"fchownat"
	.text
	.globl	fchownat
	.type	fchownat, @function
fchownat:
	subl	$16, %esp
	movl	$_ZZZfchownat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fchownat, .-fchownat

	.section	.rodata
_ZZZalarm:
	.string	"alarm"
	.text
	.globl	alarm
	.type	alarm, @function
alarm:
	subl	$16, %esp
	movl	$_ZZZalarm, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	alarm, .-alarm

	.section	.rodata
_ZZZxdr_getcredres:
	.string	"xdr_getcredres"
	.text
	.globl	xdr_getcredres
	.type	xdr_getcredres, @function
xdr_getcredres:
	subl	$16, %esp
	movl	$_ZZZxdr_getcredres, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_getcredres, .-xdr_getcredres

	.section	.rodata
_ZZZerr:
	.string	"err"
	.text
	.globl	err
	.type	err, @function
err:
	subl	$16, %esp
	movl	$_ZZZerr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	err, .-err

	.section	.rodata
_ZZZchflags:
	.string	"chflags"
	.text
	.globl	chflags
	.type	chflags, @function
chflags:
	subl	$16, %esp
	movl	$_ZZZchflags, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	chflags, .-chflags

	.section	.rodata
_ZZZinotify_init:
	.string	"inotify_init"
	.text
	.globl	inotify_init
	.type	inotify_init, @function
inotify_init:
	subl	$16, %esp
	movl	$_ZZZinotify_init, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inotify_init, .-inotify_init

	.section	.rodata
_ZZZgetservbyname_r:
	.string	"getservbyname_r"
	.text
	.globl	getservbyname_r
	.type	getservbyname_r, @function
getservbyname_r:
	subl	$16, %esp
	movl	$_ZZZgetservbyname_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getservbyname_r, .-getservbyname_r

	.section	.rodata
_ZZZtimerfd_settime:
	.string	"timerfd_settime"
	.text
	.globl	timerfd_settime
	.type	timerfd_settime, @function
timerfd_settime:
	subl	$16, %esp
	movl	$_ZZZtimerfd_settime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	timerfd_settime, .-timerfd_settime

	.section	.rodata
_ZZZffsll:
	.string	"ffsll"
	.text
	.globl	ffsll
	.type	ffsll, @function
ffsll:
	subl	$16, %esp
	movl	$_ZZZffsll, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ffsll, .-ffsll

	.section	.rodata
_ZZZxdr_bool:
	.string	"xdr_bool"
	.text
	.globl	xdr_bool
	.type	xdr_bool, @function
xdr_bool:
	subl	$16, %esp
	movl	$_ZZZxdr_bool, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_bool, .-xdr_bool

	.section	.rodata
_ZZZsetrlimit64:
	.string	"setrlimit64"
	.text
	.globl	setrlimit64
	.type	setrlimit64, @function
setrlimit64:
	subl	$16, %esp
	movl	$_ZZZsetrlimit64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setrlimit64, .-setrlimit64

	.section	.rodata
_ZZZsched_getcpu:
	.string	"sched_getcpu"
	.text
	.globl	sched_getcpu
	.type	sched_getcpu, @function
sched_getcpu:
	subl	$16, %esp
	movl	$_ZZZsched_getcpu, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sched_getcpu, .-sched_getcpu

	.section	.rodata
_ZZZposix_spawnattr_setsigdef:
	.string	"posix_spawnattr_setsigdef"
	.text
	.globl	posix_spawnattr_setsigdef
	.type	posix_spawnattr_setsigdef, @function
posix_spawnattr_setsigdef:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_setsigdef, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_setsigdef, .-posix_spawnattr_setsigdef

	.section	.rodata
_ZZZendsgent:
	.string	"endsgent"
	.text
	.globl	endsgent
	.type	endsgent, @function
endsgent:
	subl	$16, %esp
	movl	$_ZZZendsgent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endsgent, .-endsgent

	.section	.rodata
_ZZZntp_gettimex:
	.string	"ntp_gettimex"
	.text
	.globl	ntp_gettimex
	.type	ntp_gettimex, @function
ntp_gettimex:
	subl	$16, %esp
	movl	$_ZZZntp_gettimex, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ntp_gettimex, .-ntp_gettimex

	.section	.rodata
_ZZZinet6_opt_init:
	.string	"inet6_opt_init"
	.text
	.globl	inet6_opt_init
	.type	inet6_opt_init, @function
inet6_opt_init:
	subl	$16, %esp
	movl	$_ZZZinet6_opt_init, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_opt_init, .-inet6_opt_init

	.section	.rodata
_ZZZgethostbyname:
	.string	"gethostbyname"
	.text
	.globl	gethostbyname
	.type	gethostbyname, @function
gethostbyname:
	subl	$16, %esp
	movl	$_ZZZgethostbyname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gethostbyname, .-gethostbyname

	.section	.rodata
_ZZZposix_spawn_file_actions_:
	.string	"posix_spawn_file_actions_"
	.text
	.globl	posix_spawn_file_actions_
	.type	posix_spawn_file_actions_, @function
posix_spawn_file_actions_:
	subl	$16, %esp
	movl	$_ZZZposix_spawn_file_actions_, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawn_file_actions_, .-posix_spawn_file_actions_

	.section	.rodata
_ZZZseteuid:
	.string	"seteuid"
	.text
	.globl	seteuid
	.type	seteuid, @function
seteuid:
	subl	$16, %esp
	movl	$_ZZZseteuid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	seteuid, .-seteuid

	.section	.rodata
_ZZZmkdirat:
	.string	"mkdirat"
	.text
	.globl	mkdirat
	.type	mkdirat, @function
mkdirat:
	subl	$16, %esp
	movl	$_ZZZmkdirat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkdirat, .-mkdirat

	.section	.rodata
_ZZZwcscpy:
	.string	"wcscpy"
	.text
	.globl	wcscpy
	.type	wcscpy, @function
wcscpy:
	subl	$16, %esp
	movl	$_ZZZwcscpy, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcscpy, .-wcscpy

	.section	.rodata
_ZZZsetfsuid:
	.string	"setfsuid"
	.text
	.globl	setfsuid
	.type	setfsuid, @function
setfsuid:
	subl	$16, %esp
	movl	$_ZZZsetfsuid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setfsuid, .-setfsuid

	.section	.rodata
_ZZZmrand48_r:
	.string	"mrand48_r"
	.text
	.globl	mrand48_r
	.type	mrand48_r, @function
mrand48_r:
	subl	$16, %esp
	movl	$_ZZZmrand48_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mrand48_r, .-mrand48_r

	.section	.rodata
_ZZZpthread_exit:
	.string	"pthread_exit"
	.text
	.globl	pthread_exit
	.type	pthread_exit, @function
pthread_exit:
	subl	$16, %esp
	movl	$_ZZZpthread_exit, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_exit, .-pthread_exit

	.section	.rodata
_ZZZxdr_u_char:
	.string	"xdr_u_char"
	.text
	.globl	xdr_u_char
	.type	xdr_u_char, @function
xdr_u_char:
	subl	$16, %esp
	movl	$_ZZZxdr_u_char, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_u_char, .-xdr_u_char

	.section	.rodata
_ZZZgetwchar_unlocked:
	.string	"getwchar_unlocked"
	.text
	.globl	getwchar_unlocked
	.type	getwchar_unlocked, @function
getwchar_unlocked:
	subl	$16, %esp
	movl	$_ZZZgetwchar_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getwchar_unlocked, .-getwchar_unlocked

	.section	.rodata
_ZZZpututxline:
	.string	"pututxline"
	.text
	.globl	pututxline
	.type	pututxline, @function
pututxline:
	subl	$16, %esp
	movl	$_ZZZpututxline, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pututxline, .-pututxline

	.section	.rodata
_ZZZfchflags:
	.string	"fchflags"
	.text
	.globl	fchflags
	.type	fchflags, @function
fchflags:
	subl	$16, %esp
	movl	$_ZZZfchflags, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fchflags, .-fchflags

	.section	.rodata
_ZZZgetlogin:
	.string	"getlogin"
	.text
	.globl	getlogin
	.type	getlogin, @function
getlogin:
	subl	$16, %esp
	movl	$_ZZZgetlogin, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getlogin, .-getlogin

	.section	.rodata
_ZZZsigandset:
	.string	"sigandset"
	.text
	.globl	sigandset
	.type	sigandset, @function
sigandset:
	subl	$16, %esp
	movl	$_ZZZsigandset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigandset, .-sigandset

	.section	.rodata
_ZZZxdr_double:
	.string	"xdr_double"
	.text
	.globl	xdr_double
	.type	xdr_double, @function
xdr_double:
	subl	$16, %esp
	movl	$_ZZZxdr_double, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_double, .-xdr_double

	.section	.rodata
_ZZZrcmd:
	.string	"rcmd"
	.text
	.globl	rcmd
	.type	rcmd, @function
rcmd:
	subl	$16, %esp
	movl	$_ZZZrcmd, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rcmd, .-rcmd

	.section	.rodata
_ZZZiruserok_af:
	.string	"iruserok_af"
	.text
	.globl	iruserok_af
	.type	iruserok_af, @function
iruserok_af:
	subl	$16, %esp
	movl	$_ZZZiruserok_af, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	iruserok_af, .-iruserok_af

	.section	.rodata
_ZZZlsearch:
	.string	"lsearch"
	.text
	.globl	lsearch
	.type	lsearch, @function
lsearch:
	subl	$16, %esp
	movl	$_ZZZlsearch, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lsearch, .-lsearch

	.section	.rodata
_ZZZfscanf:
	.string	"fscanf"
	.text
	.globl	fscanf
	.type	fscanf, @function
fscanf:
	subl	$16, %esp
	movl	$_ZZZfscanf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fscanf, .-fscanf

	.section	.rodata
_ZZZmkostemps64:
	.string	"mkostemps64"
	.text
	.globl	mkostemps64
	.type	mkostemps64, @function
mkostemps64:
	subl	$16, %esp
	movl	$_ZZZmkostemps64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkostemps64, .-mkostemps64

	.section	.rodata
_ZZZether_aton_r:
	.string	"ether_aton_r"
	.text
	.globl	ether_aton_r
	.type	ether_aton_r, @function
ether_aton_r:
	subl	$16, %esp
	movl	$_ZZZether_aton_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ether_aton_r, .-ether_aton_r

	.section	.rodata
_ZZZhost2netname:
	.string	"host2netname"
	.text
	.globl	host2netname
	.type	host2netname, @function
host2netname:
	subl	$16, %esp
	movl	$_ZZZhost2netname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	host2netname, .-host2netname

	.section	.rodata
_ZZZremovexattr:
	.string	"removexattr"
	.text
	.globl	removexattr
	.type	removexattr, @function
removexattr:
	subl	$16, %esp
	movl	$_ZZZremovexattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	removexattr, .-removexattr

	.section	.rodata
_ZZZxdr_pmap:
	.string	"xdr_pmap"
	.text
	.globl	xdr_pmap
	.type	xdr_pmap, @function
xdr_pmap:
	subl	$16, %esp
	movl	$_ZZZxdr_pmap, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_pmap, .-xdr_pmap

	.section	.rodata
_ZZZgetprotoent:
	.string	"getprotoent"
	.text
	.globl	getprotoent
	.type	getprotoent, @function
getprotoent:
	subl	$16, %esp
	movl	$_ZZZgetprotoent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getprotoent, .-getprotoent

	.section	.rodata
_ZZZxdr_opaque:
	.string	"xdr_opaque"
	.text
	.globl	xdr_opaque
	.type	xdr_opaque, @function
xdr_opaque:
	subl	$16, %esp
	movl	$_ZZZxdr_opaque, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_opaque, .-xdr_opaque

	.section	.rodata
_ZZZsetrlimit:
	.string	"setrlimit"
	.text
	.globl	setrlimit
	.type	setrlimit, @function
setrlimit:
	subl	$16, %esp
	movl	$_ZZZsetrlimit, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setrlimit, .-setrlimit

	.section	.rodata
_ZZZgetopt_long:
	.string	"getopt_long"
	.text
	.globl	getopt_long
	.type	getopt_long, @function
getopt_long:
	subl	$16, %esp
	movl	$_ZZZgetopt_long, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getopt_long, .-getopt_long

	.section	.rodata
_ZZZopen_memstream:
	.string	"open_memstream"
	.text
	.globl	open_memstream
	.type	open_memstream, @function
open_memstream:
	subl	$16, %esp
	movl	$_ZZZopen_memstream, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	open_memstream, .-open_memstream

	.section	.rodata
_ZZZsstk:
	.string	"sstk"
	.text
	.globl	sstk
	.type	sstk, @function
sstk:
	subl	$16, %esp
	movl	$_ZZZsstk, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sstk, .-sstk

	.section	.rodata
_ZZZutmpxname:
	.string	"utmpxname"
	.text
	.globl	utmpxname
	.type	utmpxname, @function
utmpxname:
	subl	$16, %esp
	movl	$_ZZZutmpxname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	utmpxname, .-utmpxname

	.section	.rodata
_ZZZvwarnx:
	.string	"vwarnx"
	.text
	.globl	vwarnx
	.type	vwarnx, @function
vwarnx:
	subl	$16, %esp
	movl	$_ZZZvwarnx, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vwarnx, .-vwarnx

	.section	.rodata
_ZZZposix_madvise:
	.string	"posix_madvise"
	.text
	.globl	posix_madvise
	.type	posix_madvise, @function
posix_madvise:
	subl	$16, %esp
	movl	$_ZZZposix_madvise, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_madvise, .-posix_madvise

	.section	.rodata
_ZZZposix_spawnattr_getpgroup:
	.string	"posix_spawnattr_getpgroup"
	.text
	.globl	posix_spawnattr_getpgroup
	.type	posix_spawnattr_getpgroup, @function
posix_spawnattr_getpgroup:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_getpgroup, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_getpgroup, .-posix_spawnattr_getpgroup

	.section	.rodata
_ZZZfgetpos64:
	.string	"fgetpos64"
	.text
	.globl	fgetpos64
	.type	fgetpos64, @function
fgetpos64:
	subl	$16, %esp
	movl	$_ZZZfgetpos64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fgetpos64, .-fgetpos64

	.section	.rodata
_ZZZexecvp:
	.string	"execvp"
	.text
	.globl	execvp
	.type	execvp, @function
execvp:
	subl	$16, %esp
	movl	$_ZZZexecvp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	execvp, .-execvp

	.section	.rodata
_ZZZpthread_attr_getdetachsta:
	.string	"pthread_attr_getdetachsta"
	.text
	.globl	pthread_attr_getdetachsta
	.type	pthread_attr_getdetachsta, @function
pthread_attr_getdetachsta:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_getdetachsta, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_getdetachsta, .-pthread_attr_getdetachsta

	.section	.rodata
_ZZZmincore:
	.string	"mincore"
	.text
	.globl	mincore
	.type	mincore, @function
mincore:
	subl	$16, %esp
	movl	$_ZZZmincore, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mincore, .-mincore

	.section	.rodata
_ZZZfreeifaddrs:
	.string	"freeifaddrs"
	.text
	.globl	freeifaddrs
	.type	freeifaddrs, @function
freeifaddrs:
	subl	$16, %esp
	movl	$_ZZZfreeifaddrs, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	freeifaddrs, .-freeifaddrs

	.section	.rodata
_ZZZsvcudp_enablecache:
	.string	"svcudp_enablecache"
	.text
	.globl	svcudp_enablecache
	.type	svcudp_enablecache, @function
svcudp_enablecache:
	subl	$16, %esp
	movl	$_ZZZsvcudp_enablecache, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcudp_enablecache, .-svcudp_enablecache

	.section	.rodata
_ZZZlinkat:
	.string	"linkat"
	.text
	.globl	linkat
	.type	linkat, @function
linkat:
	subl	$16, %esp
	movl	$_ZZZlinkat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	linkat, .-linkat

	.section	.rodata
_ZZZinet6_rth_space:
	.string	"inet6_rth_space"
	.text
	.globl	inet6_rth_space
	.type	inet6_rth_space, @function
inet6_rth_space:
	subl	$16, %esp
	movl	$_ZZZinet6_rth_space, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_rth_space, .-inet6_rth_space

	.section	.rodata
_ZZZpthread_cond_timedwait:
	.string	"pthread_cond_timedwait"
	.text
	.globl	pthread_cond_timedwait
	.type	pthread_cond_timedwait, @function
pthread_cond_timedwait:
	subl	$16, %esp
	movl	$_ZZZpthread_cond_timedwait, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_cond_timedwait, .-pthread_cond_timedwait

	.section	.rodata
_ZZZgetpwnam_r:
	.string	"getpwnam_r"
	.text
	.globl	getpwnam_r
	.type	getpwnam_r, @function
getpwnam_r:
	subl	$16, %esp
	movl	$_ZZZgetpwnam_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpwnam_r, .-getpwnam_r

	.section	.rodata
_ZZZfreopen:
	.string	"freopen"
	.text
	.globl	freopen
	.type	freopen, @function
freopen:
	subl	$16, %esp
	movl	$_ZZZfreopen, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	freopen, .-freopen

	.section	.rodata
_ZZZgetsgnam:
	.string	"getsgnam"
	.text
	.globl	getsgnam
	.type	getsgnam, @function
getsgnam:
	subl	$16, %esp
	movl	$_ZZZgetsgnam, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getsgnam, .-getsgnam

	.section	.rodata
_ZZZremque:
	.string	"remque"
	.text
	.globl	remque
	.type	remque, @function
remque:
	subl	$16, %esp
	movl	$_ZZZremque, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	remque, .-remque

	.section	.rodata
_ZZZinet6_rth_reverse:
	.string	"inet6_rth_reverse"
	.text
	.globl	inet6_rth_reverse
	.type	inet6_rth_reverse, @function
inet6_rth_reverse:
	subl	$16, %esp
	movl	$_ZZZinet6_rth_reverse, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_rth_reverse, .-inet6_rth_reverse

	.section	.rodata
_ZZZptrace:
	.string	"ptrace"
	.text
	.globl	ptrace
	.type	ptrace, @function
ptrace:
	subl	$16, %esp
	movl	$_ZZZptrace, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ptrace, .-ptrace

	.section	.rodata
_ZZZgetifaddrs:
	.string	"getifaddrs"
	.text
	.globl	getifaddrs
	.type	getifaddrs, @function
getifaddrs:
	subl	$16, %esp
	movl	$_ZZZgetifaddrs, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getifaddrs, .-getifaddrs

	.section	.rodata
_ZZZputwc_unlocked:
	.string	"putwc_unlocked"
	.text
	.globl	putwc_unlocked
	.type	putwc_unlocked, @function
putwc_unlocked:
	subl	$16, %esp
	movl	$_ZZZputwc_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putwc_unlocked, .-putwc_unlocked

	.section	.rodata
_ZZZprintf_size_info:
	.string	"printf_size_info"
	.text
	.globl	printf_size_info
	.type	printf_size_info, @function
printf_size_info:
	subl	$16, %esp
	movl	$_ZZZprintf_size_info, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	printf_size_info, .-printf_size_info

	.section	.rodata
_ZZZif_nametoindex:
	.string	"if_nametoindex"
	.text
	.globl	if_nametoindex
	.type	if_nametoindex, @function
if_nametoindex:
	subl	$16, %esp
	movl	$_ZZZif_nametoindex, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	if_nametoindex, .-if_nametoindex

	.section	.rodata
_ZZZkey_decryptsession_pk:
	.string	"key_decryptsession_pk"
	.text
	.globl	key_decryptsession_pk
	.type	key_decryptsession_pk, @function
key_decryptsession_pk:
	subl	$16, %esp
	movl	$_ZZZkey_decryptsession_pk, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	key_decryptsession_pk, .-key_decryptsession_pk

	.section	.rodata
_ZZZstrncat:
	.string	"strncat"
	.text
	.globl	strncat
	.type	strncat, @function
strncat:
	subl	$16, %esp
	movl	$_ZZZstrncat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strncat, .-strncat

	.section	.rodata
_ZZZsendfile64:
	.string	"sendfile64"
	.text
	.globl	sendfile64
	.type	sendfile64, @function
sendfile64:
	subl	$16, %esp
	movl	$_ZZZsendfile64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sendfile64, .-sendfile64

	.section	.rodata
_ZZZwcstoimax:
	.string	"wcstoimax"
	.text
	.globl	wcstoimax
	.type	wcstoimax, @function
wcstoimax:
	subl	$16, %esp
	movl	$_ZZZwcstoimax, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcstoimax, .-wcstoimax

	.section	.rodata
_ZZZpwritev:
	.string	"pwritev"
	.text
	.globl	pwritev
	.type	pwritev, @function
pwritev:
	subl	$16, %esp
	movl	$_ZZZpwritev, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pwritev, .-pwritev

	.section	.rodata
_ZZZstrtoull:
	.string	"strtoull"
	.text
	.globl	strtoull
	.type	strtoull, @function
strtoull:
	subl	$16, %esp
	movl	$_ZZZstrtoull, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strtoull, .-strtoull

	.section	.rodata
_ZZZposix_spawnattr_getsigmas:
	.string	"posix_spawnattr_getsigmas"
	.text
	.globl	posix_spawnattr_getsigmas
	.type	posix_spawnattr_getsigmas, @function
posix_spawnattr_getsigmas:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_getsigmas, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_getsigmas, .-posix_spawnattr_getsigmas

	.section	.rodata
_ZZZfputwc_unlocked:
	.string	"fputwc_unlocked"
	.text
	.globl	fputwc_unlocked
	.type	fputwc_unlocked, @function
fputwc_unlocked:
	subl	$16, %esp
	movl	$_ZZZfputwc_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fputwc_unlocked, .-fputwc_unlocked

	.section	.rodata
_ZZZdrand48:
	.string	"drand48"
	.text
	.globl	drand48
	.type	drand48, @function
drand48:
	subl	$16, %esp
	movl	$_ZZZdrand48, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	drand48, .-drand48

	.section	.rodata
_ZZZqsort_r:
	.string	"qsort_r"
	.text
	.globl	qsort_r
	.type	qsort_r, @function
qsort_r:
	subl	$16, %esp
	movl	$_ZZZqsort_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	qsort_r, .-qsort_r

	.section	.rodata
_ZZZxdr_free:
	.string	"xdr_free"
	.text
	.globl	xdr_free
	.type	xdr_free, @function
xdr_free:
	subl	$16, %esp
	movl	$_ZZZxdr_free, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_free, .-xdr_free

	.section	.rodata
_ZZZfileno:
	.string	"fileno"
	.text
	.globl	fileno
	.type	fileno, @function
fileno:
	subl	$16, %esp
	movl	$_ZZZfileno, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fileno, .-fileno

	.section	.rodata
_ZZZpclose:
	.string	"pclose"
	.text
	.globl	pclose
	.type	pclose, @function
pclose:
	subl	$16, %esp
	movl	$_ZZZpclose, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pclose, .-pclose

	.section	.rodata
_ZZZsethostent:
	.string	"sethostent"
	.text
	.globl	sethostent
	.type	sethostent, @function
sethostent:
	subl	$16, %esp
	movl	$_ZZZsethostent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sethostent, .-sethostent

	.section	.rodata
_ZZZinet6_rth_getaddr:
	.string	"inet6_rth_getaddr"
	.text
	.globl	inet6_rth_getaddr
	.type	inet6_rth_getaddr, @function
inet6_rth_getaddr:
	subl	$16, %esp
	movl	$_ZZZinet6_rth_getaddr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_rth_getaddr, .-inet6_rth_getaddr

	.section	.rodata
_ZZZpthread_equal:
	.string	"pthread_equal"
	.text
	.globl	pthread_equal
	.type	pthread_equal, @function
pthread_equal:
	subl	$16, %esp
	movl	$_ZZZpthread_equal, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_equal, .-pthread_equal

	.section	.rodata
_ZZZpthread_mutex_init:
	.string	"pthread_mutex_init"
	.text
	.globl	pthread_mutex_init
	.type	pthread_mutex_init, @function
pthread_mutex_init:
	subl	$16, %esp
	movl	$_ZZZpthread_mutex_init, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_mutex_init, .-pthread_mutex_init

	.section	.rodata
_ZZZusleep:
	.string	"usleep"
	.text
	.globl	usleep
	.type	usleep, @function
usleep:
	subl	$16, %esp
	movl	$_ZZZusleep, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	usleep, .-usleep

	.section	.rodata
_ZZZsigset:
	.string	"sigset"
	.text
	.globl	sigset
	.type	sigset, @function
sigset:
	subl	$16, %esp
	movl	$_ZZZsigset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigset, .-sigset

	.section	.rodata
_ZZZustat:
	.string	"ustat"
	.text
	.globl	ustat
	.type	ustat, @function
ustat:
	subl	$16, %esp
	movl	$_ZZZustat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ustat, .-ustat

	.section	.rodata
_ZZZchown:
	.string	"chown"
	.text
	.globl	chown
	.type	chown, @function
chown:
	subl	$16, %esp
	movl	$_ZZZchown, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	chown, .-chown

	.section	.rodata
_ZZZsplice:
	.string	"splice"
	.text
	.globl	splice
	.type	splice, @function
splice:
	subl	$16, %esp
	movl	$_ZZZsplice, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	splice, .-splice

	.section	.rodata
_ZZZposix_spawn:
	.string	"posix_spawn"
	.text
	.globl	posix_spawn
	.type	posix_spawn, @function
posix_spawn:
	subl	$16, %esp
	movl	$_ZZZposix_spawn, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawn, .-posix_spawn

	.section	.rodata
_ZZZxdr_vector:
	.string	"xdr_vector"
	.text
	.globl	xdr_vector
	.type	xdr_vector, @function
xdr_vector:
	subl	$16, %esp
	movl	$_ZZZxdr_vector, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_vector, .-xdr_vector

	.section	.rodata
_ZZZeventfd_write:
	.string	"eventfd_write"
	.text
	.globl	eventfd_write
	.type	eventfd_write, @function
eventfd_write:
	subl	$16, %esp
	movl	$_ZZZeventfd_write, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	eventfd_write, .-eventfd_write

	.section	.rodata
_ZZZlgetxattr:
	.string	"lgetxattr"
	.text
	.globl	lgetxattr
	.type	lgetxattr, @function
lgetxattr:
	subl	$16, %esp
	movl	$_ZZZlgetxattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lgetxattr, .-lgetxattr

	.section	.rodata
_ZZZxdr_uint8_t:
	.string	"xdr_uint8_t"
	.text
	.globl	xdr_uint8_t
	.type	xdr_uint8_t, @function
xdr_uint8_t:
	subl	$16, %esp
	movl	$_ZZZxdr_uint8_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_uint8_t, .-xdr_uint8_t

	.section	.rodata
_ZZZif_indextoname:
	.string	"if_indextoname"
	.text
	.globl	if_indextoname
	.type	if_indextoname, @function
if_indextoname:
	subl	$16, %esp
	movl	$_ZZZif_indextoname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	if_indextoname, .-if_indextoname

	.section	.rodata
_ZZZauthdes_pk_create:
	.string	"authdes_pk_create"
	.text
	.globl	authdes_pk_create
	.type	authdes_pk_create, @function
authdes_pk_create:
	subl	$16, %esp
	movl	$_ZZZauthdes_pk_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	authdes_pk_create, .-authdes_pk_create

	.section	.rodata
_ZZZsvcerr_decode:
	.string	"svcerr_decode"
	.text
	.globl	svcerr_decode
	.type	svcerr_decode, @function
svcerr_decode:
	subl	$16, %esp
	movl	$_ZZZsvcerr_decode, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcerr_decode, .-svcerr_decode

	.section	.rodata
_ZZZswscanf:
	.string	"swscanf"
	.text
	.globl	swscanf
	.type	swscanf, @function
swscanf:
	subl	$16, %esp
	movl	$_ZZZswscanf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	swscanf, .-swscanf

	.section	.rodata
_ZZZvmsplice:
	.string	"vmsplice"
	.text
	.globl	vmsplice
	.type	vmsplice, @function
vmsplice:
	subl	$16, %esp
	movl	$_ZZZvmsplice, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vmsplice, .-vmsplice

	.section	.rodata
_ZZZupdwtmpx:
	.string	"updwtmpx"
	.text
	.globl	updwtmpx
	.type	updwtmpx, @function
updwtmpx:
	subl	$16, %esp
	movl	$_ZZZupdwtmpx, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	updwtmpx, .-updwtmpx

	.section	.rodata
_ZZZdes_setparity:
	.string	"des_setparity"
	.text
	.globl	des_setparity
	.type	des_setparity, @function
des_setparity:
	subl	$16, %esp
	movl	$_ZZZdes_setparity, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	des_setparity, .-des_setparity

	.section	.rodata
_ZZZgetsourcefilter:
	.string	"getsourcefilter"
	.text
	.globl	getsourcefilter
	.type	getsourcefilter, @function
getsourcefilter:
	subl	$16, %esp
	movl	$_ZZZgetsourcefilter, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getsourcefilter, .-getsourcefilter

	.section	.rodata
_ZZZlrand48_r:
	.string	"lrand48_r"
	.text
	.globl	lrand48_r
	.type	lrand48_r, @function
lrand48_r:
	subl	$16, %esp
	movl	$_ZZZlrand48_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lrand48_r, .-lrand48_r

	.section	.rodata
_ZZZqfcvt_r:
	.string	"qfcvt_r"
	.text
	.globl	qfcvt_r
	.type	qfcvt_r, @function
qfcvt_r:
	subl	$16, %esp
	movl	$_ZZZqfcvt_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	qfcvt_r, .-qfcvt_r

	.section	.rodata
_ZZZfcvt_r:
	.string	"fcvt_r"
	.text
	.globl	fcvt_r
	.type	fcvt_r, @function
fcvt_r:
	subl	$16, %esp
	movl	$_ZZZfcvt_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fcvt_r, .-fcvt_r

	.section	.rodata
_ZZZiconv_close:
	.string	"iconv_close"
	.text
	.globl	iconv_close
	.type	iconv_close, @function
iconv_close:
	subl	$16, %esp
	movl	$_ZZZiconv_close, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	iconv_close, .-iconv_close

	.section	.rodata
_ZZZendttyent:
	.string	"endttyent"
	.text
	.globl	endttyent
	.type	endttyent, @function
endttyent:
	subl	$16, %esp
	movl	$_ZZZendttyent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endttyent, .-endttyent

	.section	.rodata
_ZZZseed48:
	.string	"seed48"
	.text
	.globl	seed48
	.type	seed48, @function
seed48:
	subl	$16, %esp
	movl	$_ZZZseed48, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	seed48, .-seed48

	.section	.rodata
_ZZZrename:
	.string	"rename"
	.text
	.globl	rename
	.type	rename, @function
rename:
	subl	$16, %esp
	movl	$_ZZZrename, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rename, .-rename

	.section	.rodata
_ZZZrtime:
	.string	"rtime"
	.text
	.globl	rtime
	.type	rtime, @function
rtime:
	subl	$16, %esp
	movl	$_ZZZrtime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rtime, .-rtime

	.section	.rodata
_ZZZgetfsent:
	.string	"getfsent"
	.text
	.globl	getfsent
	.type	getfsent, @function
getfsent:
	subl	$16, %esp
	movl	$_ZZZgetfsent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getfsent, .-getfsent

	.section	.rodata
_ZZZepoll_ctl:
	.string	"epoll_ctl"
	.text
	.globl	epoll_ctl
	.type	epoll_ctl, @function
epoll_ctl:
	subl	$16, %esp
	movl	$_ZZZepoll_ctl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	epoll_ctl, .-epoll_ctl

	.section	.rodata
_ZZZfanotify_mark:
	.string	"fanotify_mark"
	.text
	.globl	fanotify_mark
	.type	fanotify_mark, @function
fanotify_mark:
	subl	$16, %esp
	movl	$_ZZZfanotify_mark, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fanotify_mark, .-fanotify_mark

	.section	.rodata
_ZZZmadvise:
	.string	"madvise"
	.text
	.globl	madvise
	.type	madvise, @function
madvise:
	subl	$16, %esp
	movl	$_ZZZmadvise, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	madvise, .-madvise

	.section	.rodata
_ZZZpasswd2des:
	.string	"passwd2des"
	.text
	.globl	passwd2des
	.type	passwd2des, @function
passwd2des:
	subl	$16, %esp
	movl	$_ZZZpasswd2des, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	passwd2des, .-passwd2des

	.section	.rodata
_ZZZgetnetname:
	.string	"getnetname"
	.text
	.globl	getnetname
	.type	getnetname, @function
getnetname:
	subl	$16, %esp
	movl	$_ZZZgetnetname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getnetname, .-getnetname

	.section	.rodata
_ZZZsetnetent:
	.string	"setnetent"
	.text
	.globl	setnetent
	.type	setnetent, @function
setnetent:
	subl	$16, %esp
	movl	$_ZZZsetnetent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setnetent, .-setnetent

	.section	.rodata
_ZZZmkstemp64:
	.string	"mkstemp64"
	.text
	.globl	mkstemp64
	.type	mkstemp64, @function
mkstemp64:
	subl	$16, %esp
	movl	$_ZZZmkstemp64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkstemp64, .-mkstemp64

	.section	.rodata
_ZZZscandir:
	.string	"scandir"
	.text
	.globl	scandir
	.type	scandir, @function
scandir:
	subl	$16, %esp
	movl	$_ZZZscandir, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	scandir, .-scandir

	.section	.rodata
_ZZZgnu_dev_minor:
	.string	"gnu_dev_minor"
	.text
	.globl	gnu_dev_minor
	.type	gnu_dev_minor, @function
gnu_dev_minor:
	subl	$16, %esp
	movl	$_ZZZgnu_dev_minor, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gnu_dev_minor, .-gnu_dev_minor

	.section	.rodata
_ZZZether_hostton:
	.string	"ether_hostton"
	.text
	.globl	ether_hostton
	.type	ether_hostton, @function
ether_hostton:
	subl	$16, %esp
	movl	$_ZZZether_hostton, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ether_hostton, .-ether_hostton

	.section	.rodata
_ZZZmkstemps64:
	.string	"mkstemps64"
	.text
	.globl	mkstemps64
	.type	mkstemps64, @function
mkstemps64:
	subl	$16, %esp
	movl	$_ZZZmkstemps64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkstemps64, .-mkstemps64

	.section	.rodata
_ZZZquotactl:
	.string	"quotactl"
	.text
	.globl	quotactl
	.type	quotactl, @function
quotactl:
	subl	$16, %esp
	movl	$_ZZZquotactl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	quotactl, .-quotactl

	.section	.rodata
_ZZZgetrpcbynumber_r:
	.string	"getrpcbynumber_r"
	.text
	.globl	getrpcbynumber_r
	.type	getrpcbynumber_r, @function
getrpcbynumber_r:
	subl	$16, %esp
	movl	$_ZZZgetrpcbynumber_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getrpcbynumber_r, .-getrpcbynumber_r

	.section	.rodata
_ZZZsigismember:
	.string	"sigismember"
	.text
	.globl	sigismember
	.type	sigismember, @function
sigismember:
	subl	$16, %esp
	movl	$_ZZZsigismember, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigismember, .-sigismember

	.section	.rodata
_ZZZgetttynam:
	.string	"getttynam"
	.text
	.globl	getttynam
	.type	getttynam, @function
getttynam:
	subl	$16, %esp
	movl	$_ZZZgetttynam, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getttynam, .-getttynam

	.section	.rodata
_ZZZatof:
	.string	"atof"
	.text
	.globl	atof
	.type	atof, @function
atof:
	subl	$16, %esp
	movl	$_ZZZatof, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	atof, .-atof

	.section	.rodata
_ZZZpthread_attr_setschedpara:
	.string	"pthread_attr_setschedpara"
	.text
	.globl	pthread_attr_setschedpara
	.type	pthread_attr_setschedpara, @function
pthread_attr_setschedpara:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_setschedpara, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_setschedpara, .-pthread_attr_setschedpara

	.section	.rodata
_ZZZbcopy:
	.string	"bcopy"
	.text
	.globl	bcopy
	.type	bcopy, @function
bcopy:
	subl	$16, %esp
	movl	$_ZZZbcopy, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	bcopy, .-bcopy

	.section	.rodata
_ZZZsetlinebuf:
	.string	"setlinebuf"
	.text
	.globl	setlinebuf
	.type	setlinebuf, @function
setlinebuf:
	subl	$16, %esp
	movl	$_ZZZsetlinebuf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setlinebuf, .-setlinebuf

	.section	.rodata
_ZZZgetsgnam_r:
	.string	"getsgnam_r"
	.text
	.globl	getsgnam_r
	.type	getsgnam_r, @function
getsgnam_r:
	subl	$16, %esp
	movl	$_ZZZgetsgnam_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getsgnam_r, .-getsgnam_r

	.section	.rodata
_ZZZatoi:
	.string	"atoi"
	.text
	.globl	atoi
	.type	atoi, @function
atoi:
	subl	$16, %esp
	movl	$_ZZZatoi, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	atoi, .-atoi

	.section	.rodata
_ZZZxdr_hyper:
	.string	"xdr_hyper"
	.text
	.globl	xdr_hyper
	.type	xdr_hyper, @function
xdr_hyper:
	subl	$16, %esp
	movl	$_ZZZxdr_hyper, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_hyper, .-xdr_hyper

	.section	.rodata
_ZZZstime:
	.string	"stime"
	.text
	.globl	stime
	.type	stime, @function
stime:
	subl	$16, %esp
	movl	$_ZZZstime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	stime, .-stime

	.section	.rodata
_ZZZgetdirentries64:
	.string	"getdirentries64"
	.text
	.globl	getdirentries64
	.type	getdirentries64, @function
getdirentries64:
	subl	$16, %esp
	movl	$_ZZZgetdirentries64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getdirentries64, .-getdirentries64

	.section	.rodata
_ZZZposix_spawnattr_getschedp:
	.string	"posix_spawnattr_getschedp"
	.text
	.globl	posix_spawnattr_getschedp
	.type	posix_spawnattr_getschedp, @function
posix_spawnattr_getschedp:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_getschedp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_getschedp, .-posix_spawnattr_getschedp

	.section	.rodata
_ZZZtcflush:
	.string	"tcflush"
	.text
	.globl	tcflush
	.type	tcflush, @function
tcflush:
	subl	$16, %esp
	movl	$_ZZZtcflush, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tcflush, .-tcflush

	.section	.rodata
_ZZZatol:
	.string	"atol"
	.text
	.globl	atol
	.type	atol, @function
atol:
	subl	$16, %esp
	movl	$_ZZZatol, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	atol, .-atol

	.section	.rodata
_ZZZinet6_opt_find:
	.string	"inet6_opt_find"
	.text
	.globl	inet6_opt_find
	.type	inet6_opt_find, @function
inet6_opt_find:
	subl	$16, %esp
	movl	$_ZZZinet6_opt_find, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_opt_find, .-inet6_opt_find

	.section	.rodata
_ZZZwcstoull:
	.string	"wcstoull"
	.text
	.globl	wcstoull
	.type	wcstoull, @function
wcstoull:
	subl	$16, %esp
	movl	$_ZZZwcstoull, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcstoull, .-wcstoull

	.section	.rodata
_ZZZmlockall:
	.string	"mlockall"
	.text
	.globl	mlockall
	.type	mlockall, @function
mlockall:
	subl	$16, %esp
	movl	$_ZZZmlockall, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mlockall, .-mlockall

	.section	.rodata
_ZZZether_ntohost:
	.string	"ether_ntohost"
	.text
	.globl	ether_ntohost
	.type	ether_ntohost, @function
ether_ntohost:
	subl	$16, %esp
	movl	$_ZZZether_ntohost, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ether_ntohost, .-ether_ntohost

	.section	.rodata
_ZZZftw64:
	.string	"ftw64"
	.text
	.globl	ftw64
	.type	ftw64, @function
ftw64:
	subl	$16, %esp
	movl	$_ZZZftw64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ftw64, .-ftw64

	.section	.rodata
_ZZZstty:
	.string	"stty"
	.text
	.globl	stty
	.type	stty, @function
stty:
	subl	$16, %esp
	movl	$_ZZZstty, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	stty, .-stty

	.section	.rodata
_ZZZunlockpt:
	.string	"unlockpt"
	.text
	.globl	unlockpt
	.type	unlockpt, @function
unlockpt:
	subl	$16, %esp
	movl	$_ZZZunlockpt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	unlockpt, .-unlockpt

	.section	.rodata
_ZZZxdr_union:
	.string	"xdr_union"
	.text
	.globl	xdr_union
	.type	xdr_union, @function
xdr_union:
	subl	$16, %esp
	movl	$_ZZZxdr_union, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_union, .-xdr_union

	.section	.rodata
_ZZZcatgets:
	.string	"catgets"
	.text
	.globl	catgets
	.type	catgets, @function
catgets:
	subl	$16, %esp
	movl	$_ZZZcatgets, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	catgets, .-catgets

	.section	.rodata
_ZZZposix_spawnattr_getschedp:
	.string	"posix_spawnattr_getschedp"
	.text
	.globl	posix_spawnattr_getschedp
	.type	posix_spawnattr_getschedp, @function
posix_spawnattr_getschedp:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_getschedp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_getschedp, .-posix_spawnattr_getschedp

	.section	.rodata
_ZZZlldiv:
	.string	"lldiv"
	.text
	.globl	lldiv
	.type	lldiv, @function
lldiv:
	subl	$16, %esp
	movl	$_ZZZlldiv, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lldiv, .-lldiv

	.section	.rodata
_ZZZtmpnam:
	.string	"tmpnam"
	.text
	.globl	tmpnam
	.type	tmpnam, @function
tmpnam:
	subl	$16, %esp
	movl	$_ZZZtmpnam, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tmpnam, .-tmpnam

	.section	.rodata
_ZZZinet_nsap_ntoa:
	.string	"inet_nsap_ntoa"
	.text
	.globl	inet_nsap_ntoa
	.type	inet_nsap_ntoa, @function
inet_nsap_ntoa:
	subl	$16, %esp
	movl	$_ZZZinet_nsap_ntoa, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet_nsap_ntoa, .-inet_nsap_ntoa

	.section	.rodata
_ZZZstrerror_l:
	.string	"strerror_l"
	.text
	.globl	strerror_l
	.type	strerror_l, @function
strerror_l:
	subl	$16, %esp
	movl	$_ZZZstrerror_l, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strerror_l, .-strerror_l

	.section	.rodata
_ZZZsrand48:
	.string	"srand48"
	.text
	.globl	srand48
	.type	srand48, @function
srand48:
	subl	$16, %esp
	movl	$_ZZZsrand48, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	srand48, .-srand48

	.section	.rodata
_ZZZsvcunixfd_create:
	.string	"svcunixfd_create"
	.text
	.globl	svcunixfd_create
	.type	svcunixfd_create, @function
svcunixfd_create:
	subl	$16, %esp
	movl	$_ZZZsvcunixfd_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcunixfd_create, .-svcunixfd_create

	.section	.rodata
_ZZZftw:
	.string	"ftw"
	.text
	.globl	ftw
	.type	ftw, @function
ftw:
	subl	$16, %esp
	movl	$_ZZZftw, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ftw, .-ftw

	.section	.rodata
_ZZZiopl:
	.string	"iopl"
	.text
	.globl	iopl
	.type	iopl, @function
iopl:
	subl	$16, %esp
	movl	$_ZZZiopl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	iopl, .-iopl

	.section	.rodata
_ZZZsgetspent:
	.string	"sgetspent"
	.text
	.globl	sgetspent
	.type	sgetspent, @function
sgetspent:
	subl	$16, %esp
	movl	$_ZZZsgetspent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sgetspent, .-sgetspent

	.section	.rodata
_ZZZpthread_getschedparam:
	.string	"pthread_getschedparam"
	.text
	.globl	pthread_getschedparam
	.type	pthread_getschedparam, @function
pthread_getschedparam:
	subl	$16, %esp
	movl	$_ZZZpthread_getschedparam, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_getschedparam, .-pthread_getschedparam

	.section	.rodata
_ZZZvhangup:
	.string	"vhangup"
	.text
	.globl	vhangup
	.type	vhangup, @function
vhangup:
	subl	$16, %esp
	movl	$_ZZZvhangup, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vhangup, .-vhangup

	.section	.rodata
_ZZZkey_secretkey_is_set:
	.string	"key_secretkey_is_set"
	.text
	.globl	key_secretkey_is_set
	.type	key_secretkey_is_set, @function
key_secretkey_is_set:
	subl	$16, %esp
	movl	$_ZZZkey_secretkey_is_set, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	key_secretkey_is_set, .-key_secretkey_is_set

	.section	.rodata
_ZZZlocaltime:
	.string	"localtime"
	.text
	.globl	localtime
	.type	localtime, @function
localtime:
	subl	$16, %esp
	movl	$_ZZZlocaltime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	localtime, .-localtime

	.section	.rodata
_ZZZendutxent:
	.string	"endutxent"
	.text
	.globl	endutxent
	.type	endutxent, @function
endutxent:
	subl	$16, %esp
	movl	$_ZZZendutxent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endutxent, .-endutxent

	.section	.rodata
_ZZZferror_unlocked:
	.string	"ferror_unlocked"
	.text
	.globl	ferror_unlocked
	.type	ferror_unlocked, @function
ferror_unlocked:
	subl	$16, %esp
	movl	$_ZZZferror_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ferror_unlocked, .-ferror_unlocked

	.section	.rodata
_ZZZdifftime:
	.string	"difftime"
	.text
	.globl	difftime
	.type	difftime, @function
difftime:
	subl	$16, %esp
	movl	$_ZZZdifftime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	difftime, .-difftime

	.section	.rodata
_ZZZstrchr:
	.string	"strchr"
	.text
	.globl	strchr
	.type	strchr, @function
strchr:
	subl	$16, %esp
	movl	$_ZZZstrchr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strchr, .-strchr

	.section	.rodata
_ZZZcapset:
	.string	"capset"
	.text
	.globl	capset
	.type	capset, @function
capset:
	subl	$16, %esp
	movl	$_ZZZcapset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	capset, .-capset

	.section	.rodata
_ZZZflistxattr:
	.string	"flistxattr"
	.text
	.globl	flistxattr
	.type	flistxattr, @function
flistxattr:
	subl	$16, %esp
	movl	$_ZZZflistxattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	flistxattr, .-flistxattr

	.section	.rodata
_ZZZclnt_spcreateerror:
	.string	"clnt_spcreateerror"
	.text
	.globl	clnt_spcreateerror
	.type	clnt_spcreateerror, @function
clnt_spcreateerror:
	subl	$16, %esp
	movl	$_ZZZclnt_spcreateerror, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clnt_spcreateerror, .-clnt_spcreateerror

	.section	.rodata
_ZZZobstack_free:
	.string	"obstack_free"
	.text
	.globl	obstack_free
	.type	obstack_free, @function
obstack_free:
	subl	$16, %esp
	movl	$_ZZZobstack_free, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	obstack_free, .-obstack_free

	.section	.rodata
_ZZZpthread_attr_getscope:
	.string	"pthread_attr_getscope"
	.text
	.globl	pthread_attr_getscope
	.type	pthread_attr_getscope, @function
pthread_attr_getscope:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_getscope, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_getscope, .-pthread_attr_getscope

	.section	.rodata
_ZZZgetaliasent:
	.string	"getaliasent"
	.text
	.globl	getaliasent
	.type	getaliasent, @function
getaliasent:
	subl	$16, %esp
	movl	$_ZZZgetaliasent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getaliasent, .-getaliasent

	.section	.rodata
_ZZZrresvport_af:
	.string	"rresvport_af"
	.text
	.globl	rresvport_af
	.type	rresvport_af, @function
rresvport_af:
	subl	$16, %esp
	movl	$_ZZZrresvport_af, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rresvport_af, .-rresvport_af

	.section	.rodata
_ZZZsigignore:
	.string	"sigignore"
	.text
	.globl	sigignore
	.type	sigignore, @function
sigignore:
	subl	$16, %esp
	movl	$_ZZZsigignore, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigignore, .-sigignore

	.section	.rodata
_ZZZsvcerr_weakauth:
	.string	"svcerr_weakauth"
	.text
	.globl	svcerr_weakauth
	.type	svcerr_weakauth, @function
svcerr_weakauth:
	subl	$16, %esp
	movl	$_ZZZsvcerr_weakauth, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcerr_weakauth, .-svcerr_weakauth

	.section	.rodata
_ZZZfprintf:
	.string	"fprintf"
	.text
	.globl	fprintf
	.type	fprintf, @function
fprintf:
	subl	$16, %esp
	movl	$_ZZZfprintf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fprintf, .-fprintf

	.section	.rodata
_ZZZgetsockname:
	.string	"getsockname"
	.text
	.globl	getsockname
	.type	getsockname, @function
getsockname:
	subl	$16, %esp
	movl	$_ZZZgetsockname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getsockname, .-getsockname

	.section	.rodata
_ZZZscandir64:
	.string	"scandir64"
	.text
	.globl	scandir64
	.type	scandir64, @function
scandir64:
	subl	$16, %esp
	movl	$_ZZZscandir64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	scandir64, .-scandir64

	.section	.rodata
_ZZZutime:
	.string	"utime"
	.text
	.globl	utime
	.type	utime, @function
utime:
	subl	$16, %esp
	movl	$_ZZZutime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	utime, .-utime

	.section	.rodata
_ZZZhsearch:
	.string	"hsearch"
	.text
	.globl	hsearch
	.type	hsearch, @function
hsearch:
	subl	$16, %esp
	movl	$_ZZZhsearch, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	hsearch, .-hsearch

	.section	.rodata
_ZZZabs:
	.string	"abs"
	.text
	.globl	abs
	.type	abs, @function
abs:
	subl	$16, %esp
	movl	$_ZZZabs, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	abs, .-abs

	.section	.rodata
_ZZZgetgrent_r:
	.string	"getgrent_r"
	.text
	.globl	getgrent_r
	.type	getgrent_r, @function
getgrent_r:
	subl	$16, %esp
	movl	$_ZZZgetgrent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getgrent_r, .-getgrent_r

	.section	.rodata
_ZZZaddseverity:
	.string	"addseverity"
	.text
	.globl	addseverity
	.type	addseverity, @function
addseverity:
	subl	$16, %esp
	movl	$_ZZZaddseverity, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	addseverity, .-addseverity

	.section	.rodata
_ZZZgetgrent_r:
	.string	"getgrent_r"
	.text
	.globl	getgrent_r
	.type	getgrent_r, @function
getgrent_r:
	subl	$16, %esp
	movl	$_ZZZgetgrent_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getgrent_r, .-getgrent_r

	.section	.rodata
_ZZZepoll_create1:
	.string	"epoll_create1"
	.text
	.globl	epoll_create1
	.type	epoll_create1, @function
epoll_create1:
	subl	$16, %esp
	movl	$_ZZZepoll_create1, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	epoll_create1, .-epoll_create1

	.section	.rodata
_ZZZxprt_register:
	.string	"xprt_register"
	.text
	.globl	xprt_register
	.type	xprt_register, @function
xprt_register:
	subl	$16, %esp
	movl	$_ZZZxprt_register, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xprt_register, .-xprt_register

	.section	.rodata
_ZZZkey_gendes:
	.string	"key_gendes"
	.text
	.globl	key_gendes
	.type	key_gendes, @function
key_gendes:
	subl	$16, %esp
	movl	$_ZZZkey_gendes, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	key_gendes, .-key_gendes

	.section	.rodata
_ZZZmktime:
	.string	"mktime"
	.text
	.globl	mktime
	.type	mktime, @function
mktime:
	subl	$16, %esp
	movl	$_ZZZmktime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mktime, .-mktime

	.section	.rodata
_ZZZmblen:
	.string	"mblen"
	.text
	.globl	mblen
	.type	mblen, @function
mblen:
	subl	$16, %esp
	movl	$_ZZZmblen, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mblen, .-mblen

	.section	.rodata
_ZZZclnt_create:
	.string	"clnt_create"
	.text
	.globl	clnt_create
	.type	clnt_create, @function
clnt_create:
	subl	$16, %esp
	movl	$_ZZZclnt_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clnt_create, .-clnt_create

	.section	.rodata
_ZZZalphasort:
	.string	"alphasort"
	.text
	.globl	alphasort
	.type	alphasort, @function
alphasort:
	subl	$16, %esp
	movl	$_ZZZalphasort, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	alphasort, .-alphasort

	.section	.rodata
_ZZZxdr_rmtcall_args:
	.string	"xdr_rmtcall_args"
	.text
	.globl	xdr_rmtcall_args
	.type	xdr_rmtcall_args, @function
xdr_rmtcall_args:
	subl	$16, %esp
	movl	$_ZZZxdr_rmtcall_args, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_rmtcall_args, .-xdr_rmtcall_args

	.section	.rodata
_ZZZxdrstdio_create:
	.string	"xdrstdio_create"
	.text
	.globl	xdrstdio_create
	.type	xdrstdio_create, @function
xdrstdio_create:
	subl	$16, %esp
	movl	$_ZZZxdrstdio_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdrstdio_create, .-xdrstdio_create

	.section	.rodata
_ZZZstrtoimax:
	.string	"strtoimax"
	.text
	.globl	strtoimax
	.type	strtoimax, @function
strtoimax:
	subl	$16, %esp
	movl	$_ZZZstrtoimax, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strtoimax, .-strtoimax

	.section	.rodata
_ZZZgetrpcbyname_r:
	.string	"getrpcbyname_r"
	.text
	.globl	getrpcbyname_r
	.type	getrpcbyname_r, @function
getrpcbyname_r:
	subl	$16, %esp
	movl	$_ZZZgetrpcbyname_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getrpcbyname_r, .-getrpcbyname_r

	.section	.rodata
_ZZZiconv:
	.string	"iconv"
	.text
	.globl	iconv
	.type	iconv, @function
iconv:
	subl	$16, %esp
	movl	$_ZZZiconv, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	iconv, .-iconv

	.section	.rodata
_ZZZget_myaddress:
	.string	"get_myaddress"
	.text
	.globl	get_myaddress
	.type	get_myaddress, @function
get_myaddress:
	subl	$16, %esp
	movl	$_ZZZget_myaddress, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	get_myaddress, .-get_myaddress

	.section	.rodata
_ZZZgetrpcbyname_r:
	.string	"getrpcbyname_r"
	.text
	.globl	getrpcbyname_r
	.type	getrpcbyname_r, @function
getrpcbyname_r:
	subl	$16, %esp
	movl	$_ZZZgetrpcbyname_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getrpcbyname_r, .-getrpcbyname_r

	.section	.rodata
_ZZZbdflush:
	.string	"bdflush"
	.text
	.globl	bdflush
	.type	bdflush, @function
bdflush:
	subl	$16, %esp
	movl	$_ZZZbdflush, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	bdflush, .-bdflush

	.section	.rodata
_ZZZmkstemps:
	.string	"mkstemps"
	.text
	.globl	mkstemps
	.type	mkstemps, @function
mkstemps:
	subl	$16, %esp
	movl	$_ZZZmkstemps, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkstemps, .-mkstemps

	.section	.rodata
_ZZZlremovexattr:
	.string	"lremovexattr"
	.text
	.globl	lremovexattr
	.type	lremovexattr, @function
lremovexattr:
	subl	$16, %esp
	movl	$_ZZZlremovexattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lremovexattr, .-lremovexattr

	.section	.rodata
_ZZZfdopen:
	.string	"fdopen"
	.text
	.globl	fdopen
	.type	fdopen, @function
fdopen:
	subl	$16, %esp
	movl	$_ZZZfdopen, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fdopen, .-fdopen

	.section	.rodata
_ZZZsetusershell:
	.string	"setusershell"
	.text
	.globl	setusershell
	.type	setusershell, @function
setusershell:
	subl	$16, %esp
	movl	$_ZZZsetusershell, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setusershell, .-setusershell

	.section	.rodata
_ZZZfdopen:
	.string	"fdopen"
	.text
	.globl	fdopen
	.type	fdopen, @function
fdopen:
	subl	$16, %esp
	movl	$_ZZZfdopen, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fdopen, .-fdopen

	.section	.rodata
_ZZZreaddir64:
	.string	"readdir64"
	.text
	.globl	readdir64
	.type	readdir64, @function
readdir64:
	subl	$16, %esp
	movl	$_ZZZreaddir64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	readdir64, .-readdir64

	.section	.rodata
_ZZZsvcerr_auth:
	.string	"svcerr_auth"
	.text
	.globl	svcerr_auth
	.type	svcerr_auth, @function
svcerr_auth:
	subl	$16, %esp
	movl	$_ZZZsvcerr_auth, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcerr_auth, .-svcerr_auth

	.section	.rodata
_ZZZxdr_callmsg:
	.string	"xdr_callmsg"
	.text
	.globl	xdr_callmsg
	.type	xdr_callmsg, @function
xdr_callmsg:
	subl	$16, %esp
	movl	$_ZZZxdr_callmsg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_callmsg, .-xdr_callmsg

	.section	.rodata
_ZZZqsort:
	.string	"qsort"
	.text
	.globl	qsort
	.type	qsort, @function
qsort:
	subl	$16, %esp
	movl	$_ZZZqsort, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	qsort, .-qsort

	.section	.rodata
_ZZZiconv_open:
	.string	"iconv_open"
	.text
	.globl	iconv_open
	.type	iconv_open, @function
iconv_open:
	subl	$16, %esp
	movl	$_ZZZiconv_open, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	iconv_open, .-iconv_open

	.section	.rodata
_ZZZmrand48:
	.string	"mrand48"
	.text
	.globl	mrand48
	.type	mrand48, @function
mrand48:
	subl	$16, %esp
	movl	$_ZZZmrand48, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mrand48, .-mrand48

	.section	.rodata
_ZZZwcstombs:
	.string	"wcstombs"
	.text
	.globl	wcstombs
	.type	wcstombs, @function
wcstombs:
	subl	$16, %esp
	movl	$_ZZZwcstombs, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcstombs, .-wcstombs

	.section	.rodata
_ZZZposix_spawnattr_getflags:
	.string	"posix_spawnattr_getflags"
	.text
	.globl	posix_spawnattr_getflags
	.type	posix_spawnattr_getflags, @function
posix_spawnattr_getflags:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_getflags, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_getflags, .-posix_spawnattr_getflags

	.section	.rodata
_ZZZgethostbyname2:
	.string	"gethostbyname2"
	.text
	.globl	gethostbyname2
	.type	gethostbyname2, @function
gethostbyname2:
	subl	$16, %esp
	movl	$_ZZZgethostbyname2, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gethostbyname2, .-gethostbyname2

	.section	.rodata
_ZZZcbc_crypt:
	.string	"cbc_crypt"
	.text
	.globl	cbc_crypt
	.type	cbc_crypt, @function
cbc_crypt:
	subl	$16, %esp
	movl	$_ZZZcbc_crypt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	cbc_crypt, .-cbc_crypt

	.section	.rodata
_ZZZenvz_get:
	.string	"envz_get"
	.text
	.globl	envz_get
	.type	envz_get, @function
envz_get:
	subl	$16, %esp
	movl	$_ZZZenvz_get, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	envz_get, .-envz_get

	.section	.rodata
_ZZZxdr_netnamestr:
	.string	"xdr_netnamestr"
	.text
	.globl	xdr_netnamestr
	.type	xdr_netnamestr, @function
xdr_netnamestr:
	subl	$16, %esp
	movl	$_ZZZxdr_netnamestr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_netnamestr, .-xdr_netnamestr

	.section	.rodata
_ZZZposix_spawnattr_setsigmas:
	.string	"posix_spawnattr_setsigmas"
	.text
	.globl	posix_spawnattr_setsigmas
	.type	posix_spawnattr_setsigmas, @function
posix_spawnattr_setsigmas:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_setsigmas, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_setsigmas, .-posix_spawnattr_setsigmas

	.section	.rodata
_ZZZhstrerror:
	.string	"hstrerror"
	.text
	.globl	hstrerror
	.type	hstrerror, @function
hstrerror:
	subl	$16, %esp
	movl	$_ZZZhstrerror, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	hstrerror, .-hstrerror

	.section	.rodata
_ZZZinotify_add_watch:
	.string	"inotify_add_watch"
	.text
	.globl	inotify_add_watch
	.type	inotify_add_watch, @function
inotify_add_watch:
	subl	$16, %esp
	movl	$_ZZZinotify_add_watch, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inotify_add_watch, .-inotify_add_watch

	.section	.rodata
_ZZZtoascii:
	.string	"toascii"
	.text
	.globl	toascii
	.type	toascii, @function
toascii:
	subl	$16, %esp
	movl	$_ZZZtoascii, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	toascii, .-toascii

	.section	.rodata
_ZZZauthnone_create:
	.string	"authnone_create"
	.text
	.globl	authnone_create
	.type	authnone_create, @function
authnone_create:
	subl	$16, %esp
	movl	$_ZZZauthnone_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	authnone_create, .-authnone_create

	.section	.rodata
_ZZZgetutxline:
	.string	"getutxline"
	.text
	.globl	getutxline
	.type	getutxline, @function
getutxline:
	subl	$16, %esp
	movl	$_ZZZgetutxline, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getutxline, .-getutxline

	.section	.rodata
_ZZZsethostid:
	.string	"sethostid"
	.text
	.globl	sethostid
	.type	sethostid, @function
sethostid:
	subl	$16, %esp
	movl	$_ZZZsethostid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sethostid, .-sethostid

	.section	.rodata
_ZZZtmpfile64:
	.string	"tmpfile64"
	.text
	.globl	tmpfile64
	.type	tmpfile64, @function
tmpfile64:
	subl	$16, %esp
	movl	$_ZZZtmpfile64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tmpfile64, .-tmpfile64

	.section	.rodata
_ZZZwcsxfrm:
	.string	"wcsxfrm"
	.text
	.globl	wcsxfrm
	.type	wcsxfrm, @function
wcsxfrm:
	subl	$16, %esp
	movl	$_ZZZwcsxfrm, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcsxfrm, .-wcsxfrm

	.section	.rodata
_ZZZvm86:
	.string	"vm86"
	.text
	.globl	vm86
	.type	vm86, @function
vm86:
	subl	$16, %esp
	movl	$_ZZZvm86, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vm86, .-vm86

	.section	.rodata
_ZZZclntraw_create:
	.string	"clntraw_create"
	.text
	.globl	clntraw_create
	.type	clntraw_create, @function
clntraw_create:
	subl	$16, %esp
	movl	$_ZZZclntraw_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clntraw_create, .-clntraw_create

	.section	.rodata
_ZZZpwritev64:
	.string	"pwritev64"
	.text
	.globl	pwritev64
	.type	pwritev64, @function
pwritev64:
	subl	$16, %esp
	movl	$_ZZZpwritev64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pwritev64, .-pwritev64

	.section	.rodata
_ZZZinsque:
	.string	"insque"
	.text
	.globl	insque
	.type	insque, @function
insque:
	subl	$16, %esp
	movl	$_ZZZinsque, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	insque, .-insque

	.section	.rodata
_ZZZepoll_pwait:
	.string	"epoll_pwait"
	.text
	.globl	epoll_pwait
	.type	epoll_pwait, @function
epoll_pwait:
	subl	$16, %esp
	movl	$_ZZZepoll_pwait, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	epoll_pwait, .-epoll_pwait

	.section	.rodata
_ZZZgetutxent:
	.string	"getutxent"
	.text
	.globl	getutxent
	.type	getutxent, @function
getutxent:
	subl	$16, %esp
	movl	$_ZZZgetutxent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getutxent, .-getutxent

	.section	.rodata
_ZZZfputws_unlocked:
	.string	"fputws_unlocked"
	.text
	.globl	fputws_unlocked
	.type	fputws_unlocked, @function
fputws_unlocked:
	subl	$16, %esp
	movl	$_ZZZfputws_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fputws_unlocked, .-fputws_unlocked

	.section	.rodata
_ZZZxdr_array:
	.string	"xdr_array"
	.text
	.globl	xdr_array
	.type	xdr_array, @function
xdr_array:
	subl	$16, %esp
	movl	$_ZZZxdr_array, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_array, .-xdr_array

	.section	.rodata
_ZZZllistxattr:
	.string	"llistxattr"
	.text
	.globl	llistxattr
	.type	llistxattr, @function
llistxattr:
	subl	$16, %esp
	movl	$_ZZZllistxattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	llistxattr, .-llistxattr

	.section	.rodata
_ZZZsyscall:
	.string	"syscall"
	.text
	.globl	syscall
	.type	syscall, @function
syscall:
	subl	$16, %esp
	movl	$_ZZZsyscall, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	syscall, .-syscall

	.section	.rodata
_ZZZsigpending:
	.string	"sigpending"
	.text
	.globl	sigpending
	.type	sigpending, @function
sigpending:
	subl	$16, %esp
	movl	$_ZZZsigpending, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigpending, .-sigpending

	.section	.rodata
_ZZZbsearch:
	.string	"bsearch"
	.text
	.globl	bsearch
	.type	bsearch, @function
bsearch:
	subl	$16, %esp
	movl	$_ZZZbsearch, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	bsearch, .-bsearch

	.section	.rodata
_ZZZfreeaddrinfo:
	.string	"freeaddrinfo"
	.text
	.globl	freeaddrinfo
	.type	freeaddrinfo, @function
freeaddrinfo:
	subl	$16, %esp
	movl	$_ZZZfreeaddrinfo, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	freeaddrinfo, .-freeaddrinfo

	.section	.rodata
_ZZZgetprotobyname_r:
	.string	"getprotobyname_r"
	.text
	.globl	getprotobyname_r
	.type	getprotobyname_r, @function
getprotobyname_r:
	subl	$16, %esp
	movl	$_ZZZgetprotobyname_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getprotobyname_r, .-getprotobyname_r

	.section	.rodata
_ZZZgethostbyaddr_r:
	.string	"gethostbyaddr_r"
	.text
	.globl	gethostbyaddr_r
	.type	gethostbyaddr_r, @function
gethostbyaddr_r:
	subl	$16, %esp
	movl	$_ZZZgethostbyaddr_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gethostbyaddr_r, .-gethostbyaddr_r

	.section	.rodata
_ZZZfgetpwent:
	.string	"fgetpwent"
	.text
	.globl	fgetpwent
	.type	fgetpwent, @function
fgetpwent:
	subl	$16, %esp
	movl	$_ZZZfgetpwent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fgetpwent, .-fgetpwent

	.section	.rodata
_ZZZgethostbyaddr_r:
	.string	"gethostbyaddr_r"
	.text
	.globl	gethostbyaddr_r
	.type	gethostbyaddr_r, @function
gethostbyaddr_r:
	subl	$16, %esp
	movl	$_ZZZgethostbyaddr_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gethostbyaddr_r, .-gethostbyaddr_r

	.section	.rodata
_ZZZsetaliasent:
	.string	"setaliasent"
	.text
	.globl	setaliasent
	.type	setaliasent, @function
setaliasent:
	subl	$16, %esp
	movl	$_ZZZsetaliasent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setaliasent, .-setaliasent

	.section	.rodata
_ZZZxdr_rejected_reply:
	.string	"xdr_rejected_reply"
	.text
	.globl	xdr_rejected_reply
	.type	xdr_rejected_reply, @function
xdr_rejected_reply:
	subl	$16, %esp
	movl	$_ZZZxdr_rejected_reply, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_rejected_reply, .-xdr_rejected_reply

	.section	.rodata
_ZZZcapget:
	.string	"capget"
	.text
	.globl	capget
	.type	capget, @function
capget:
	subl	$16, %esp
	movl	$_ZZZcapget, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	capget, .-capget

	.section	.rodata
_ZZZreaddir64_r:
	.string	"readdir64_r"
	.text
	.globl	readdir64_r
	.type	readdir64_r, @function
readdir64_r:
	subl	$16, %esp
	movl	$_ZZZreaddir64_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	readdir64_r, .-readdir64_r

	.section	.rodata
_ZZZgetpublickey:
	.string	"getpublickey"
	.text
	.globl	getpublickey
	.type	getpublickey, @function
getpublickey:
	subl	$16, %esp
	movl	$_ZZZgetpublickey, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpublickey, .-getpublickey

	.section	.rodata
_ZZZsvc_unregister:
	.string	"svc_unregister"
	.text
	.globl	svc_unregister
	.type	svc_unregister, @function
svc_unregister:
	subl	$16, %esp
	movl	$_ZZZsvc_unregister, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svc_unregister, .-svc_unregister

	.section	.rodata
_ZZZfts_open:
	.string	"fts_open"
	.text
	.globl	fts_open
	.type	fts_open, @function
fts_open:
	subl	$16, %esp
	movl	$_ZZZfts_open, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fts_open, .-fts_open

	.section	.rodata
_ZZZsgetsgent:
	.string	"sgetsgent"
	.text
	.globl	sgetsgent
	.type	sgetsgent, @function
sgetsgent:
	subl	$16, %esp
	movl	$_ZZZsgetsgent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sgetsgent, .-sgetsgent

	.section	.rodata
_ZZZposix_spawnattr_getsigdef:
	.string	"posix_spawnattr_getsigdef"
	.text
	.globl	posix_spawnattr_getsigdef
	.type	posix_spawnattr_getsigdef, @function
posix_spawnattr_getsigdef:
	subl	$16, %esp
	movl	$_ZZZposix_spawnattr_getsigdef, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnattr_getsigdef, .-posix_spawnattr_getsigdef

	.section	.rodata
_ZZZprintf_size:
	.string	"printf_size"
	.text
	.globl	printf_size
	.type	printf_size, @function
printf_size:
	subl	$16, %esp
	movl	$_ZZZprintf_size, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	printf_size, .-printf_size

	.section	.rodata
_ZZZpthread_attr_destroy:
	.string	"pthread_attr_destroy"
	.text
	.globl	pthread_attr_destroy
	.type	pthread_attr_destroy, @function
pthread_attr_destroy:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_destroy, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_destroy, .-pthread_attr_destroy

	.section	.rodata
_ZZZxdr_uint64_t:
	.string	"xdr_uint64_t"
	.text
	.globl	xdr_uint64_t
	.type	xdr_uint64_t, @function
xdr_uint64_t:
	subl	$16, %esp
	movl	$_ZZZxdr_uint64_t, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_uint64_t, .-xdr_uint64_t

	.section	.rodata
_ZZZsvcunix_create:
	.string	"svcunix_create"
	.text
	.globl	svcunix_create
	.type	svcunix_create, @function
svcunix_create:
	subl	$16, %esp
	movl	$_ZZZsvcunix_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svcunix_create, .-svcunix_create

	.section	.rodata
_ZZZcfsetspeed:
	.string	"cfsetspeed"
	.text
	.globl	cfsetspeed
	.type	cfsetspeed, @function
cfsetspeed:
	subl	$16, %esp
	movl	$_ZZZcfsetspeed, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	cfsetspeed, .-cfsetspeed

	.section	.rodata
_ZZZgetrlimit64:
	.string	"getrlimit64"
	.text
	.globl	getrlimit64
	.type	getrlimit64, @function
getrlimit64:
	subl	$16, %esp
	movl	$_ZZZgetrlimit64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getrlimit64, .-getrlimit64

	.section	.rodata
_ZZZwcsspn:
	.string	"wcsspn"
	.text
	.globl	wcsspn
	.type	wcsspn, @function
wcsspn:
	subl	$16, %esp
	movl	$_ZZZwcsspn, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcsspn, .-wcsspn

	.section	.rodata
_ZZZgetrlimit64:
	.string	"getrlimit64"
	.text
	.globl	getrlimit64
	.type	getrlimit64, @function
getrlimit64:
	subl	$16, %esp
	movl	$_ZZZgetrlimit64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getrlimit64, .-getrlimit64

	.section	.rodata
_ZZZinet6_option_init:
	.string	"inet6_option_init"
	.text
	.globl	inet6_option_init
	.type	inet6_option_init, @function
inet6_option_init:
	subl	$16, %esp
	movl	$_ZZZinet6_option_init, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_option_init, .-inet6_option_init

	.section	.rodata
_ZZZecvt:
	.string	"ecvt"
	.text
	.globl	ecvt
	.type	ecvt, @function
ecvt:
	subl	$16, %esp
	movl	$_ZZZecvt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ecvt, .-ecvt

	.section	.rodata
_ZZZbindresvport:
	.string	"bindresvport"
	.text
	.globl	bindresvport
	.type	bindresvport, @function
bindresvport:
	subl	$16, %esp
	movl	$_ZZZbindresvport, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	bindresvport, .-bindresvport

	.section	.rodata
_ZZZrresvport:
	.string	"rresvport"
	.text
	.globl	rresvport
	.type	rresvport, @function
rresvport:
	subl	$16, %esp
	movl	$_ZZZrresvport, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	rresvport, .-rresvport

	.section	.rodata
_ZZZcfsetospeed:
	.string	"cfsetospeed"
	.text
	.globl	cfsetospeed
	.type	cfsetospeed, @function
cfsetospeed:
	subl	$16, %esp
	movl	$_ZZZcfsetospeed, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	cfsetospeed, .-cfsetospeed

	.section	.rodata
_ZZZfwide:
	.string	"fwide"
	.text
	.globl	fwide
	.type	fwide, @function
fwide:
	subl	$16, %esp
	movl	$_ZZZfwide, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fwide, .-fwide

	.section	.rodata
_ZZZgetgrgid_r:
	.string	"getgrgid_r"
	.text
	.globl	getgrgid_r
	.type	getgrgid_r, @function
getgrgid_r:
	subl	$16, %esp
	movl	$_ZZZgetgrgid_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getgrgid_r, .-getgrgid_r

	.section	.rodata
_ZZZpthread_cond_init:
	.string	"pthread_cond_init"
	.text
	.globl	pthread_cond_init
	.type	pthread_cond_init, @function
pthread_cond_init:
	subl	$16, %esp
	movl	$_ZZZpthread_cond_init, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_cond_init, .-pthread_cond_init

	.section	.rodata
_ZZZsetpgrp:
	.string	"setpgrp"
	.text
	.globl	setpgrp
	.type	setpgrp, @function
setpgrp:
	subl	$16, %esp
	movl	$_ZZZsetpgrp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setpgrp, .-setpgrp

	.section	.rodata
_ZZZcfgetispeed:
	.string	"cfgetispeed"
	.text
	.globl	cfgetispeed
	.type	cfgetispeed, @function
cfgetispeed:
	subl	$16, %esp
	movl	$_ZZZcfgetispeed, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	cfgetispeed, .-cfgetispeed

	.section	.rodata
_ZZZwcsdup:
	.string	"wcsdup"
	.text
	.globl	wcsdup
	.type	wcsdup, @function
wcsdup:
	subl	$16, %esp
	movl	$_ZZZwcsdup, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcsdup, .-wcsdup

	.section	.rodata
_ZZZatoll:
	.string	"atoll"
	.text
	.globl	atoll
	.type	atoll, @function
atoll:
	subl	$16, %esp
	movl	$_ZZZatoll, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	atoll, .-atoll

	.section	.rodata
_ZZZxdrrec_create:
	.string	"xdrrec_create"
	.text
	.globl	xdrrec_create
	.type	xdrrec_create, @function
xdrrec_create:
	subl	$16, %esp
	movl	$_ZZZxdrrec_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdrrec_create, .-xdrrec_create

	.section	.rodata
_ZZZfsetxattr:
	.string	"fsetxattr"
	.text
	.globl	fsetxattr
	.type	fsetxattr, @function
fsetxattr:
	subl	$16, %esp
	movl	$_ZZZfsetxattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fsetxattr, .-fsetxattr

	.section	.rodata
_ZZZlabs:
	.string	"labs"
	.text
	.globl	labs
	.type	labs, @function
labs:
	subl	$16, %esp
	movl	$_ZZZlabs, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	labs, .-labs

	.section	.rodata
_ZZZxdr_cryptkeyres:
	.string	"xdr_cryptkeyres"
	.text
	.globl	xdr_cryptkeyres
	.type	xdr_cryptkeyres, @function
xdr_cryptkeyres:
	subl	$16, %esp
	movl	$_ZZZxdr_cryptkeyres, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_cryptkeyres, .-xdr_cryptkeyres

	.section	.rodata
_ZZZinnetgr:
	.string	"innetgr"
	.text
	.globl	innetgr
	.type	innetgr, @function
innetgr:
	subl	$16, %esp
	movl	$_ZZZinnetgr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	innetgr, .-innetgr

	.section	.rodata
_ZZZfutimesat:
	.string	"futimesat"
	.text
	.globl	futimesat
	.type	futimesat, @function
futimesat:
	subl	$16, %esp
	movl	$_ZZZfutimesat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	futimesat, .-futimesat

	.section	.rodata
_ZZZclntudp_create:
	.string	"clntudp_create"
	.text
	.globl	clntudp_create
	.type	clntudp_create, @function
clntudp_create:
	subl	$16, %esp
	movl	$_ZZZclntudp_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clntudp_create, .-clntudp_create

	.section	.rodata
_ZZZgetprotobyname:
	.string	"getprotobyname"
	.text
	.globl	getprotobyname
	.type	getprotobyname, @function
getprotobyname:
	subl	$16, %esp
	movl	$_ZZZgetprotobyname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getprotobyname, .-getprotobyname

	.section	.rodata
_ZZZgetrlimit:
	.string	"getrlimit"
	.text
	.globl	getrlimit
	.type	getrlimit, @function
getrlimit:
	subl	$16, %esp
	movl	$_ZZZgetrlimit, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getrlimit, .-getrlimit

	.section	.rodata
_ZZZscanf:
	.string	"scanf"
	.text
	.globl	scanf
	.type	scanf, @function
scanf:
	subl	$16, %esp
	movl	$_ZZZscanf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	scanf, .-scanf

	.section	.rodata
_ZZZisdigit:
	.string	"isdigit"
	.text
	.globl	isdigit
	.type	isdigit, @function
isdigit:
	subl	$16, %esp
	movl	$_ZZZisdigit, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isdigit, .-isdigit

	.section	.rodata
_ZZZgetxattr:
	.string	"getxattr"
	.text
	.globl	getxattr
	.type	getxattr, @function
getxattr:
	subl	$16, %esp
	movl	$_ZZZgetxattr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getxattr, .-getxattr

	.section	.rodata
_ZZZlchmod:
	.string	"lchmod"
	.text
	.globl	lchmod
	.type	lchmod, @function
lchmod:
	subl	$16, %esp
	movl	$_ZZZlchmod, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	lchmod, .-lchmod

	.section	.rodata
_ZZZkey_encryptsession:
	.string	"key_encryptsession"
	.text
	.globl	key_encryptsession
	.type	key_encryptsession, @function
key_encryptsession:
	subl	$16, %esp
	movl	$_ZZZkey_encryptsession, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	key_encryptsession, .-key_encryptsession

	.section	.rodata
_ZZZiscntrl:
	.string	"iscntrl"
	.text
	.globl	iscntrl
	.type	iscntrl, @function
iscntrl:
	subl	$16, %esp
	movl	$_ZZZiscntrl, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	iscntrl, .-iscntrl

	.section	.rodata
_ZZZerrx:
	.string	"errx"
	.text
	.globl	errx
	.type	errx, @function
errx:
	subl	$16, %esp
	movl	$_ZZZerrx, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	errx, .-errx

	.section	.rodata
_ZZZwmemchr:
	.string	"wmemchr"
	.text
	.globl	wmemchr
	.type	wmemchr, @function
wmemchr:
	subl	$16, %esp
	movl	$_ZZZwmemchr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wmemchr, .-wmemchr

	.section	.rodata
_ZZZmemmove:
	.string	"memmove"
	.text
	.globl	memmove
	.type	memmove, @function
memmove:
	subl	$16, %esp
	movl	$_ZZZmemmove, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	memmove, .-memmove

	.section	.rodata
_ZZZkey_setnet:
	.string	"key_setnet"
	.text
	.globl	key_setnet
	.type	key_setnet, @function
key_setnet:
	subl	$16, %esp
	movl	$_ZZZkey_setnet, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	key_setnet, .-key_setnet

	.section	.rodata
_ZZZsvc_getreqset:
	.string	"svc_getreqset"
	.text
	.globl	svc_getreqset
	.type	svc_getreqset, @function
svc_getreqset:
	subl	$16, %esp
	movl	$_ZZZsvc_getreqset, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svc_getreqset, .-svc_getreqset

	.section	.rodata
_ZZZwcstod:
	.string	"wcstod"
	.text
	.globl	wcstod
	.type	wcstod, @function
wcstod:
	subl	$16, %esp
	movl	$_ZZZwcstod, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcstod, .-wcstod

	.section	.rodata
_ZZZposix_spawnp:
	.string	"posix_spawnp"
	.text
	.globl	posix_spawnp
	.type	posix_spawnp, @function
posix_spawnp:
	subl	$16, %esp
	movl	$_ZZZposix_spawnp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawnp, .-posix_spawnp

	.section	.rodata
_ZZZmprobe:
	.string	"mprobe"
	.text
	.globl	mprobe
	.type	mprobe, @function
mprobe:
	subl	$16, %esp
	movl	$_ZZZmprobe, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mprobe, .-mprobe

	.section	.rodata
_ZZZwcstof:
	.string	"wcstof"
	.text
	.globl	wcstof
	.type	wcstof, @function
wcstof:
	subl	$16, %esp
	movl	$_ZZZwcstof, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcstof, .-wcstof

	.section	.rodata
_ZZZpthread_self:
	.string	"pthread_self"
	.text
	.globl	pthread_self
	.type	pthread_self, @function
pthread_self:
	subl	$16, %esp
	movl	$_ZZZpthread_self, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_self, .-pthread_self

	.section	.rodata
_ZZZwcstok:
	.string	"wcstok"
	.text
	.globl	wcstok
	.type	wcstok, @function
wcstok:
	subl	$16, %esp
	movl	$_ZZZwcstok, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcstok, .-wcstok

	.section	.rodata
_ZZZruserpass:
	.string	"ruserpass"
	.text
	.globl	ruserpass
	.type	ruserpass, @function
ruserpass:
	subl	$16, %esp
	movl	$_ZZZruserpass, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ruserpass, .-ruserpass

	.section	.rodata
_ZZZsvc_register:
	.string	"svc_register"
	.text
	.globl	svc_register
	.type	svc_register, @function
svc_register:
	subl	$16, %esp
	movl	$_ZZZsvc_register, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svc_register, .-svc_register

	.section	.rodata
_ZZZwcstol:
	.string	"wcstol"
	.text
	.globl	wcstol
	.type	wcstol, @function
wcstol:
	subl	$16, %esp
	movl	$_ZZZwcstol, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcstol, .-wcstol

	.section	.rodata
_ZZZendservent:
	.string	"endservent"
	.text
	.globl	endservent
	.type	endservent, @function
endservent:
	subl	$16, %esp
	movl	$_ZZZendservent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endservent, .-endservent

	.section	.rodata
_ZZZpthread_attr_setschedpoli:
	.string	"pthread_attr_setschedpoli"
	.text
	.globl	pthread_attr_setschedpoli
	.type	pthread_attr_setschedpoli, @function
pthread_attr_setschedpoli:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_setschedpoli, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_setschedpoli, .-pthread_attr_setschedpoli

	.section	.rodata
_ZZZvswscanf:
	.string	"vswscanf"
	.text
	.globl	vswscanf
	.type	vswscanf, @function
vswscanf:
	subl	$16, %esp
	movl	$_ZZZvswscanf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vswscanf, .-vswscanf

	.section	.rodata
_ZZZctermid:
	.string	"ctermid"
	.text
	.globl	ctermid
	.type	ctermid, @function
ctermid:
	subl	$16, %esp
	movl	$_ZZZctermid, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ctermid, .-ctermid

	.section	.rodata
_ZZZsigstack:
	.string	"sigstack"
	.text
	.globl	sigstack
	.type	sigstack, @function
sigstack:
	subl	$16, %esp
	movl	$_ZZZsigstack, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sigstack, .-sigstack

	.section	.rodata
_ZZZmkostemp:
	.string	"mkostemp"
	.text
	.globl	mkostemp
	.type	mkostemp, @function
mkostemp:
	subl	$16, %esp
	movl	$_ZZZmkostemp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkostemp, .-mkostemp

	.section	.rodata
_ZZZmkostemps:
	.string	"mkostemps"
	.text
	.globl	mkostemps
	.type	mkostemps, @function
mkostemps:
	subl	$16, %esp
	movl	$_ZZZmkostemps, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkostemps, .-mkostemps

	.section	.rodata
_ZZZgetnetgrent:
	.string	"getnetgrent"
	.text
	.globl	getnetgrent
	.type	getnetgrent, @function
getnetgrent:
	subl	$16, %esp
	movl	$_ZZZgetnetgrent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getnetgrent, .-getnetgrent

	.section	.rodata
_ZZZuser2netname:
	.string	"user2netname"
	.text
	.globl	user2netname
	.type	user2netname, @function
user2netname:
	subl	$16, %esp
	movl	$_ZZZuser2netname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	user2netname, .-user2netname

	.section	.rodata
_ZZZfmtmsg:
	.string	"fmtmsg"
	.text
	.globl	fmtmsg
	.type	fmtmsg, @function
fmtmsg:
	subl	$16, %esp
	movl	$_ZZZfmtmsg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fmtmsg, .-fmtmsg

	.section	.rodata
_ZZZqfcvt:
	.string	"qfcvt"
	.text
	.globl	qfcvt
	.type	qfcvt, @function
qfcvt:
	subl	$16, %esp
	movl	$_ZZZqfcvt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	qfcvt, .-qfcvt

	.section	.rodata
_ZZZmcheck_pedantic:
	.string	"mcheck_pedantic"
	.text
	.globl	mcheck_pedantic
	.type	mcheck_pedantic, @function
mcheck_pedantic:
	subl	$16, %esp
	movl	$_ZZZmcheck_pedantic, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mcheck_pedantic, .-mcheck_pedantic

	.section	.rodata
_ZZZmtrace:
	.string	"mtrace"
	.text
	.globl	mtrace
	.type	mtrace, @function
mtrace:
	subl	$16, %esp
	movl	$_ZZZmtrace, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mtrace, .-mtrace

	.section	.rodata
_ZZZntp_gettime:
	.string	"ntp_gettime"
	.text
	.globl	ntp_gettime
	.type	ntp_gettime, @function
ntp_gettime:
	subl	$16, %esp
	movl	$_ZZZntp_gettime, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ntp_gettime, .-ntp_gettime

	.section	.rodata
_ZZZmemmem:
	.string	"memmem"
	.text
	.globl	memmem
	.type	memmem, @function
memmem:
	subl	$16, %esp
	movl	$_ZZZmemmem, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	memmem, .-memmem

	.section	.rodata
_ZZZsync:
	.string	"sync"
	.text
	.globl	sync
	.type	sync, @function
sync:
	subl	$16, %esp
	movl	$_ZZZsync, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sync, .-sync

	.section	.rodata
_ZZZgetgrouplist:
	.string	"getgrouplist"
	.text
	.globl	getgrouplist
	.type	getgrouplist, @function
getgrouplist:
	subl	$16, %esp
	movl	$_ZZZgetgrouplist, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getgrouplist, .-getgrouplist

	.section	.rodata
_ZZZsysinfo:
	.string	"sysinfo"
	.text
	.globl	sysinfo
	.type	sysinfo, @function
sysinfo:
	subl	$16, %esp
	movl	$_ZZZsysinfo, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	sysinfo, .-sysinfo

	.section	.rodata
_ZZZsvc_getreq:
	.string	"svc_getreq"
	.text
	.globl	svc_getreq
	.type	svc_getreq, @function
svc_getreq:
	subl	$16, %esp
	movl	$_ZZZsvc_getreq, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	svc_getreq, .-svc_getreq

	.section	.rodata
_ZZZwprintf:
	.string	"wprintf"
	.text
	.globl	wprintf
	.type	wprintf, @function
wprintf:
	subl	$16, %esp
	movl	$_ZZZwprintf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wprintf, .-wprintf

	.section	.rodata
_ZZZfts_children:
	.string	"fts_children"
	.text
	.globl	fts_children
	.type	fts_children, @function
fts_children:
	subl	$16, %esp
	movl	$_ZZZfts_children, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fts_children, .-fts_children

	.section	.rodata
_ZZZstrxfrm:
	.string	"strxfrm"
	.text
	.globl	strxfrm
	.type	strxfrm, @function
strxfrm:
	subl	$16, %esp
	movl	$_ZZZstrxfrm, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strxfrm, .-strxfrm

	.section	.rodata
_ZZZgetservbyport_r:
	.string	"getservbyport_r"
	.text
	.globl	getservbyport_r
	.type	getservbyport_r, @function
getservbyport_r:
	subl	$16, %esp
	movl	$_ZZZgetservbyport_r, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getservbyport_r, .-getservbyport_r

	.section	.rodata
_ZZZmkfifo:
	.string	"mkfifo"
	.text
	.globl	mkfifo
	.type	mkfifo, @function
mkfifo:
	subl	$16, %esp
	movl	$_ZZZmkfifo, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	mkfifo, .-mkfifo

	.section	.rodata
_ZZZfaccessat:
	.string	"faccessat"
	.text
	.globl	faccessat
	.type	faccessat, @function
faccessat:
	subl	$16, %esp
	movl	$_ZZZfaccessat, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	faccessat, .-faccessat

	.section	.rodata
_ZZZsetbuf:
	.string	"setbuf"
	.text
	.globl	setbuf
	.type	setbuf, @function
setbuf:
	subl	$16, %esp
	movl	$_ZZZsetbuf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setbuf, .-setbuf

	.section	.rodata
_ZZZfwrite_unlocked:
	.string	"fwrite_unlocked"
	.text
	.globl	fwrite_unlocked
	.type	fwrite_unlocked, @function
fwrite_unlocked:
	subl	$16, %esp
	movl	$_ZZZfwrite_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fwrite_unlocked, .-fwrite_unlocked

	.section	.rodata
_ZZZstrcmp:
	.string	"strcmp"
	.text
	.globl	strcmp
	.type	strcmp, @function
strcmp:
	subl	$16, %esp
	movl	$_ZZZstrcmp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strcmp, .-strcmp

	.section	.rodata
_ZZZstrerror:
	.string	"strerror"
	.text
	.globl	strerror
	.type	strerror, @function
strerror:
	subl	$16, %esp
	movl	$_ZZZstrerror, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strerror, .-strerror

	.section	.rodata
_ZZZxdr_wrapstring:
	.string	"xdr_wrapstring"
	.text
	.globl	xdr_wrapstring
	.type	xdr_wrapstring, @function
xdr_wrapstring:
	subl	$16, %esp
	movl	$_ZZZxdr_wrapstring, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_wrapstring, .-xdr_wrapstring

	.section	.rodata
_ZZZtcgetpgrp:
	.string	"tcgetpgrp"
	.text
	.globl	tcgetpgrp
	.type	tcgetpgrp, @function
tcgetpgrp:
	subl	$16, %esp
	movl	$_ZZZtcgetpgrp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	tcgetpgrp, .-tcgetpgrp

	.section	.rodata
_ZZZdirfd:
	.string	"dirfd"
	.text
	.globl	dirfd
	.type	dirfd, @function
dirfd:
	subl	$16, %esp
	movl	$_ZZZdirfd, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	dirfd, .-dirfd

	.section	.rodata
_ZZZxdr_des_block:
	.string	"xdr_des_block"
	.text
	.globl	xdr_des_block
	.type	xdr_des_block, @function
xdr_des_block:
	subl	$16, %esp
	movl	$_ZZZxdr_des_block, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_des_block, .-xdr_des_block

	.section	.rodata
_ZZZnftw:
	.string	"nftw"
	.text
	.globl	nftw
	.type	nftw, @function
nftw:
	subl	$16, %esp
	movl	$_ZZZnftw, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	nftw, .-nftw

	.section	.rodata
_ZZZxdr_cryptkeyarg2:
	.string	"xdr_cryptkeyarg2"
	.text
	.globl	xdr_cryptkeyarg2
	.type	xdr_cryptkeyarg2, @function
xdr_cryptkeyarg2:
	subl	$16, %esp
	movl	$_ZZZxdr_cryptkeyarg2, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_cryptkeyarg2, .-xdr_cryptkeyarg2

	.section	.rodata
_ZZZxdr_callhdr:
	.string	"xdr_callhdr"
	.text
	.globl	xdr_callhdr
	.type	xdr_callhdr, @function
xdr_callhdr:
	subl	$16, %esp
	movl	$_ZZZxdr_callhdr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_callhdr, .-xdr_callhdr

	.section	.rodata
_ZZZsetpwent:
	.string	"setpwent"
	.text
	.globl	setpwent
	.type	setpwent, @function
setpwent:
	subl	$16, %esp
	movl	$_ZZZsetpwent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setpwent, .-setpwent

	.section	.rodata
_ZZZsemop:
	.string	"semop"
	.text
	.globl	semop
	.type	semop, @function
semop:
	subl	$16, %esp
	movl	$_ZZZsemop, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	semop, .-semop

	.section	.rodata
_ZZZendfsent:
	.string	"endfsent"
	.text
	.globl	endfsent
	.type	endfsent, @function
endfsent:
	subl	$16, %esp
	movl	$_ZZZendfsent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	endfsent, .-endfsent

	.section	.rodata
_ZZZwscanf:
	.string	"wscanf"
	.text
	.globl	wscanf
	.type	wscanf, @function
wscanf:
	subl	$16, %esp
	movl	$_ZZZwscanf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wscanf, .-wscanf

	.section	.rodata
_ZZZauthdes_create:
	.string	"authdes_create"
	.text
	.globl	authdes_create
	.type	authdes_create, @function
authdes_create:
	subl	$16, %esp
	movl	$_ZZZauthdes_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	authdes_create, .-authdes_create

	.section	.rodata
_ZZZppoll:
	.string	"ppoll"
	.text
	.globl	ppoll
	.type	ppoll, @function
ppoll:
	subl	$16, %esp
	movl	$_ZZZppoll, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ppoll, .-ppoll

	.section	.rodata
_ZZZfdetach:
	.string	"fdetach"
	.text
	.globl	fdetach
	.type	fdetach, @function
fdetach:
	subl	$16, %esp
	movl	$_ZZZfdetach, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fdetach, .-fdetach

	.section	.rodata
_ZZZpthread_cond_destroy:
	.string	"pthread_cond_destroy"
	.text
	.globl	pthread_cond_destroy
	.type	pthread_cond_destroy, @function
pthread_cond_destroy:
	subl	$16, %esp
	movl	$_ZZZpthread_cond_destroy, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_cond_destroy, .-pthread_cond_destroy

	.section	.rodata
_ZZZgcvt:
	.string	"gcvt"
	.text
	.globl	gcvt
	.type	gcvt, @function
gcvt:
	subl	$16, %esp
	movl	$_ZZZgcvt, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gcvt, .-gcvt

	.section	.rodata
_ZZZxdr_bytes:
	.string	"xdr_bytes"
	.text
	.globl	xdr_bytes
	.type	xdr_bytes, @function
xdr_bytes:
	subl	$16, %esp
	movl	$_ZZZxdr_bytes, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_bytes, .-xdr_bytes

	.section	.rodata
_ZZZsetpriority:
	.string	"setpriority"
	.text
	.globl	setpriority
	.type	setpriority, @function
setpriority:
	subl	$16, %esp
	movl	$_ZZZsetpriority, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setpriority, .-setpriority

	.section	.rodata
_ZZZposix_spawn_file_actions_:
	.string	"posix_spawn_file_actions_"
	.text
	.globl	posix_spawn_file_actions_
	.type	posix_spawn_file_actions_, @function
posix_spawn_file_actions_:
	subl	$16, %esp
	movl	$_ZZZposix_spawn_file_actions_, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_spawn_file_actions_, .-posix_spawn_file_actions_

	.section	.rodata
_ZZZfgetgrent:
	.string	"fgetgrent"
	.text
	.globl	fgetgrent
	.type	fgetgrent, @function
fgetgrent:
	subl	$16, %esp
	movl	$_ZZZfgetgrent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fgetgrent, .-fgetgrent

	.section	.rodata
_ZZZsetdomainname:
	.string	"setdomainname"
	.text
	.globl	setdomainname
	.type	setdomainname, @function
setdomainname:
	subl	$16, %esp
	movl	$_ZZZsetdomainname, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setdomainname, .-setdomainname

	.section	.rodata
_ZZZgetservbyport:
	.string	"getservbyport"
	.text
	.globl	getservbyport
	.type	getservbyport, @function
getservbyport:
	subl	$16, %esp
	movl	$_ZZZgetservbyport, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getservbyport, .-getservbyport

	.section	.rodata
_ZZZif_freenameindex:
	.string	"if_freenameindex"
	.text
	.globl	if_freenameindex
	.type	if_freenameindex, @function
if_freenameindex:
	subl	$16, %esp
	movl	$_ZZZif_freenameindex, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	if_freenameindex, .-if_freenameindex

	.section	.rodata
_ZZZgetnetent:
	.string	"getnetent"
	.text
	.globl	getnetent
	.type	getnetent, @function
getnetent:
	subl	$16, %esp
	movl	$_ZZZgetnetent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getnetent, .-getnetent

	.section	.rodata
_ZZZposix_fallocate:
	.string	"posix_fallocate"
	.text
	.globl	posix_fallocate
	.type	posix_fallocate, @function
posix_fallocate:
	subl	$16, %esp
	movl	$_ZZZposix_fallocate, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_fallocate, .-posix_fallocate

	.section	.rodata
_ZZZfseeko:
	.string	"fseeko"
	.text
	.globl	fseeko
	.type	fseeko, @function
fseeko:
	subl	$16, %esp
	movl	$_ZZZfseeko, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fseeko, .-fseeko

	.section	.rodata
_ZZZxdrrec_endofrecord:
	.string	"xdrrec_endofrecord"
	.text
	.globl	xdrrec_endofrecord
	.type	xdrrec_endofrecord, @function
xdrrec_endofrecord:
	subl	$16, %esp
	movl	$_ZZZxdrrec_endofrecord, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdrrec_endofrecord, .-xdrrec_endofrecord

	.section	.rodata
_ZZZinet6_opt_set_val:
	.string	"inet6_opt_set_val"
	.text
	.globl	inet6_opt_set_val
	.type	inet6_opt_set_val, @function
inet6_opt_set_val:
	subl	$16, %esp
	movl	$_ZZZinet6_opt_set_val, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_opt_set_val, .-inet6_opt_set_val

	.section	.rodata
_ZZZvfprintf:
	.string	"vfprintf"
	.text
	.globl	vfprintf
	.type	vfprintf, @function
vfprintf:
	subl	$16, %esp
	movl	$_ZZZvfprintf, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vfprintf, .-vfprintf

	.section	.rodata
_ZZZstrcoll:
	.string	"strcoll"
	.text
	.globl	strcoll
	.type	strcoll, @function
strcoll:
	subl	$16, %esp
	movl	$_ZZZstrcoll, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	strcoll, .-strcoll

	.section	.rodata
_ZZZglobfree:
	.string	"globfree"
	.text
	.globl	globfree
	.type	globfree, @function
globfree:
	subl	$16, %esp
	movl	$_ZZZglobfree, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	globfree, .-globfree

	.section	.rodata
_ZZZdelete_module:
	.string	"delete_module"
	.text
	.globl	delete_module
	.type	delete_module, @function
delete_module:
	subl	$16, %esp
	movl	$_ZZZdelete_module, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	delete_module, .-delete_module

	.section	.rodata
_ZZZbasename:
	.string	"basename"
	.text
	.globl	basename
	.type	basename, @function
basename:
	subl	$16, %esp
	movl	$_ZZZbasename, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	basename, .-basename

	.section	.rodata
_ZZZcloselog:
	.string	"closelog"
	.text
	.globl	closelog
	.type	closelog, @function
closelog:
	subl	$16, %esp
	movl	$_ZZZcloselog, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	closelog, .-closelog

	.section	.rodata
_ZZZgetopt_long_only:
	.string	"getopt_long_only"
	.text
	.globl	getopt_long_only
	.type	getopt_long_only, @function
getopt_long_only:
	subl	$16, %esp
	movl	$_ZZZgetopt_long_only, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getopt_long_only, .-getopt_long_only

	.section	.rodata
_ZZZgetpgrp:
	.string	"getpgrp"
	.text
	.globl	getpgrp
	.type	getpgrp, @function
getpgrp:
	subl	$16, %esp
	movl	$_ZZZgetpgrp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getpgrp, .-getpgrp

	.section	.rodata
_ZZZisascii:
	.string	"isascii"
	.text
	.globl	isascii
	.type	isascii, @function
isascii:
	subl	$16, %esp
	movl	$_ZZZisascii, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	isascii, .-isascii

	.section	.rodata
_ZZZwcsncmp:
	.string	"wcsncmp"
	.text
	.globl	wcsncmp
	.type	wcsncmp, @function
wcsncmp:
	subl	$16, %esp
	movl	$_ZZZwcsncmp, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcsncmp, .-wcsncmp

	.section	.rodata
_ZZZclnt_pcreateerror:
	.string	"clnt_pcreateerror"
	.text
	.globl	clnt_pcreateerror
	.type	clnt_pcreateerror, @function
clnt_pcreateerror:
	subl	$16, %esp
	movl	$_ZZZclnt_pcreateerror, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clnt_pcreateerror, .-clnt_pcreateerror

	.section	.rodata
_ZZZposix_fadvise64:
	.string	"posix_fadvise64"
	.text
	.globl	posix_fadvise64
	.type	posix_fadvise64, @function
posix_fadvise64:
	subl	$16, %esp
	movl	$_ZZZposix_fadvise64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_fadvise64, .-posix_fadvise64

	.section	.rodata
_ZZZxdr_cryptkeyarg:
	.string	"xdr_cryptkeyarg"
	.text
	.globl	xdr_cryptkeyarg
	.type	xdr_cryptkeyarg, @function
xdr_cryptkeyarg:
	subl	$16, %esp
	movl	$_ZZZxdr_cryptkeyarg, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_cryptkeyarg, .-xdr_cryptkeyarg

	.section	.rodata
_ZZZposix_fadvise64:
	.string	"posix_fadvise64"
	.text
	.globl	posix_fadvise64
	.type	posix_fadvise64, @function
posix_fadvise64:
	subl	$16, %esp
	movl	$_ZZZposix_fadvise64, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	posix_fadvise64, .-posix_fadvise64

	.section	.rodata
_ZZZsetnetgrent:
	.string	"setnetgrent"
	.text
	.globl	setnetgrent
	.type	setnetgrent, @function
setnetgrent:
	subl	$16, %esp
	movl	$_ZZZsetnetgrent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	setnetgrent, .-setnetgrent

	.section	.rodata
_ZZZgnu_dev_makedev:
	.string	"gnu_dev_makedev"
	.text
	.globl	gnu_dev_makedev
	.type	gnu_dev_makedev, @function
gnu_dev_makedev:
	subl	$16, %esp
	movl	$_ZZZgnu_dev_makedev, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	gnu_dev_makedev, .-gnu_dev_makedev

	.section	.rodata
_ZZZxdr_u_hyper:
	.string	"xdr_u_hyper"
	.text
	.globl	xdr_u_hyper
	.type	xdr_u_hyper, @function
xdr_u_hyper:
	subl	$16, %esp
	movl	$_ZZZxdr_u_hyper, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_u_hyper, .-xdr_u_hyper

	.section	.rodata
_ZZZinet6_option_find:
	.string	"inet6_option_find"
	.text
	.globl	inet6_option_find
	.type	inet6_option_find, @function
inet6_option_find:
	subl	$16, %esp
	movl	$_ZZZinet6_option_find, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	inet6_option_find, .-inet6_option_find

	.section	.rodata
_ZZZgetservent:
	.string	"getservent"
	.text
	.globl	getservent
	.type	getservent, @function
getservent:
	subl	$16, %esp
	movl	$_ZZZgetservent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	getservent, .-getservent

	.section	.rodata
_ZZZclnttcp_create:
	.string	"clnttcp_create"
	.text
	.globl	clnttcp_create
	.type	clnttcp_create, @function
clnttcp_create:
	subl	$16, %esp
	movl	$_ZZZclnttcp_create, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	clnttcp_create, .-clnttcp_create

	.section	.rodata
_ZZZwctomb:
	.string	"wctomb"
	.text
	.globl	wctomb
	.type	wctomb, @function
wctomb:
	subl	$16, %esp
	movl	$_ZZZwctomb, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wctomb, .-wctomb

	.section	.rodata
_ZZZfputs_unlocked:
	.string	"fputs_unlocked"
	.text
	.globl	fputs_unlocked
	.type	fputs_unlocked, @function
fputs_unlocked:
	subl	$16, %esp
	movl	$_ZZZfputs_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	fputs_unlocked, .-fputs_unlocked

	.section	.rodata
_ZZZsiggetmask:
	.string	"siggetmask"
	.text
	.globl	siggetmask
	.type	siggetmask, @function
siggetmask:
	subl	$16, %esp
	movl	$_ZZZsiggetmask, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	siggetmask, .-siggetmask

	.section	.rodata
_ZZZputwchar_unlocked:
	.string	"putwchar_unlocked"
	.text
	.globl	putwchar_unlocked
	.type	putwchar_unlocked, @function
putwchar_unlocked:
	subl	$16, %esp
	movl	$_ZZZputwchar_unlocked, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putwchar_unlocked, .-putwchar_unlocked

	.section	.rodata
_ZZZsemget:
	.string	"semget"
	.text
	.globl	semget
	.type	semget, @function
semget:
	subl	$16, %esp
	movl	$_ZZZsemget, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	semget, .-semget

	.section	.rodata
_ZZZputpwent:
	.string	"putpwent"
	.text
	.globl	putpwent
	.type	putpwent, @function
putpwent:
	subl	$16, %esp
	movl	$_ZZZputpwent, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	putpwent, .-putpwent

	.section	.rodata
_ZZZxdr_accepted_reply:
	.string	"xdr_accepted_reply"
	.text
	.globl	xdr_accepted_reply
	.type	xdr_accepted_reply, @function
xdr_accepted_reply:
	subl	$16, %esp
	movl	$_ZZZxdr_accepted_reply, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	xdr_accepted_reply, .-xdr_accepted_reply

	.section	.rodata
_ZZZwcsstr:
	.string	"wcsstr"
	.text
	.globl	wcsstr
	.type	wcsstr, @function
wcsstr:
	subl	$16, %esp
	movl	$_ZZZwcsstr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcsstr, .-wcsstr

	.section	.rodata
_ZZZfree:
	.string	"free"
	.text
	.globl	free
	.type	free, @function
free:
	subl	$16, %esp
	movl	$_ZZZfree, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	free, .-free

	.section	.rodata
_ZZZispunct:
	.string	"ispunct"
	.text
	.globl	ispunct
	.type	ispunct, @function
ispunct:
	subl	$16, %esp
	movl	$_ZZZispunct, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	ispunct, .-ispunct

	.section	.rodata
_ZZZwcsrchr:
	.string	"wcsrchr"
	.text
	.globl	wcsrchr
	.type	wcsrchr, @function
wcsrchr:
	subl	$16, %esp
	movl	$_ZZZwcsrchr, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	wcsrchr, .-wcsrchr

	.section	.rodata
_ZZZpthread_attr_getinheritsc:
	.string	"pthread_attr_getinheritsc"
	.text
	.globl	pthread_attr_getinheritsc
	.type	pthread_attr_getinheritsc, @function
pthread_attr_getinheritsc:
	subl	$16, %esp
	movl	$_ZZZpthread_attr_getinheritsc, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	pthread_attr_getinheritsc, .-pthread_attr_getinheritsc

	.section	.rodata
_ZZZkey_decryptsession:
	.string	"key_decryptsession"
	.text
	.globl	key_decryptsession
	.type	key_decryptsession, @function
key_decryptsession:
	subl	$16, %esp
	movl	$_ZZZkey_decryptsession, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	key_decryptsession, .-key_decryptsession

	.section	.rodata
_ZZZvwarn:
	.string	"vwarn"
	.text
	.globl	vwarn
	.type	vwarn, @function
vwarn:
	subl	$16, %esp
	movl	$_ZZZvwarn, %eax
	movl	%eax, 4(%esp)
	movl	$-1, (%esp)
	call	dlsym
	addl	$16,%esp
	jmp	*%eax
	.size	vwarn, .-vwarn

