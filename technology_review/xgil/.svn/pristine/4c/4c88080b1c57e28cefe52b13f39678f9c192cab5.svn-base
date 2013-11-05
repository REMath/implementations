# 1 "pc_keyb.c"
 
















# 1 "/usr/src/linux/include/linux/config.h" 1



# 1 "/usr/src/linux/include/linux/autoconf.h" 1
 




 




 



















 






 



























 





 































 





























 





 












 


















































 







 




 









 























































































 









 





 












 




 




 




 




 















 









 


























 





 




 
























 










 








 




































 





 











































 




 



# 4 "/usr/src/linux/include/linux/config.h" 2



# 18 "pc_keyb.c" 2


# 1 "/usr/src/linux/include/asm/spinlock.h" 1









 





  typedef struct { } spinlock_t;
  


















# 80 "/usr/src/linux/include/asm/spinlock.h"


 












  typedef struct { } rwlock_t;
  























# 253 "/usr/src/linux/include/asm/spinlock.h"


# 20 "pc_keyb.c" 2

# 1 "/usr/src/linux/include/linux/sched.h" 1



# 1 "/usr/src/linux/include/asm/param.h" 1




















# 4 "/usr/src/linux/include/linux/sched.h" 2


extern unsigned long global_event;

# 1 "/usr/src/linux/include/linux/binfmts.h" 1



# 1 "/usr/src/linux/include/linux/ptrace.h" 1


 
 

 

















# 1 "/usr/src/linux/include/asm/ptrace.h" 1






















 


struct pt_regs {
	long ebx;
	long ecx;
	long edx;
	long esi;
	long edi;
	long ebp;
	long eax;
	int  xds;
	int  xes;
	long orig_eax;
	long eip;
	int  xcs;
	long eflags;
	long esp;
	int  xss;
};

 








extern void show_regs(struct pt_regs *);



# 24 "/usr/src/linux/include/linux/ptrace.h" 2



# 4 "/usr/src/linux/include/linux/binfmts.h" 2

# 1 "/usr/src/linux/include/linux/capability.h" 1
 









 




# 1 "/usr/src/linux/include/linux/types.h" 1



# 1 "/usr/src/linux/include/linux/posix_types.h" 1



# 1 "/usr/src/linux/include/linux/stddef.h" 1














# 4 "/usr/src/linux/include/linux/posix_types.h" 2


 










 


















typedef struct {
	unsigned long fds_bits [(1024 / (8 * sizeof(unsigned long)) ) ];
} __kernel_fd_set;

 
typedef void (*__kernel_sighandler_t)(int);

 
typedef int __kernel_key_t;

# 1 "/usr/src/linux/include/asm/posix_types.h" 1



 





typedef unsigned short	__kernel_dev_t;
typedef unsigned long	__kernel_ino_t;
typedef unsigned short	__kernel_mode_t;
typedef unsigned short	__kernel_nlink_t;
typedef long		__kernel_off_t;
typedef int		__kernel_pid_t;
typedef unsigned short	__kernel_ipc_pid_t;
typedef unsigned short	__kernel_uid_t;
typedef unsigned short	__kernel_gid_t;
typedef unsigned int	__kernel_size_t;
typedef int		__kernel_ssize_t;
typedef int		__kernel_ptrdiff_t;
typedef long		__kernel_time_t;
typedef long		__kernel_suseconds_t;
typedef long		__kernel_clock_t;
typedef int		__kernel_daddr_t;
typedef char *		__kernel_caddr_t;


typedef long long	__kernel_loff_t;


typedef struct {

	int	val[2];



} __kernel_fsid_t;























# 70 "/usr/src/linux/include/asm/posix_types.h"




# 46 "/usr/src/linux/include/linux/posix_types.h" 2



# 4 "/usr/src/linux/include/linux/types.h" 2

# 1 "/usr/src/linux/include/asm/types.h" 1



typedef unsigned short umode_t;

 




typedef __signed__ char __s8;
typedef unsigned char __u8;

typedef __signed__ short __s16;
typedef unsigned short __u16;

typedef __signed__ int __s32;
typedef unsigned int __u32;


typedef __signed__ long long __s64;
typedef unsigned long long __u64;


 




typedef signed char s8;
typedef unsigned char u8;

typedef signed short s16;
typedef unsigned short u16;

typedef signed int s32;
typedef unsigned int u32;

typedef signed long long s64;
typedef unsigned long long u64;






# 5 "/usr/src/linux/include/linux/types.h" 2




typedef __kernel_fd_set		fd_set;
typedef __kernel_dev_t		dev_t;
typedef __kernel_ino_t		ino_t;
typedef __kernel_mode_t		mode_t;
typedef __kernel_nlink_t	nlink_t;
typedef __kernel_off_t		off_t;
typedef __kernel_pid_t		pid_t;
typedef __kernel_uid_t		uid_t;
typedef __kernel_gid_t		gid_t;
typedef __kernel_daddr_t	daddr_t;
typedef __kernel_key_t		key_t;
typedef __kernel_suseconds_t	suseconds_t;


typedef __kernel_loff_t		loff_t;


 





typedef __kernel_size_t		size_t;




typedef __kernel_ssize_t	ssize_t;




typedef __kernel_ptrdiff_t	ptrdiff_t;




typedef __kernel_time_t		time_t;




typedef __kernel_clock_t	clock_t;




typedef __kernel_caddr_t	caddr_t;


 
typedef unsigned char		u_char;
typedef unsigned short		u_short;
typedef unsigned int		u_int;
typedef unsigned long		u_long;

 
typedef unsigned char		unchar;
typedef unsigned short		ushort;
typedef unsigned int		uint;
typedef unsigned long		ulong;




typedef		__u8		u_int8_t;
typedef		__s8		int8_t;
typedef		__u16		u_int16_t;
typedef		__s16		int16_t;
typedef		__u32		u_int32_t;
typedef		__s32		int32_t;



typedef		__u8		uint8_t;
typedef		__u16		uint16_t;
typedef		__u32		uint32_t;


typedef		__u64		uint64_t;
typedef		__u64		u_int64_t;
typedef		__s64		int64_t;




 




struct ustat {
	__kernel_daddr_t	f_tfree;
	__kernel_ino_t		f_tinode;
	char			f_fname[6];
	char			f_fpack[6];
};


# 16 "/usr/src/linux/include/linux/capability.h" 2


 




 




 


typedef struct __user_cap_header_struct {
	__u32 version;
	int pid;
} *cap_user_header_t;
 
typedef struct __user_cap_data_struct {
        __u32 effective;
        __u32 permitted;
        __u32 inheritable;
} *cap_user_data_t;
  


 









typedef __u32 kernel_cap_t;


  






 



 





 





 




    
 





 








 



 





 
 
 



 
 




 



 




 



 



 



 
 
 
 
 

 
 
 
 
 
 



 
 



 
 




 



 
 


 



 



 



 



 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
 
 
 
 
 
 

 
 
 
 
 
 
 
 
 

 



 



 

 





 
 
 
 

 
 
 
 



 
 
 



 
 




 


extern kernel_cap_t cap_bset;

 


 






















static inline kernel_cap_t cap_combine(kernel_cap_t a, kernel_cap_t b)
{
     kernel_cap_t dest;
     ( dest )  = ( a )  | ( b ) ;
     return dest;
}

static inline kernel_cap_t cap_intersect(kernel_cap_t a, kernel_cap_t b)
{
     kernel_cap_t dest;
     ( dest )  = ( a )  & ( b ) ;     // AMBIGUOUS
     return dest;
}

static inline kernel_cap_t cap_drop(kernel_cap_t a, kernel_cap_t drop)
{
     kernel_cap_t dest;
     ( dest )  = ( a )  & ~( drop ) ;     // AMBIGUOUS
     return dest;
}

static inline kernel_cap_t cap_invert(kernel_cap_t c)
{
     kernel_cap_t dest;
     ( dest )  = ~( c ) ;
     return dest;
}













# 5 "/usr/src/linux/include/linux/binfmts.h" 2


 








 


struct linux_binprm{
	char buf[128];
	unsigned long page[32 ];
	unsigned long p;
	int sh_bang;
	int java;		 
	struct dentry * dentry;
	int e_uid, e_gid;
	kernel_cap_t cap_inheritable, cap_permitted, cap_effective;
	int argc, envc;
	char * filename;	 
	unsigned long loader, exec;
};

 



struct linux_binfmt {
	struct linux_binfmt * next;
	struct module *module;
	int (*load_binary)(struct linux_binprm *, struct  pt_regs * regs);
	int (*load_shlib)(int fd);
	int (*core_dump)(long signr, struct pt_regs * regs);
};

extern int register_binfmt(struct linux_binfmt *);
extern int unregister_binfmt(struct linux_binfmt *);

extern int read_exec(struct dentry *, unsigned long offset,
	char * addr, unsigned long count, int to_kmem);

extern int open_dentry(struct dentry *, int mode);

extern int init_elf_binfmt(void);
extern int init_elf32_binfmt(void);
extern int init_irix_binfmt(void);
extern int init_aout_binfmt(void);
extern int init_aout32_binfmt(void);
extern int init_script_binfmt(void);
extern int init_java_binfmt(void);
extern int init_em86_binfmt(void);
extern int init_misc_binfmt(void);

extern int prepare_binprm(struct linux_binprm *);
extern void remove_arg_zero(struct linux_binprm *);
extern int search_binary_handler(struct linux_binprm *,struct pt_regs *);
extern int flush_old_exec(struct linux_binprm * bprm);
extern unsigned long setup_arg_pages(unsigned long p, struct linux_binprm * bprm);
extern unsigned long copy_strings(int argc,char ** argv,unsigned long *page,
		unsigned long p, int from_kmem);

extern void compute_creds(struct linux_binprm *binprm);

 




# 8 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/linux/personality.h" 1



# 1 "/usr/src/linux/include/linux/linkage.h" 1









































# 52 "/usr/src/linux/include/linux/linkage.h"



# 4 "/usr/src/linux/include/linux/personality.h" 2




 




 

















 
typedef void (*lcall7_func)(struct pt_regs *);


 




struct exec_domain {
	const char *name;
	lcall7_func handler;
	unsigned char pers_low, pers_high;
	unsigned long * signal_map;
	unsigned long * signal_invmap;
	struct module * module;
	struct exec_domain *next;
};

extern struct exec_domain default_exec_domain;

extern struct exec_domain *lookup_exec_domain(unsigned long personality);
extern int register_exec_domain(struct exec_domain *it);
extern int unregister_exec_domain(struct exec_domain *it);
  __attribute__((regparm(0)))  int sys_personality(unsigned long personality);


# 9 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/linux/tasks.h" 1



 


 












 





# 10 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/linux/kernel.h" 1



 





# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stdarg.h" 1 3
 





























































 






typedef void *__gnuc_va_list;



 



 














void va_end (__gnuc_va_list);		 


 



 












 






















 
 













# 168 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stdarg.h" 3


 




 

 

 

typedef __gnuc_va_list va_list;
























# 10 "/usr/src/linux/include/linux/kernel.h" 2



 
 




























extern void math_error(void);
extern struct notifier_block *panic_notifier_list;
  void panic(const char * fmt, ...)
	__attribute__ ((noreturn,  format (printf, 1, 2)));
  void do_exit(long error_code)
	__attribute__((noreturn)) ;
extern unsigned long simple_strtoul(const char *,char **,unsigned int);
extern long simple_strtol(const char *,char **,unsigned int);
extern int sprintf(char * buf, const char * fmt, ...);
extern int vsprintf(char *buf, const char *, va_list);

extern int session_of_pgrp(int pgrp);

  __attribute__((regparm(0)))  int printk(const char * fmt, ...)
	__attribute__ ((format (printf, 1, 2)));












 












struct sysinfo {
	long uptime;			 
	unsigned long loads[3];		 
	unsigned long totalram;		 
	unsigned long freeram;		 
	unsigned long sharedram;	 
	unsigned long bufferram;	 
	unsigned long totalswap;	 
	unsigned long freeswap;		 
	unsigned short procs;		 
	char _f[22];			 
};


# 11 "/usr/src/linux/include/linux/sched.h" 2


# 1 "/usr/src/linux/include/linux/times.h" 1



struct tms {
	clock_t tms_utime;
	clock_t tms_stime;
	clock_t tms_cutime;
	clock_t tms_cstime;
};


# 13 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/linux/timex.h" 1
 















 




































 












 















 

























 

























 


# 1 "/usr/src/linux/include/asm/timex.h" 1
 








# 1 "/usr/src/linux/include/asm/msr.h" 1
 





























# 10 "/usr/src/linux/include/asm/timex.h" 2








 













typedef unsigned long cycles_t;

extern cycles_t cacheflush_time;

static inline cycles_t get_cycles (void)
{



	unsigned long eax, edx;

	__asm__ __volatile__("rdtsc" : "=a" ( eax ), "=d" ( edx )) ;
	return eax;

}


# 138 "/usr/src/linux/include/linux/timex.h" 2

 


# 1 "/usr/src/linux/include/linux/time.h" 1








struct timespec {
	time_t	tv_sec;		 
	long	tv_nsec;	 
};


 













static __inline__ unsigned long
timespec_to_jiffies(struct timespec *value)
{
	unsigned long sec = value->tv_sec;
	long nsec = value->tv_nsec;

	if (sec >= (((~0UL >> 1)-1)  / 100 ))
		return ((~0UL >> 1)-1) ;
	nsec += 1000000000L / 100  - 1;
	nsec /= 1000000000L / 100 ;
	return 100  * sec + nsec;
}

static __inline__ void
jiffies_to_timespec(unsigned long jiffies, struct timespec *value)
{
	value->tv_nsec = (jiffies % 100 ) * (1000000000L / 100 );
	value->tv_sec = jiffies / 100 ;
}
 
struct timeval {
	time_t		tv_sec;		 
	suseconds_t	tv_usec;	 
};

struct timezone {
	int	tz_minuteswest;	 
	int	tz_dsttime;	 
};




extern void do_gettimeofday(struct timeval *tv);
extern void do_settimeofday(struct timeval *tv);
extern void get_fast_time(struct timeval *tv);
extern void (*do_get_fast_time)(struct timeval *);








 







struct  itimerspec {
        struct  timespec it_interval;     
        struct  timespec it_value;        
};

struct	itimerval {
	struct	timeval it_interval;	 
	struct	timeval it_value;	 
};


# 142 "/usr/src/linux/include/linux/timex.h" 2


 


 



struct timex {
	unsigned int modes;	 
	long offset;		 
	long freq;		 
	long maxerror;		 
	long esterror;		 
	int status;		 
	long constant;		 
	long precision;		 
	long tolerance;		 


	struct timeval time;	 
	long tick;		 

	long ppsfreq;            
	long jitter;             
	int shift;               
	long stabil;             
	long jitcnt;             
	long calcnt;             
	long errcnt;             
	long stbcnt;             

	int  :32; int  :32; int  :32; int  :32;
	int  :32; int  :32; int  :32; int  :32;
	int  :32; int  :32; int  :32; int  :32;
};

 











 










 






















 











 




extern long tick;                       
extern int tickadj;			 

 


extern int time_state;		 
extern int time_status;		 
extern long time_offset;	 
extern long time_constant;	 
extern long time_tolerance;	 
extern long time_precision;	 
extern long time_maxerror;	 
extern long time_esterror;	 

extern long time_phase;		 
extern long time_freq;		 
extern long time_adj;		 
extern long time_reftime;	 

extern long time_adjust;	 

 
extern long pps_offset;		 
extern long pps_jitter;		 
extern long pps_freq;		 
extern long pps_stabil;		 
extern long pps_valid;		 

 
extern int pps_shift;		 
extern long pps_jitcnt;		 
extern long pps_calcnt;		 
extern long pps_errcnt;		 
extern long pps_stbcnt;		 




# 14 "/usr/src/linux/include/linux/sched.h" 2


# 1 "/usr/src/linux/include/asm/system.h" 1




# 1 "/usr/src/linux/include/asm/segment.h" 1










# 5 "/usr/src/linux/include/asm/system.h" 2




struct task_struct;	 
extern void  __switch_to(struct task_struct *prev, struct task_struct *next)  __attribute__((regparm(3))) ;


# 31 "/usr/src/linux/include/asm/system.h"


# 43 "/usr/src/linux/include/asm/system.h"


# 56 "/usr/src/linux/include/asm/system.h"




static inline unsigned long _get_base(char * addr)
{
	unsigned long __base;
	__asm__("movb %3,%%dh\n\t"
		"movb %2,%%dl\n\t"
		"shll $16,%%edx\n\t"
		"movw %1,%%dx"
		:"=&d" (__base)
		:"m" (*((addr)+2)),
		 "m" (*((addr)+4)),
		 "m" (*((addr)+7)));
	return __base;
}



 




# 96 "/usr/src/linux/include/asm/system.h"

 
















static inline unsigned long get_limit(unsigned long segment)
{
	unsigned long __limit;
	__asm__("lsll %1,%0"
		:"=r" (__limit):"r" (segment));
	return __limit+1;
}






struct __xchg_dummy { unsigned long a[100]; };


 


static inline unsigned long __xchg(unsigned long x, void * ptr, int size)
{
	switch (size) {
		case 1:
			__asm__("xchgb %b0,%1"
				:"=q" (x)
				:"m" (* ((struct __xchg_dummy *)( ptr )) ), "0" (x)
				:"memory");
			break;
		case 2:
			__asm__("xchgw %w0,%1"
				:"=r" (x)
				:"m" (* ((struct __xchg_dummy *)( ptr )) ), "0" (x)
				:"memory");
			break;
		case 4:
			__asm__("xchgl %0,%1"
				:"=r" (x)
				:"m" (* ((struct __xchg_dummy *)( ptr )) ), "0" (x)
				:"memory");
			break;
	}
	return x;
}

 

















 








# 196 "/usr/src/linux/include/asm/system.h"









 



void disable_hlt(void);
void enable_hlt(void);


# 16 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/asm/semaphore.h" 1





 

























# 1 "/usr/src/linux/include/asm/atomic.h" 1



 










 









typedef struct { int counter; } atomic_t;







static __inline__ void atomic_add(int i, volatile atomic_t *v)
{
	__asm__ __volatile__(
		""  "addl %1,%0"
		:"=m" ((*(volatile struct { int a[100]; } *) v ) )
		:"ir" (i), "m" ((*(volatile struct { int a[100]; } *) v ) ));
}

static __inline__ void atomic_sub(int i, volatile atomic_t *v)
{
	__asm__ __volatile__(
		""  "subl %1,%0"
		:"=m" ((*(volatile struct { int a[100]; } *) v ) )
		:"ir" (i), "m" ((*(volatile struct { int a[100]; } *) v ) ));
}

static __inline__ void atomic_inc(volatile atomic_t *v)
{
	__asm__ __volatile__(
		""  "incl %0"
		:"=m" ((*(volatile struct { int a[100]; } *) v ) )
		:"m" ((*(volatile struct { int a[100]; } *) v ) ));
}

static __inline__ void atomic_dec(volatile atomic_t *v)
{
	__asm__ __volatile__(
		""  "decl %0"
		:"=m" ((*(volatile struct { int a[100]; } *) v ) )
		:"m" ((*(volatile struct { int a[100]; } *) v ) ));
}

static __inline__ int atomic_dec_and_test(volatile atomic_t *v)
{
	unsigned char c;

	__asm__ __volatile__(
		""  "decl %0; sete %1"
		:"=m" ((*(volatile struct { int a[100]; } *) v ) ), "=qm" (c)
		:"m" ((*(volatile struct { int a[100]; } *) v ) ));
	return c != 0;
}

extern __inline__ int atomic_inc_and_test_greater_zero(volatile atomic_t *v)
{
	unsigned char c;

	__asm__ __volatile__(
		""  "incl %0; setg %1"
		:"=m" ((*(volatile struct { int a[100]; } *) v ) ), "=qm" (c)
		:"m" ((*(volatile struct { int a[100]; } *) v ) ));
	return c;  
}

 









# 32 "/usr/src/linux/include/asm/semaphore.h" 2



struct semaphore {
	atomic_t count;
	int waking;
	struct wait_queue * wait;
};




  __attribute__((regparm(0)))  void __down_failed(void  );
  __attribute__((regparm(0)))  int  __down_failed_interruptible(void   );
  __attribute__((regparm(0)))  int  __down_failed_trylock(void   );
  __attribute__((regparm(0)))  void __up_wakeup(void  );

  __attribute__((regparm(0)))  void __down(struct semaphore * sem);
  __attribute__((regparm(0)))  int  __down_interruptible(struct semaphore * sem);
  __attribute__((regparm(0)))  int  __down_trylock(struct semaphore * sem);
  __attribute__((regparm(0)))  void __up(struct semaphore * sem);

extern spinlock_t semaphore_wake_lock;



 




extern inline void down(struct semaphore * sem)
{
	__asm__ __volatile__(
		"# atomic down operation\n\t"



		"decl (%0)\n\t"      
		"js 2f\n"
		"1:\n"
		".section .text.lock,\"ax\"\n"
		"2:\tcall __down_failed\n\t"
		"jmp 1b\n"
		".previous"
		: 
		:"c" (sem)
		:"memory");
}

extern inline int down_interruptible(struct semaphore * sem)
{
	int result;

	__asm__ __volatile__(
		"# atomic interruptible down operation\n\t"



		"decl (%1)\n\t"      
		"js 2f\n\t"
		"xorl %0,%0\n"
		"1:\n"
		".section .text.lock,\"ax\"\n"
		"2:\tcall __down_failed_interruptible\n\t"
		"jmp 1b\n"
		".previous"
		:"=a" (result)
		:"c" (sem)
		:"memory");
	return result;
}

extern inline int down_trylock(struct semaphore * sem)
{
	int result;

	__asm__ __volatile__(
		"# atomic interruptible down operation\n\t"



		"decl (%1)\n\t"      
		"js 2f\n\t"
		"xorl %0,%0\n"
		"1:\n"
		".section .text.lock,\"ax\"\n"
		"2:\tcall __down_failed_trylock\n\t"
		"jmp 1b\n"
		".previous"
		:"=a" (result)
		:"c" (sem)
		:"memory");
	return result;
}

 





extern inline void up(struct semaphore * sem)
{
	__asm__ __volatile__(
		"# atomic up operation\n\t"



		"incl (%0)\n\t"      
		"jle 2f\n"
		"1:\n"
		".section .text.lock,\"ax\"\n"
		"2:\tcall __up_wakeup\n\t"
		"jmp 1b\n"
		".previous"
		: 
		:"c" (sem)
		:"memory");
}


# 17 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/asm/page.h" 1



 













 


typedef struct { unsigned long pte; } pte_t;
typedef struct { unsigned long pmd; } pmd_t;
typedef struct { unsigned long pgd; } pgd_t;
typedef struct { unsigned long pgprot; } pgprot_t;











# 55 "/usr/src/linux/include/asm/page.h"



 


 





















# 1 "/usr/src/linux/include/asm/page_offset.h" 1








# 83 "/usr/src/linux/include/asm/page.h" 2












# 18 "/usr/src/linux/include/linux/sched.h" 2


# 1 "/usr/src/linux/include/linux/smp.h" 1



 




# 71 "/usr/src/linux/include/linux/smp.h"


 


 










# 20 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/linux/tty.h" 1



 



 






		 




# 1 "/usr/src/linux/include/linux/fs.h" 1



 






# 1 "/usr/src/linux/include/linux/limits.h" 1



















# 11 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/wait.h" 1












struct wait_queue {
	struct task_struct * task;
	struct wait_queue * next;
};



static inline void init_waitqueue(struct wait_queue **q)
{
	*q = ((struct wait_queue *)(( q )-1)) ;   // AMBIGUOUS
}

static inline int waitqueue_active(struct wait_queue **q)
{
	struct wait_queue *head = *q;
	return head && head != ((struct wait_queue *)(( q )-1)) ;   // AMBIGUOUS
}




# 12 "/usr/src/linux/include/linux/fs.h" 2


# 1 "/usr/src/linux/include/linux/vfs.h" 1



# 1 "/usr/src/linux/include/asm/statfs.h" 1







typedef __kernel_fsid_t	fsid_t;



struct statfs {
	long f_type;
	long f_bsize;
	long f_blocks;
	long f_bfree;
	long f_bavail;
	long f_files;
	long f_ffree;
	__kernel_fsid_t f_fsid;
	long f_namelen;
	long f_spare[6];
};


# 4 "/usr/src/linux/include/linux/vfs.h" 2



# 14 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/net.h" 1
 



















# 1 "/usr/src/linux/include/linux/socket.h" 1





# 1 "/usr/src/linux/include/asm/socket.h" 1



# 1 "/usr/src/linux/include/asm/sockios.h" 1



 








# 4 "/usr/src/linux/include/asm/socket.h" 2


 
















 







 






 



 

 






					 
					 
					 
					 



# 6 "/usr/src/linux/include/linux/socket.h" 2

# 1 "/usr/src/linux/include/linux/sockios.h" 1
 





















 




 











































 
		     




 




 




 




 

 





 


 


 


# 7 "/usr/src/linux/include/linux/socket.h" 2

# 1 "/usr/src/linux/include/linux/uio.h" 1





 









 


struct iovec
{
	void *iov_base;		 
	__kernel_size_t iov_len;  
};

 


 









# 8 "/usr/src/linux/include/linux/socket.h" 2



typedef unsigned short	sa_family_t;

 


 
struct sockaddr {
	sa_family_t	sa_family;	 
	char		sa_data[14];	 
};

struct linger {
	int		l_onoff;	 
	int		l_linger;	 
};

 




 
struct msghdr {
	void	*	msg_name;	 
	int		msg_namelen;	 
	struct iovec *	msg_iov;	 
	__kernel_size_t	msg_iovlen;	 
	void 	*	msg_control;	 
	__kernel_size_t	msg_controllen;	 
	unsigned	msg_flags;
};

 





struct cmsghdr {
	__kernel_size_t	cmsg_len;	 
        int		cmsg_level;	 
        int		cmsg_type;	 
};

 


















 


 











 











 
extern __inline__  struct cmsghdr * __cmsg_nxthdr(void *__ctl, __kernel_size_t __size,
					       struct cmsghdr *__cmsg)
{
	struct cmsghdr * __ptr;

	__ptr = (struct cmsghdr*)(((unsigned char *) __cmsg) +  ( (( __cmsg->cmsg_len )+sizeof(long)-1) & ~(sizeof(long)-1) ) );
	if ((unsigned long)((char*)(__ptr+1) - (char *) __ctl) > __size)
		return (struct cmsghdr*)0;

	return __ptr;
}

extern __inline__  struct cmsghdr * cmsg_nxthdr (struct msghdr *__msg, struct cmsghdr *__cmsg)
{
	return __cmsg_nxthdr(__msg->msg_control, __msg->msg_controllen, __cmsg);
}

 





struct ucred {
	__u32	pid;
	__u32	uid;
	__u32	gid;
};


 



























 




























 


 


 























 

 

















 


 





extern int memcpy_fromiovec(unsigned char *kdata, struct iovec *iov, int len);
extern int memcpy_fromiovecend(unsigned char *kdata, struct iovec *iov, 
				int offset, int len);
extern int csum_partial_copy_fromiovecend(unsigned char *kdata, 
					  struct iovec *iov, 
					  int offset, 
					  unsigned int len, int *csump);

extern int verify_iovec(struct msghdr *m, struct iovec *iov, char *address, int mode);
extern int memcpy_toiovec(struct iovec *v, unsigned char *kdata, int len);
extern void memcpy_tokerneliovec(struct iovec *iov, unsigned char *kdata, int len);
extern int move_addr_to_user(void *kaddr, int klen, void *uaddr, int *ulen);
extern int move_addr_to_kernel(void *uaddr, int ulen, void *kaddr);
extern int put_cmsg(struct msghdr*, int level, int type, int len, void *data);



# 279 "/usr/src/linux/include/linux/socket.h"


# 21 "/usr/src/linux/include/linux/net.h" 2


struct poll_table_struct;























typedef enum {
  SS_FREE = 0,				 
  SS_UNCONNECTED,			 
  SS_CONNECTING,			 
  SS_CONNECTED,				 
  SS_DISCONNECTING			 
} socket_state;







struct socket
{
	socket_state		state;

	unsigned long		flags;
	struct proto_ops	*ops;
	struct inode		*inode;
	struct fasync_struct	*fasync_list;	 
	struct file		*file;		 
	struct sock		*sk;
	struct wait_queue	*wait;

	short			type;
	unsigned char		passcred;
	unsigned char		tli;
};



struct scm_cookie;

struct proto_ops {
  int	family;

  int	(*dup)		(struct socket *newsock, struct socket *oldsock);
  int	(*release)	(struct socket *sock, struct socket *peer);
  int	(*bind)		(struct socket *sock, struct sockaddr *umyaddr,
			 int sockaddr_len);
  int	(*connect)	(struct socket *sock, struct sockaddr *uservaddr,
			 int sockaddr_len, int flags);
  int	(*socketpair)	(struct socket *sock1, struct socket *sock2);
  int	(*accept)	(struct socket *sock, struct socket *newsock,
			 int flags);
  int	(*getname)	(struct socket *sock, struct sockaddr *uaddr,
			 int *usockaddr_len, int peer);
  unsigned int (*poll)	(struct file *file, struct socket *sock, struct poll_table_struct *wait);
  int	(*ioctl)	(struct socket *sock, unsigned int cmd,
			 unsigned long arg);
  int	(*listen)	(struct socket *sock, int len);
  int	(*shutdown)	(struct socket *sock, int flags);
  int	(*setsockopt)	(struct socket *sock, int level, int optname,
			 char *optval, int optlen);
  int	(*getsockopt)	(struct socket *sock, int level, int optname,
			 char *optval, int *optlen);
  int	(*fcntl)	(struct socket *sock, unsigned int cmd,
			 unsigned long arg);	
  int   (*sendmsg)	(struct socket *sock, struct msghdr *m, int total_len, struct scm_cookie *scm);
  int   (*recvmsg)	(struct socket *sock, struct msghdr *m, int total_len, int flags, struct scm_cookie *scm);
};

struct net_proto_family 
{
	int	family;
	int	(*create)(struct socket *sock, int protocol);
	 

	short	authentication;
	short	encryption;
	short	encrypt_net;
};

struct net_proto 
{
	const char *name;		 
	void (*init_func)(struct net_proto *);	 
};

extern struct net_proto_family *net_families[];
extern int	sock_wake_async(struct socket *sk, int how);
extern int	sock_register(struct net_proto_family *fam);
extern int	sock_unregister(int family);
extern struct socket *sock_alloc(void);
extern int	sock_create(int family, int type, int proto, struct socket **);
extern void	sock_release(struct socket *);
extern int   	sock_sendmsg(struct socket *, struct msghdr *m, int len);
extern int	sock_recvmsg(struct socket *, struct msghdr *m, int len, int flags);
extern int	sock_readv_writev(int type, struct inode * inode, struct file * file,
				  const struct iovec * iov, long count, long size);

extern int	net_ratelimit(void);
extern unsigned long net_random(void);
extern void net_srandom(unsigned long);



# 15 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/kdev_t.h" 1



 























































 






typedef unsigned short kdev_t;








extern char * kdevname(kdev_t);	 

 




static inline unsigned int kdev_t_to_nr(kdev_t dev) {
   return (((unsigned int) (( dev ) >> 8 )) <<8) | ((unsigned int) (( dev ) & ((1U << 8 ) - 1) )) ;   // AMBIGUOUS
}

static inline kdev_t to_kdev_t(int dev)
{
	int major, minor;








	major = (dev >> 8);
	minor = (dev & 0xff);

	return ((( major ) << 8 ) | (  minor )) ;
}

# 113 "/usr/src/linux/include/linux/kdev_t.h"


# 16 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/ioctl.h" 1



# 1 "/usr/src/linux/include/asm/ioctl.h" 1
 







 









 






















 












 





 





 








# 4 "/usr/src/linux/include/linux/ioctl.h" 2




# 17 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/list.h" 1





 









struct list_head {
	struct list_head *next, *prev;
};








 





static __inline__ void __list_add(struct list_head * new,
	struct list_head * prev,
	struct list_head * next)
{
	next->prev = new;
	new->next = next;
	new->prev = prev;
	prev->next = new;
}

 


static __inline__ void list_add(struct list_head *new, struct list_head *head)
{
	__list_add(new, head, head->next);
}

 






static __inline__ void __list_del(struct list_head * prev,
				  struct list_head * next)
{
	next->prev = prev;
	prev->next = next;
}

static __inline__ void list_del(struct list_head *entry)
{
	__list_del(entry->prev, entry->next);
}

static __inline__ int list_empty(struct list_head *head)
{
	return head->next == head;
}

 


static __inline__ void list_splice(struct list_head *list, struct list_head *head)
{
	struct list_head *first = list->next;

	if (first != list) {
		struct list_head *last = list->prev;
		struct list_head *at = head->next;

		first->prev = head;
		head->next = first;

		last->next = at;
		at->prev = last;
	}
}







# 18 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/dcache.h" 1





 












 



struct qstr {
	const unsigned char * name;
	unsigned int len;
	unsigned int hash;
};

 


 
static __inline__ unsigned long partial_name_hash(unsigned long c, unsigned long prevhash)
{
	prevhash = (prevhash << 4) | (prevhash >> (8*sizeof(unsigned long)-4));
	return prevhash ^ c;
}

 
static __inline__ unsigned long end_name_hash(unsigned long hash)
{
	if (sizeof(hash) > sizeof(unsigned int))
		hash += hash >> 4*sizeof(hash);
	return (unsigned int) hash;
}

 
static __inline__ unsigned int full_name_hash(const unsigned char * name, unsigned int len)
{
	unsigned long hash = 0 ;
	while (len--)
		hash = partial_name_hash(*name++, hash);
	return end_name_hash(hash);
}



struct dentry {
	int d_count;
	unsigned int d_flags;
	struct inode  * d_inode;	 
	struct dentry * d_parent;	 
	struct dentry * d_mounts;	 
	struct dentry * d_covers;
	struct list_head d_hash;	 
	struct list_head d_lru;		 
	struct list_head d_child;	 
	struct list_head d_subdirs;	 
	struct list_head d_alias;	 
	struct qstr d_name;
	unsigned long d_time;		 
	struct dentry_operations  *d_op;
	struct super_block * d_sb;	 
	unsigned long d_reftime;	 
	void * d_fsdata;		 
	unsigned char d_iname[16 ];  
};

struct dentry_operations {
	int (*d_revalidate)(struct dentry *, int);
	int (*d_hash) (struct dentry *, struct qstr *);
	int (*d_compare) (struct dentry *, struct qstr *, struct qstr *);
	void (*d_delete)(struct dentry *);
	void (*d_release)(struct dentry *);
	void (*d_iput)(struct dentry *, struct inode *);
};

 








 






 












static __inline__ void d_drop(struct dentry * dentry)
{
	list_del(&dentry->d_hash);
	do { ( &dentry->d_hash )->next = ( &dentry->d_hash ); ( &dentry->d_hash )->prev = ( &dentry->d_hash ); } while (0) ;
}

static __inline__ int dname_external(struct dentry *d)
{
	return d->d_name.name != d->d_iname; 
}

 


extern void d_instantiate(struct dentry *, struct inode *);
extern void d_delete(struct dentry *);

 
extern struct dentry * d_alloc(struct dentry * parent, const struct qstr *name);
extern int prune_dcache(int, int);
extern void shrink_dcache_sb(struct super_block *);
extern void shrink_dcache_parent(struct dentry *);
extern int d_invalidate(struct dentry *);



 
extern void shrink_dcache_memory(int, unsigned int);
extern void check_dcache_memory(void);
extern void free_inode_memory(int);	 

 
extern struct dentry * d_alloc_root(struct inode * root_inode, struct dentry * old_root);

 
extern int is_root_busy(struct dentry *);

 
extern int have_submounts(struct dentry *);

 


extern void d_rehash(struct dentry * entry);
 



static __inline__ void d_add(struct dentry * entry, struct inode * inode)
{
	d_rehash(entry);
	d_instantiate(entry, inode);
}

 
extern void d_move(struct dentry * entry, struct dentry * newdentry);

 
extern struct dentry * d_lookup(struct dentry * dir, struct qstr * name);

 
extern int d_validate(struct dentry *dentry, struct dentry *dparent,
		      unsigned int hash, unsigned int len);

 
extern char * d_path(struct dentry * entry, char * buf, int buflen);

 
static __inline__ struct dentry * dget(struct dentry *dentry)
{
	if (dentry)
		dentry->d_count++;
	return dentry;
}

extern void dput(struct dentry *);




# 19 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/stat.h" 1





# 1 "/usr/src/linux/include/asm/stat.h" 1



struct __old_kernel_stat {
	unsigned short st_dev;
	unsigned short st_ino;
	unsigned short st_mode;
	unsigned short st_nlink;
	unsigned short st_uid;
	unsigned short st_gid;
	unsigned short st_rdev;
	unsigned long  st_size;
	unsigned long  st_atime;
	unsigned long  st_mtime;
	unsigned long  st_ctime;
};

struct stat {
	unsigned short st_dev;
	unsigned short __pad1;
	unsigned long st_ino;
	unsigned short st_mode;
	unsigned short st_nlink;
	unsigned short st_uid;
	unsigned short st_gid;
	unsigned short st_rdev;
	unsigned short __pad2;
	unsigned long  st_size;
	unsigned long  st_blksize;
	unsigned long  st_blocks;
	unsigned long  st_atime;
	unsigned long  __unused1;
	unsigned long  st_mtime;
	unsigned long  __unused2;
	unsigned long  st_ctime;
	unsigned long  __unused3;
	unsigned long  __unused4;
	unsigned long  __unused5;
};


# 6 "/usr/src/linux/include/linux/stat.h" 2




















































# 20 "/usr/src/linux/include/linux/fs.h" 2



# 1 "/usr/src/linux/include/linux/bitops.h" 1




 





extern __inline__ int generic_ffs(int x)
{
	int r = 1;

	if (!x)
		return 0;
	if (!(x & 0xffff)) {
		x >>= 16;
		r += 16;
	}
	if (!(x & 0xff)) {
		x >>= 8;
		r += 8;
	}
	if (!(x & 0xf)) {
		x >>= 4;
		r += 4;
	}
	if (!(x & 3)) {
		x >>= 2;
		r += 2;
	}
	if (!(x & 1)) {
		x >>= 1;
		r += 1;
	}
	return r;
}

 




extern __inline__ unsigned int generic_hweight32(unsigned int w)
{
        unsigned int res = (w & 0x55555555) + ((w >> 1) & 0x55555555);
        res = (res & 0x33333333) + ((res >> 2) & 0x33333333);
        res = (res & 0x0F0F0F0F) + ((res >> 4) & 0x0F0F0F0F);
        res = (res & 0x00FF00FF) + ((res >> 8) & 0x00FF00FF);
        return (res & 0x0000FFFF) + ((res >> 16) & 0x0000FFFF);
}

extern __inline__ unsigned int generic_hweight16(unsigned int w)
{
        unsigned int res = (w & 0x5555) + ((w >> 1) & 0x5555);
        res = (res & 0x3333) + ((res >> 2) & 0x3333);
        res = (res & 0x0F0F) + ((res >> 4) & 0x0F0F);
        return (res & 0x00FF) + ((res >> 8) & 0x00FF);
}

extern __inline__ unsigned int generic_hweight8(unsigned int w)
{
        unsigned int res = (w & 0x55) + ((w >> 1) & 0x55);
        res = (res & 0x33) + ((res >> 2) & 0x33);
        return (res & 0x0F) + ((res >> 4) & 0x0F);
}

# 1 "/usr/src/linux/include/asm/bitops.h" 1



 



 













 


extern void set_bit(int nr, volatile void * addr);
extern void clear_bit(int nr, volatile void * addr);
extern void change_bit(int nr, volatile void * addr);
extern int test_and_set_bit(int nr, volatile void * addr);
extern int test_and_clear_bit(int nr, volatile void * addr);
extern int test_and_change_bit(int nr, volatile void * addr);
extern int __constant_test_bit(int nr, const volatile void * addr);
extern int __test_bit(int nr, volatile void * addr);
extern int find_first_zero_bit(void * addr, unsigned size);
extern int find_next_zero_bit (void * addr, int size, int offset);
extern unsigned long ffz(unsigned long word);

 


struct __dummy { unsigned long a[100]; };



extern __inline__ void set_bit(int nr, volatile void * addr)
{
	__asm__ __volatile__( "" 
		"btsl %1,%0"
		:"=m" ((*(volatile struct __dummy *) addr) )
		:"Ir" (nr));
}

extern __inline__ void clear_bit(int nr, volatile void * addr)
{
	__asm__ __volatile__( "" 
		"btrl %1,%0"
		:"=m" ((*(volatile struct __dummy *) addr) )
		:"Ir" (nr));
}

extern __inline__ void change_bit(int nr, volatile void * addr)
{
	__asm__ __volatile__( "" 
		"btcl %1,%0"
		:"=m" ((*(volatile struct __dummy *) addr) )
		:"Ir" (nr));
}

extern __inline__ int test_and_set_bit(int nr, volatile void * addr)
{
	int oldbit;

	__asm__ __volatile__( "" 
		"btsl %2,%1\n\tsbbl %0,%0"
		:"=r" (oldbit),"=m" ((*(volatile struct __dummy *) addr) )
		:"Ir" (nr));
	return oldbit;
}

extern __inline__ int test_and_clear_bit(int nr, volatile void * addr)
{
	int oldbit;

	__asm__ __volatile__( "" 
		"btrl %2,%1\n\tsbbl %0,%0"
		:"=r" (oldbit),"=m" ((*(volatile struct __dummy *) addr) )
		:"Ir" (nr));
	return oldbit;
}

extern __inline__ int test_and_change_bit(int nr, volatile void * addr)
{
	int oldbit;

	__asm__ __volatile__( "" 
		"btcl %2,%1\n\tsbbl %0,%0"
		:"=r" (oldbit),"=m" ((*(volatile struct __dummy *) addr) )
		:"Ir" (nr));
	return oldbit;
}

 


extern __inline__ int __constant_test_bit(int nr, const volatile void * addr)
{
	return ((1UL << (nr & 31)) & (((const volatile unsigned int *) addr)[nr >> 5])) != 0;
}

extern __inline__ int __test_bit(int nr, volatile void * addr)
{
	int oldbit;

	__asm__ __volatile__(
		"btl %2,%1\n\tsbbl %0,%0"
		:"=r" (oldbit)
		:"m" ((*(volatile struct __dummy *) addr) ),"Ir" (nr));
	return oldbit;
}






 


extern __inline__ int find_first_zero_bit(void * addr, unsigned size)
{
	int d0, d1, d2;
	int res;

	if (!size)
		return 0;
	__asm__("cld\n\t"
		"movl $-1,%%eax\n\t"
		"xorl %%edx,%%edx\n\t"
		"repe; scasl\n\t"
		"je 1f\n\t"
		"xorl -4(%%edi),%%eax\n\t"
		"subl $4,%%edi\n\t"
		"bsfl %%eax,%%edx\n"
		"1:\tsubl %%ebx,%%edi\n\t"
		"shll $3,%%edi\n\t"
		"addl %%edi,%%edx"
		:"=d" (res), "=&c" (d0), "=&D" (d1), "=&a" (d2)
		:"1" ((size + 31) >> 5), "2" (addr), "b" (addr));
	return res;
}

extern __inline__ int find_next_zero_bit (void * addr, int size, int offset)
{
	unsigned long * p = ((unsigned long *) addr) + (offset >> 5);
	int set = 0, bit = offset & 31, res;
	
	if (bit) {
		 


		__asm__("bsfl %1,%0\n\t"
			"jne 1f\n\t"
			"movl $32, %0\n"
			"1:"
			: "=r" (set)
			: "r" (~(*p >> bit)));
		if (set < (32 - bit))
			return set + offset;
		set = 32 - bit;
		p++;
	}
	 


	res = find_first_zero_bit (p, size - 32 * (p - (unsigned long *) addr));
	return (offset + set + res);
}

 



extern __inline__ unsigned long ffz(unsigned long word)
{
	__asm__("bsfl %1,%0"
		:"=r" (word)
		:"r" (~word));
	return word;
}



 





extern __inline__ int ffs(int x)
{
	int r;

	__asm__("bsfl %1,%0\n\t"
		"jnz 1f\n\t"
		"movl $-1,%0\n"
		"1:" : "=r" (r) : "g" (x));
	return r+1;
}

 


















 








# 69 "/usr/src/linux/include/linux/bitops.h" 2




# 23 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/asm/cache.h" 1
 





 











# 24 "/usr/src/linux/include/linux/fs.h" 2



struct poll_table_struct;


 









 







 
extern int max_inodes;
extern int max_files, nr_files, nr_free_files;
extern int max_super_blocks, nr_super_blocks;






















 







 



















 




 





 




























 


























# 1 "/usr/src/linux/include/asm/byteorder.h" 1







 




static __inline__ __const__ __u32 ___arch__swab32(__u32 x)
{

	__asm__("bswap %0" : "=r" (x) : "0" (x));







	return x;
}

static __inline__ __const__ __u16 ___arch__swab16(__u16 x)
{
	__asm__("xchgb %b0,%h0"		  		: "=q" (x) 		:  "0" (x)); 		return x;



}











# 1 "/usr/src/linux/include/linux/byteorder/little_endian.h" 1










# 1 "/usr/src/linux/include/linux/byteorder/swab.h" 1



 













 













# 41 "/usr/src/linux/include/linux/byteorder/swab.h"

 

































 






















extern __inline__ __const__ __u16 __fswab16(__u16 x)
{
	return ___arch__swab16( x ) ;
}
extern __inline__ __u16 __swab16p(__u16 *x)
{
	return (__builtin_constant_p((__u16)( *( x ) )) ? ((__u16)( (((__u16)( ( *( x ) ) ) & (__u16)0x00ffU) << 8) | (((__u16)( ( *( x ) ) ) & (__u16)0xff00U) >> 8) ))  : __fswab16(( *( x ) )))  ;
}
extern __inline__ void __swab16s(__u16 *addr)
{
	do { *( addr ) = __swab16p(( addr )); } while (0) ;
}

extern __inline__ __const__ __u32 __fswab32(__u32 x)
{
	return ___arch__swab32( x ) ;
}
extern __inline__ __u32 __swab32p(__u32 *x)
{
	return (__builtin_constant_p((__u32)( *( x ) )) ? ((__u32)( (((__u32)( ( *( x ) ) ) & (__u32)0x000000ffUL) << 24) | (((__u32)( ( *( x ) ) ) & (__u32)0x0000ff00UL) <<  8) | (((__u32)( ( *( x ) ) ) & (__u32)0x00ff0000UL) >>  8) | (((__u32)( ( *( x ) ) ) & (__u32)0xff000000UL) >> 24) ))  : __fswab32(( *( x ) )))  ;
}
extern __inline__ void __swab32s(__u32 *addr)
{
	do { *( addr ) = __swab32p(( addr )); } while (0) ;
}


extern __inline__ __const__ __u64 __fswab64(__u64 x)
{

	__u32 h = x >> 32;
        __u32 l = x & ((1ULL<<32)-1);
        return (((__u64)(__builtin_constant_p((__u32)( l )) ? ((__u32)( (((__u32)( ( l ) ) & (__u32)0x000000ffUL) << 24) | (((__u32)( ( l ) ) & (__u32)0x0000ff00UL) <<  8) | (((__u32)( ( l ) ) & (__u32)0x00ff0000UL) >>  8) | (((__u32)( ( l ) ) & (__u32)0xff000000UL) >> 24) ))  : __fswab32(( l ))) ) << 32) | ((__u64)((__builtin_constant_p((__u32)( h )) ? ((__u32)( (((__u32)( ( h ) ) & (__u32)0x000000ffUL) << 24) | (((__u32)( ( h ) ) & (__u32)0x0000ff00UL) <<  8) | (((__u32)( ( h ) ) & (__u32)0x00ff0000UL) >>  8) | (((__u32)( ( h ) ) & (__u32)0xff000000UL) >> 24) ))  : __fswab32(( h ))) ));



}
extern __inline__ __u64 __swab64p(__u64 *x)
{
	return (__builtin_constant_p((__u64)( *( x ) )) ? ((__u64)( (__u64)(((__u64)( ( *( x ) ) ) & (__u64)0x00000000000000ffULL) << 56) | (__u64)(((__u64)( ( *( x ) ) ) & (__u64)0x000000000000ff00ULL) << 40) | (__u64)(((__u64)( ( *( x ) ) ) & (__u64)0x0000000000ff0000ULL) << 24) | (__u64)(((__u64)( ( *( x ) ) ) & (__u64)0x00000000ff000000ULL) <<  8) | (__u64)(((__u64)( ( *( x ) ) ) & (__u64)0x000000ff00000000ULL) >>  8) | (__u64)(((__u64)( ( *( x ) ) ) & (__u64)0x0000ff0000000000ULL) >> 24) | (__u64)(((__u64)( ( *( x ) ) ) & (__u64)0x00ff000000000000ULL) >> 40) | (__u64)(((__u64)( ( *( x ) ) ) & (__u64)0xff00000000000000ULL) >> 56) ))  : __fswab64(( *( x ) )))  ;
}
extern __inline__ void __swab64s(__u64 *addr)
{
	do { *( addr ) = __swab64p(( addr )); } while (0) ;
}















# 11 "/usr/src/linux/include/linux/byteorder/little_endian.h" 2











































# 1 "/usr/src/linux/include/linux/byteorder/generic.h" 1



 




































 









































 










































 


















 




extern __u32			ntohl(__u32);
extern __u32			htonl(__u32);




extern unsigned short int	ntohs(unsigned short int);
extern unsigned short int	htons(unsigned short int);























# 54 "/usr/src/linux/include/linux/byteorder/little_endian.h" 2



# 45 "/usr/src/linux/include/asm/byteorder.h" 2



# 169 "/usr/src/linux/include/linux/fs.h" 2



extern void update_atime (struct inode *inode);


extern void buffer_init(unsigned long);
extern void inode_init(void);
extern void file_table_init(void);
extern void dcache_init(void);

typedef char buffer_block[(1<< 10 ) ];

 






 











struct buffer_head {
	 
	struct buffer_head * b_next;	 
	unsigned long b_blocknr;	 
	unsigned long b_size;		 
	kdev_t b_dev;			 
	kdev_t b_rdev;			 
	unsigned long b_rsector;	 
	struct buffer_head * b_this_page;	 
	unsigned long b_state;		 
	struct buffer_head * b_next_free;
	unsigned int b_count;		 

	 
	char * b_data;			 
	unsigned int b_list;		 
	unsigned long b_flushtime;       

	struct wait_queue * b_wait;
	struct buffer_head ** b_pprev;		 
	struct buffer_head * b_prev_free;	 
	struct buffer_head * b_reqnext;		 

	 


	void (*b_end_io)(struct buffer_head *bh, int uptodate);
	void *b_dev_id;
};

typedef void (bh_end_io_t)(struct buffer_head *bh, int uptodate);
void init_buffer(struct buffer_head *bh, kdev_t dev, int block,
		 bh_end_io_t *handler, void *dev_id);

static inline int buffer_uptodate(struct buffer_head * bh)
{
	return (__builtin_constant_p( 0  ) ? __constant_test_bit(( 0  ),(  &bh->b_state )) : __test_bit(( 0  ),(  &bh->b_state ))) ;
}	

static inline int buffer_dirty(struct buffer_head * bh)
{
	return (__builtin_constant_p( 1  ) ? __constant_test_bit(( 1  ),(  &bh->b_state )) : __test_bit(( 1  ),(  &bh->b_state ))) ;
}

static inline int buffer_locked(struct buffer_head * bh)
{
	return (__builtin_constant_p( 2  ) ? __constant_test_bit(( 2  ),(  &bh->b_state )) : __test_bit(( 2  ),(  &bh->b_state ))) ;
}

static inline int buffer_req(struct buffer_head * bh)
{
	return (__builtin_constant_p( 3  ) ? __constant_test_bit(( 3  ),(  &bh->b_state )) : __test_bit(( 3  ),(  &bh->b_state ))) ;
}

static inline int buffer_protected(struct buffer_head * bh)
{
	return (__builtin_constant_p( 6  ) ? __constant_test_bit(( 6  ),(  &bh->b_state )) : __test_bit(( 6  ),(  &bh->b_state ))) ;
}




# 1 "/usr/src/linux/include/linux/pipe_fs_i.h" 1



struct pipe_inode_info {
	struct wait_queue * wait;
	char * base;
	unsigned int start;
	unsigned int lock;
	unsigned int rd_openers;
	unsigned int wr_openers;
	unsigned int readers;
	unsigned int writers;
};





















# 263 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/minix_fs_i.h" 1



 


struct minix_inode_info {
	union {
		__u16 i1_data[16];
		__u32 i2_data[16];
	} u;
};


# 264 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/ext2_fs_i.h" 1
 

















 


struct ext2_inode_info {
	__u32	i_data[15];
	__u32	i_flags;
	__u32	i_faddr;
	__u8	i_frag_no;
	__u8	i_frag_size;
	__u16	i_osync;
	__u32	i_file_acl;
	__u32	i_dir_acl;
	__u32	i_dtime;
	__u32	i_version;
	__u32	i_block_group;
	__u32	i_next_alloc_block;
	__u32	i_next_alloc_goal;
	__u32	i_prealloc_block;
	__u32	i_prealloc_count;
	__u32	i_high_size;
	int	i_new_inode:1;	 
};


# 265 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/hpfs_fs_i.h" 1



struct hpfs_inode_info {
	ino_t i_parent_dir;	 
	unsigned i_dno;		 
	unsigned i_dpos;	 
	unsigned i_dsubdno;	 
	unsigned i_file_sec;	 
	unsigned i_disk_sec;	 
	unsigned i_n_secs;	 
	unsigned i_conv : 2;	 
};











# 266 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/ntfs_fs_i.h" 1



 
struct ntfs_attribute;
struct ntfs_sb_info;

 


typedef u8  ntfs_u8;
typedef u16 ntfs_u16;
typedef u32 ntfs_u32;
typedef u64 ntfs_u64;
typedef s8  ntfs_s8;
typedef s16 ntfs_s16;
typedef s32 ntfs_s32;
typedef s64 ntfs_s64;




typedef __kernel_mode_t ntmode_t;



typedef __kernel_uid_t ntfs_uid_t;



typedef __kernel_gid_t ntfs_gid_t;



typedef __kernel_size_t ntfs_size_t;



typedef __kernel_time_t ntfs_time_t;


 


typedef unsigned short     ntfs_wchar_t;

 


typedef unsigned long long ntfs_offset_t;

 


typedef unsigned long long ntfs_time64_t;

 


typedef unsigned int ntfs_cluster_t;


 
struct ntfs_inode_info{
	struct ntfs_sb_info *vol;
	int i_number;                 
	unsigned sequence_number;
	unsigned char* attr;          
	int attr_count;               
	struct ntfs_attribute *attrs;
	int record_count;             
	 

	int *records;
	union{
		struct{
			int recordsize;
			int clusters_per_record;
		}index;
	} u;	
};


# 267 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/msdos_fs_i.h" 1







 



struct msdos_inode_info {
	 













	struct pipe_inode_info reserved;
	int i_start;	 
	int i_logstart;	 
	int i_attrs;	 
	int i_ctime_ms;	 
	int i_binary;	 
	int i_location;	 
	struct inode *i_fat_inode;	 
	struct list_head i_fat_hash;	 
	off_t i_last_pos; 
};


# 268 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/umsdos_fs_i.h" 1










 





































struct dir_locking_info {
	struct wait_queue *p;
	short int looking;	 
	short int creating;	 



	long pid;		 
	 
};

struct umsdos_inode_info {
	union {
		struct msdos_inode_info msdos_info;
		struct pipe_inode_info pipe_info;
		struct dir_locking_info dir_info;
	} u;
	int i_patched;			 
	int i_is_hlink;			 
	unsigned long i_emd_owner;	 
	off_t pos;			 
	 
	struct dentry *i_emd_dentry;	 
	unsigned long i_emd_dir;	 
};


# 269 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/iso_fs_i.h" 1



 


struct iso_inode_info {
	unsigned int i_first_extent;
	unsigned char i_file_format;
	unsigned long i_next_section_ino;
	off_t i_section_size;
};


# 270 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/nfs_fs_i.h" 1



# 1 "/usr/src/linux/include/linux/nfs.h" 1
 





# 1 "/usr/src/linux/include/linux/sunrpc/msg_prot.h" 1
 












enum rpc_auth_flavor {
	RPC_AUTH_NULL  = 0,
	RPC_AUTH_UNIX  = 1,
	RPC_AUTH_SHORT = 2,
	RPC_AUTH_DES   = 3,
	RPC_AUTH_KRB   = 4,
};

enum rpc_msg_type {
	RPC_CALL = 0,
	RPC_REPLY = 1
};

enum rpc_reply_stat {
	RPC_MSG_ACCEPTED = 0,
	RPC_MSG_DENIED = 1
};

enum rpc_accept_stat {
	RPC_SUCCESS = 0,
	RPC_PROG_UNAVAIL = 1,
	RPC_PROG_MISMATCH = 2,
	RPC_PROC_UNAVAIL = 3,
	RPC_GARBAGE_ARGS = 4,
	RPC_SYSTEM_ERR = 5
};

enum rpc_reject_stat {
	RPC_MISMATCH = 0,
	RPC_AUTH_ERROR = 1
};

enum rpc_auth_stat {
	RPC_AUTH_OK = 0,
	RPC_AUTH_BADCRED = 1,
	RPC_AUTH_REJECTEDCRED = 2,
	RPC_AUTH_BADVERF = 3,
	RPC_AUTH_REJECTEDVERF = 4,
	RPC_AUTH_TOOWEAK = 5
};









# 7 "/usr/src/linux/include/linux/nfs.h" 2



















	
enum nfs_stat {
	NFS_OK = 0,
	NFSERR_PERM = 1,
	NFSERR_NOENT = 2,
	NFSERR_IO = 5,
	NFSERR_NXIO = 6,
	NFSERR_EAGAIN = 11,
	NFSERR_ACCES = 13,
	NFSERR_EXIST = 17,
	NFSERR_XDEV = 18,
	NFSERR_NODEV = 19,
	NFSERR_NOTDIR = 20,
	NFSERR_ISDIR = 21,
	NFSERR_INVAL = 22,	 
	NFSERR_FBIG = 27,
	NFSERR_NOSPC = 28,
	NFSERR_ROFS = 30,
	NFSERR_OPNOTSUPP = 45,
	NFSERR_NAMETOOLONG = 63,
	NFSERR_NOTEMPTY = 66,
	NFSERR_DQUOT = 69,
	NFSERR_STALE = 70,
	NFSERR_WFLUSH = 99
};

enum nfs_ftype {
	NFNON = 0,
	NFREG = 1,
	NFDIR = 2,
	NFBLK = 3,
	NFCHR = 4,
	NFLNK = 5,
	NFSOCK = 6,
	NFBAD = 7,
	NFFIFO = 8
};

struct nfs_fh {
	char			data[32 ];
};






















 










extern struct rpc_program	nfs_program;
extern struct rpc_stat		nfs_rpcstat;

struct nfs_time {
	__u32			seconds;
	__u32			useconds;
};

struct nfs_fattr {
	enum nfs_ftype		type;
	__u32			mode;
	__u32			nlink;
	__u32			uid;
	__u32			gid;
	__u32			size;
	__u32			blocksize;
	__u32			rdev;
	__u32			blocks;
	__u32			fsid;
	__u32			fileid;
	struct nfs_time		atime;
	struct nfs_time		mtime;
	struct nfs_time		ctime;
};

struct nfs_sattr {
	__u32			mode;
	__u32			uid;
	__u32			gid;
	__u32			size;
	struct nfs_time		atime;
	struct nfs_time		mtime;
};

struct nfs_fsinfo {
	__u32			tsize;
	__u32			bsize;
	__u32			blocks;
	__u32			bfree;
	__u32			bavail;
};

struct nfs_writeargs {
	struct nfs_fh *		fh;
	__u32			offset;
	__u32			count;
	const void *		buffer;
};

# 223 "/usr/src/linux/include/linux/nfs.h"




# 4 "/usr/src/linux/include/linux/nfs_fs_i.h" 2



 


struct nfs_inode_info {
	 




	struct pipe_inode_info	pipeinfo;

	 


	unsigned short		flags;

	 
















	unsigned long		read_cache_jiffies;
	unsigned long		read_cache_mtime;
	unsigned long		attrtimeo;

	 




	struct nfs_wreq *	writeback;
};

 





 


struct nfs_lock_info {
	u32		state;
	u32		flags;
};

 





# 271 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/sysv_fs_i.h" 1



 


struct sysv_inode_info {
	u32 i_data[10+1+1+1];	 




};



# 272 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/affs_fs_i.h" 1



# 1 "/usr/src/linux/include/linux/a.out.h" 1







# 1 "/usr/src/linux/include/asm/a.out.h" 1



struct exec
{
  unsigned long a_info;		 
  unsigned a_text;		 
  unsigned a_data;		 
  unsigned a_bss;		 
  unsigned a_syms;		 
  unsigned a_entry;		 
  unsigned a_trsize;		 
  unsigned a_drsize;		 
};












# 8 "/usr/src/linux/include/linux/a.out.h" 2




 
enum machine_type {



  M_OLDSUN2 = 0,




  M_68010 = 1,




  M_68020 = 2,




  M_SPARC = 3,

   
  M_386 = 100,
  M_MIPS1 = 151,	 
  M_MIPS2 = 152		 
};





















 

 

 

 



 





































 




 





































 





struct nlist {
  union {
    char *n_name;
    struct nlist *n_next;
    long n_strx;
  } n_un;
  unsigned char n_type;
  char n_other;
  short n_desc;
  unsigned long n_value;
};































 









 










 





 



 




struct relocation_info
{
   
  int r_address;
   
  unsigned int r_symbolnum:24;
   


  unsigned int r_pcrel:1;
   

  unsigned int r_length:2;
   





  unsigned int r_extern:1;
   






  unsigned int r_pad:4;

};




# 4 "/usr/src/linux/include/linux/affs_fs_i.h" 2






struct key_cache {
	struct timeval	 kc_lru_time;	 
	s32	 kc_first;		 
	s32	 kc_last;		 
	s32	 kc_this_key;		 
	int	 kc_this_seq;		 
	s32	 kc_next_key;		 
	s32	 kc_keys[73 ];	 
};



struct ext_cache {
	struct key_cache  kc[4];	 
	s32	 ec[((1UL << 12 )  - 4 * sizeof(struct key_cache) - 4) / 4 ];		 
	int	 max_ext;		 
};

 


struct affs_inode_info {
	u32	 i_protect;			 
	s32	 i_parent;			 
	s32	 i_original;			 
	s32	 i_data[16 ];	 
	struct ext_cache *i_ec;			 
	int	 i_cache_users;			 
	int	 i_lastblock;			 
	short	 i_pa_cnt;			 
	short	 i_pa_next;			 
	short	 i_pa_last;			 
	short	 i_zone;			 
	unsigned char i_hlink;			 
	unsigned char i_pad;
};


# 273 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/ufs_fs_i.h" 1
 














struct ufs_inode_info {
	union {
		__u32	i_data[15];
		__u8	i_symlink[4*15];
	} i_u1;
	__u64	i_size;
	__u32	i_flags;
	__u32	i_gen;
	__u32	i_shadow;
	__u32	i_uid;
	__u32	i_gid;
	__u32	i_oeftflag;
	__u16	i_osync;
	__u32	i_lastfrag;
};


# 274 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/efs_fs_i.h" 1
 










typedef	int32_t		efs_block_t;
typedef uint32_t	efs_ino_t;



 


typedef union extent_u {
	unsigned char raw[8];
	struct extent_s {
		unsigned int	ex_magic:8;	 
		unsigned int	ex_bn:24;	 
		unsigned int	ex_length:8;	 
		unsigned int	ex_offset:24;	 
	} cooked;
} efs_extent;

typedef struct edevs {
	short		odev;
	short		dev_filler;	 
	unsigned int	ndev;		 
} efs_devs;

 



struct	efs_dinode {
	u_short		di_mode;	 
	short		di_nlink;	 
	u_short		di_uid;		 
	u_short		di_gid;		 
	int32_t		di_size;	 
	int32_t		di_atime;	 
	int32_t		di_mtime;	 
	int32_t		di_ctime;	 
	uint32_t	di_gen;		 
	short		di_numextents;	 
	u_char		di_version;	 
	u_char		di_spare;	 
	union di_addr {
		efs_extent	di_extents[12 ];
		efs_devs	di_dev;	 
	} di_u;
};

 
struct efs_inode_info {
	int		numextents;
	int		lastextent;

	efs_extent	extents[12 ];
};



# 275 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/coda_fs_i.h" 1
 












# 1 "/usr/src/linux/include/linux/coda.h" 1
 




 
















 




























 











 








# 98 "/usr/src/linux/include/linux/coda.h"











typedef unsigned long long u_quad_t;












# 130 "/usr/src/linux/include/linux/coda.h"



 






 








  



 










struct venus_dirent {
        unsigned long	d_fileno;		 
        unsigned short	d_reclen;		 
        unsigned char 	d_type;			 
        unsigned char	d_namlen;		 
        char		d_name[255  + 1]; 
};




 












 









typedef u_long VolumeId;
typedef u_long VnodeId;
typedef u_long Unique_t;
typedef u_long FileVersion;




typedef struct ViceFid {
    VolumeId Volume;
    VnodeId Vnode;
    Unique_t Unique;
} ViceFid;




static __inline__ ino_t  coda_f2i(struct ViceFid *fid)
{
	if ( ! fid ) 
		return 0; 
	if (fid->Vnode == 0xfffffffe || fid->Vnode == 0xffffffff)
		return ((fid->Volume << 20) | (fid->Unique & 0xfffff));
	else
		return (fid->Unique + (fid->Vnode<<10) + (fid->Volume<<20));
}
	








typedef u_int32_t vuid_t;
typedef u_int32_t vgid_t;




struct coda_cred {
    vuid_t cr_uid, cr_euid, cr_suid, cr_fsuid;  
    vgid_t cr_groupid,     cr_egid, cr_sgid, cr_fsgid;  
};




 


enum coda_vtype	{ C_VNON, C_VREG, C_VDIR, C_VBLK, C_VCHR, C_VLNK, C_VSOCK, C_VFIFO, C_VBAD };

struct coda_vattr {
	long     	va_type;	 
	u_short		va_mode;	 
	short		va_nlink;	 
	vuid_t		va_uid;		 
	vgid_t		va_gid;		 
	long		va_fileid;	 
	u_quad_t	va_size;	 
	long		va_blocksize;	 
	struct timespec	va_atime;	 
	struct timespec	va_mtime;	 
	struct timespec	va_ctime;	 
	u_long		va_gen;		 
	u_long		va_flags;	 
	u_quad_t 	        va_rdev;	 
	u_quad_t	va_bytes;	 
	u_quad_t	va_filerev;	 
};



 
struct coda_statfs {
    int32_t f_blocks;
    int32_t f_bfree;
    int32_t f_bavail;
    int32_t f_files;
    int32_t f_ffree;
};

 


















































	 


 


struct coda_in_hdr {
    unsigned long opcode;
    unsigned long unique;	     
    u_short pid;		     
    u_short pgid;		     
    u_short sid;                     
    struct coda_cred cred;	     
};

 
struct coda_out_hdr {
    unsigned long opcode;
    unsigned long unique;	
    unsigned long result;
};

 
struct coda_root_out {
    struct coda_out_hdr oh;
    ViceFid VFid;
};

struct coda_root_in {
    struct coda_in_hdr in;
};

 
 

 
struct coda_open_in {
    struct coda_in_hdr ih;
    ViceFid	VFid;
    int	flags;
};

struct coda_open_out {
    struct coda_out_hdr oh;
    u_quad_t 	dev;
    ino_t	inode;
};


 
struct coda_close_in {
    struct coda_in_hdr ih;
    ViceFid	VFid;
    int	flags;
};

struct coda_close_out {
    struct coda_out_hdr out;
};

 
struct coda_ioctl_in {
    struct coda_in_hdr ih;
    ViceFid VFid;
    int	cmd;
    int	len;
    int	rwflag;
    char *data;			 
};

struct coda_ioctl_out {
    struct coda_out_hdr oh;
    int	len;
    caddr_t	data;		 
};


 
struct coda_getattr_in {
    struct coda_in_hdr ih;
    ViceFid VFid;
};

struct coda_getattr_out {
    struct coda_out_hdr oh;
    struct coda_vattr attr;
};


 
struct coda_setattr_in {
    struct coda_in_hdr ih;
    ViceFid VFid;
    struct coda_vattr attr;
};

struct coda_setattr_out {
    struct coda_out_hdr out;
};

 
struct coda_access_in {
    struct coda_in_hdr ih;
    ViceFid	VFid;
    int	flags;
};

struct coda_access_out {
    struct coda_out_hdr out;
};


 



 
struct  coda_lookup_in {
    struct coda_in_hdr ih;
    ViceFid	VFid;
    int         name;		 
    int         flags;	
};

struct coda_lookup_out {
    struct coda_out_hdr oh;
    ViceFid VFid;
    int	vtype;
};


 
struct coda_create_in {
    struct coda_in_hdr ih;
    ViceFid VFid;
    struct coda_vattr attr;
    int excl;
    int mode;
    int 	name;		 
};

struct coda_create_out {
    struct coda_out_hdr oh;
    ViceFid VFid;
    struct coda_vattr attr;
};


 
struct coda_remove_in {
    struct coda_in_hdr ih;
    ViceFid	VFid;
    int name;		 
};

struct coda_remove_out {
    struct coda_out_hdr out;
};

 
struct coda_link_in {
    struct coda_in_hdr ih;
    ViceFid sourceFid;           
    ViceFid destFid;             
    int tname;		 
};

struct coda_link_out {
    struct coda_out_hdr out;
};


 
struct coda_rename_in {
    struct coda_in_hdr ih;
    ViceFid	sourceFid;
    int 	srcname;
    ViceFid destFid;
    int 	destname;
};

struct coda_rename_out {
    struct coda_out_hdr out;
};

 
struct coda_mkdir_in {
    struct coda_in_hdr ih;
    ViceFid	VFid;
    struct coda_vattr attr;
    int	   name;		 
};

struct coda_mkdir_out {
    struct coda_out_hdr oh;
    ViceFid VFid;
    struct coda_vattr attr;
};


 
struct coda_rmdir_in {
    struct coda_in_hdr ih;
    ViceFid	VFid;
    int name;		 
};

struct coda_rmdir_out {
    struct coda_out_hdr out;
};

 
struct coda_readdir_in {
    struct coda_in_hdr ih;
    ViceFid	VFid;
    int	count;
    int	offset;
};

struct coda_readdir_out {
    struct coda_out_hdr oh;
    int	size;
    caddr_t	data;		 
};

 
struct coda_symlink_in {
    struct coda_in_hdr ih;
    ViceFid	VFid;           
    int srcname;
    struct coda_vattr attr;
    int tname;
};

struct coda_symlink_out {
    struct coda_out_hdr out;
};

 
struct coda_readlink_in {
    struct coda_in_hdr ih;
    ViceFid VFid;
};

struct coda_readlink_out {
    struct coda_out_hdr oh;
    int	count;
    caddr_t	data;		 
};


 
struct coda_fsync_in {
    struct coda_in_hdr ih;
    ViceFid VFid;
};

struct coda_fsync_out {
    struct coda_out_hdr out;
};

 
struct coda_inactive_in {
    struct coda_in_hdr ih;
    ViceFid VFid;
};

 
struct coda_vget_in {
    struct coda_in_hdr ih;
    ViceFid VFid;
};

struct coda_vget_out {
    struct coda_out_hdr oh;
    ViceFid VFid;
    int	vtype;
};


 
 
 

 
 
struct coda_purgeuser_out {
    struct coda_out_hdr oh;
    struct coda_cred cred;
};

 
 
struct coda_zapfile_out {  
    struct coda_out_hdr oh;
    ViceFid CodaFid;
};

 
 	
struct coda_zapdir_out {	  
    struct coda_out_hdr oh;
    ViceFid CodaFid;
};

 
 	
struct coda_zapvnode_out { 
    struct coda_out_hdr oh;
    struct coda_cred cred;
    ViceFid VFid;
};

 
 	
struct coda_purgefid_out { 
    struct coda_out_hdr oh;
    ViceFid CodaFid;
};

 
struct coda_rdwr_in {
    struct coda_in_hdr ih;
    ViceFid	VFid;
    int	rwflag;
    int	count;
    int	offset;
    int	ioflag;
    caddr_t	data;		 	
};

struct coda_rdwr_out {
    struct coda_out_hdr oh;
    int	rwflag;
    int	count;
    caddr_t	data;	 
};


 
 	
struct coda_replace_out {  
    struct coda_out_hdr oh;
    ViceFid NewFid;
    ViceFid OldFid;
};

 
struct coda_open_by_path_in {
    struct coda_in_hdr ih;
    ViceFid	VFid;
    int	flags;
};

struct coda_open_by_path_out {
    struct coda_out_hdr oh;
	int path;
};

 
struct coda_statfs_in {
    struct coda_in_hdr in;
};

struct coda_statfs_out {
    struct coda_out_hdr oh;
    struct coda_statfs stat;
};

 






union inputArgs {
    struct coda_in_hdr ih;		 
    struct coda_open_in coda_open;
    struct coda_close_in coda_close;
    struct coda_ioctl_in coda_ioctl;
    struct coda_getattr_in coda_getattr;
    struct coda_setattr_in coda_setattr;
    struct coda_access_in coda_access;
    struct coda_lookup_in coda_lookup;
    struct coda_create_in coda_create;
    struct coda_remove_in coda_remove;
    struct coda_link_in coda_link;
    struct coda_rename_in coda_rename;
    struct coda_mkdir_in coda_mkdir;
    struct coda_rmdir_in coda_rmdir;
    struct coda_readdir_in coda_readdir;
    struct coda_symlink_in coda_symlink;
    struct coda_readlink_in coda_readlink;
    struct coda_fsync_in coda_fsync;
    struct coda_inactive_in coda_inactive;
    struct coda_vget_in coda_vget;
    struct coda_rdwr_in coda_rdwr;
    struct coda_open_by_path_in coda_open_by_path;
    struct coda_statfs_in coda_statfs;
};

union outputArgs {
    struct coda_out_hdr oh;		 
    struct coda_root_out coda_root;
    struct coda_open_out coda_open;
    struct coda_ioctl_out coda_ioctl;
    struct coda_getattr_out coda_getattr;
    struct coda_lookup_out coda_lookup;
    struct coda_create_out coda_create;
    struct coda_mkdir_out coda_mkdir;
    struct coda_readdir_out coda_readdir;
    struct coda_readlink_out coda_readlink;
    struct coda_vget_out coda_vget;
    struct coda_purgeuser_out coda_purgeuser;
    struct coda_zapfile_out coda_zapfile;
    struct coda_zapdir_out coda_zapdir;
    struct coda_zapvnode_out coda_zapvnode;
    struct coda_purgefid_out coda_purgefid;
    struct coda_rdwr_out coda_rdwr;
    struct coda_replace_out coda_replace;
    struct coda_open_by_path_out coda_open_by_path;
    struct coda_statfs_out coda_statfs;
};    

union coda_downcalls {
     
     
    struct coda_purgeuser_out purgeuser;
    struct coda_zapfile_out zapfile;
    struct coda_zapdir_out zapdir;
    struct coda_zapvnode_out zapvnode;
    struct coda_purgefid_out purgefid;
    struct coda_replace_out replace;
};


 




struct ViceIoctl {
        caddr_t in, out;         
        short in_size;           
        short out_size;          
};

struct PioctlData {
        const char *path;
        int follow;
        struct ViceIoctl vi;
};















# 14 "/usr/src/linux/include/linux/coda_fs_i.h" 2





 


struct coda_inode_info {
	 




	struct pipe_inode_info  pipeinfo;

        struct ViceFid     c_fid;	 
        u_short	           c_flags;      
        struct inode      *c_ovp;        
        struct list_head   c_cnhead;     
	struct list_head   c_volrootlist;  
        struct inode      *c_vnode;      
	unsigned int	   c_contcount;  
        int                c_magic;      
};

 




int coda_cnode_make(struct inode **, struct ViceFid *, struct super_block *);
int coda_cnode_makectl(struct inode **inode, struct super_block *sb);
struct inode *coda_fid_to_inode(ViceFid *fid, struct super_block *sb);
void coda_replace_fid(struct inode *, ViceFid *, ViceFid *);



# 276 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/romfs_fs_i.h" 1



 

struct romfs_inode_info {
	unsigned long i_metasize;	 
	unsigned long i_dataoffset;	 
};


# 277 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/smb_fs_i.h" 1
 













 


struct smb_inode_info {

	 



        unsigned int open;	 
	__u16 fileid;		 
	__u16 attr;		 

	__u16 access;		 
	__u16 cache_valid;	 
	unsigned long oldmtime;	 
	unsigned long closed;	 
};



# 278 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/hfs_fs_i.h" 1
 












 




struct hfs_inode_info {
	int				magic;      

	struct hfs_cat_entry		*entry;

	 
	struct hfs_fork 		*fork;
	int				convert;

	 
	ino_t				file_type;
	char				dir_size;

	 
	const struct hfs_hdr_layout	*default_layout;
	struct hfs_hdr_layout		*layout;

	 
	int                             tz_secondswest;

         
        void (*d_drop_op)(struct dentry *, const ino_t);
};


# 279 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/adfs_fs_i.h" 1
 








 


struct adfs_inode_info {
	unsigned long	file_id;		 
};


# 280 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/qnx4_fs_i.h" 1
 












# 1 "/usr/src/linux/include/linux/qnxtypes.h" 1
 













typedef __u16 qnx4_nxtnt_t;
typedef __u8  qnx4_ftype_t;

typedef struct {
	__u32 xtnt_blk;
	__u32 xtnt_size;
} qnx4_xtnt_t;

typedef __u16 qnx4_mode_t;
typedef __u16 qnx4_muid_t;
typedef __u16 qnx4_mgid_t;
typedef __u32 qnx4_off_t;
typedef __u16 qnx4_nlink_t;


# 14 "/usr/src/linux/include/linux/qnx4_fs_i.h" 2


 


struct qnx4_inode_info {
	char		i_reserved[16];	 
	qnx4_off_t	i_size;		 
	qnx4_xtnt_t	i_first_xtnt;	 
	__u32		i_xblk;		 
	__s32		i_ftime;	 
	__s32		i_mtime;	 
	__s32		i_atime;	 
	__s32		i_ctime;	 
	qnx4_nxtnt_t	i_num_xtnts;	 
	qnx4_mode_t	i_mode;		 
	qnx4_muid_t	i_uid;		 
	qnx4_mgid_t	i_gid;		 
	qnx4_nlink_t	i_nlink;	 
	__u8		i_zero[4];	 
	qnx4_ftype_t	i_type;		 
	__u8		i_status;	 
};


# 281 "/usr/src/linux/include/linux/fs.h" 2


 















 








struct iattr {
	unsigned int	ia_valid;
	umode_t		ia_mode;
	uid_t		ia_uid;
	gid_t		ia_gid;
	off_t		ia_size;
	time_t		ia_atime;
	time_t		ia_mtime;
	time_t		ia_ctime;
	unsigned int	ia_attr_flags;
};

 








 


# 1 "/usr/src/linux/include/linux/quota.h" 1
 








































# 1 "/usr/src/linux/include/linux/errno.h" 1



# 1 "/usr/src/linux/include/asm/errno.h" 1




































































































































# 4 "/usr/src/linux/include/linux/errno.h" 2




 








# 42 "/usr/src/linux/include/linux/quota.h" 2


 





 





 















 











extern int nr_dquots, nr_free_dquots;
extern int max_dquots;
extern int dquot_root_squash;




 



















 




struct dqblk {
	__u32 dqb_bhardlimit;	 
	__u32 dqb_bsoftlimit;	 
	__u32 dqb_curblocks;	 
	__u32 dqb_ihardlimit;	 
	__u32 dqb_isoftlimit;	 
	__u32 dqb_curinodes;	 
	time_t dqb_btime;		 
	time_t dqb_itime;		 
};

 













struct dqstats {
	__u32 lookups;
	__u32 drops;
	__u32 reads;
	__u32 writes;
	__u32 cache_hits;
	__u32 allocated_dquots;
	__u32 free_dquots;
	__u32 syncs;
};



 












struct dquot {
	struct dquot *dq_next;		 
	struct dquot **dq_pprev;
	struct list_head dq_free;	 
	struct dquot *dq_hash_next;	 
	struct dquot **dq_hash_pprev;	 
	struct wait_queue *dq_wait;	 
	int dq_count;			 

	 
	struct vfsmount *dq_mnt;	 
	unsigned int dq_id;		 
	kdev_t dq_dev;			 
	short dq_type;			 
	short dq_flags;			 
	unsigned long dq_referenced;	 

	struct dqblk dq_dqb;		 
};



 










# 208 "/usr/src/linux/include/linux/quota.h"


# 332 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/mount.h" 1
 















struct quota_mount_options
{
	unsigned int flags;			 
	struct semaphore dqio_sem;		 
	struct semaphore dqoff_sem;		 
	struct file *files[2 ];		 
	time_t inode_expire[2 ];		 
	time_t block_expire[2 ];		 
	char rsquash[2 ];		 
};

struct vfsmount
{
  kdev_t mnt_dev;			 
  char *mnt_devname;			 
  char *mnt_dirname;			 
  unsigned int mnt_flags;		 
  struct super_block *mnt_sb;		 
  struct quota_mount_options mnt_dquot;	 
  struct vfsmount *mnt_next;		 
};

struct vfsmount *lookup_vfsmnt(kdev_t dev);

 


 



# 333 "/usr/src/linux/include/linux/fs.h" 2


struct inode {
	struct list_head	i_hash;
	struct list_head	i_list;
	struct list_head	i_dentry;

	unsigned long		i_ino;
	unsigned int		i_count;
	kdev_t			i_dev;
	umode_t			i_mode;
	nlink_t			i_nlink;
	uid_t			i_uid;
	gid_t			i_gid;
	kdev_t			i_rdev;
	off_t			i_size;
	time_t			i_atime;
	time_t			i_mtime;
	time_t			i_ctime;
	unsigned long		i_blksize;
	unsigned long		i_blocks;
	unsigned long		i_version;
	unsigned long		i_nrpages;
	struct semaphore	i_sem;
	struct semaphore	i_atomic_write;
	struct inode_operations	*i_op;
	struct super_block	*i_sb;
	struct wait_queue	*i_wait;
	struct file_lock	*i_flock;
	struct vm_area_struct	*i_mmap;
	struct page		*i_pages;
	struct dquot		*i_dquot[2 ];

	unsigned long		i_state;

	unsigned int		i_flags;
	unsigned char		i_pipe;
	unsigned char		i_sock;

	int			i_writecount;
	unsigned int		i_attr_flags;
	__u32			i_generation;
	union {
		struct pipe_inode_info		pipe_i;
		struct minix_inode_info		minix_i;
		struct ext2_inode_info		ext2_i;
		struct hpfs_inode_info		hpfs_i;
		struct ntfs_inode_info          ntfs_i;
		struct msdos_inode_info		msdos_i;
		struct umsdos_inode_info	umsdos_i;
		struct iso_inode_info		isofs_i;
		struct nfs_inode_info		nfs_i;
		struct sysv_inode_info		sysv_i;
		struct affs_inode_info		affs_i;
		struct ufs_inode_info		ufs_i;
		struct efs_inode_info		efs_i;
		struct romfs_inode_info		romfs_i;
		struct coda_inode_info		coda_i;
		struct smb_inode_info		smbfs_i;
		struct hfs_inode_info		hfs_i;
		struct adfs_inode_info		adfs_i;
		struct qnx4_inode_info		qnx4_i;
		struct socket			socket_i;
		void				*generic_ip;
	} u;
};

 




extern void __mark_inode_dirty(struct inode *);
static inline void mark_inode_dirty(struct inode *inode)
{
	if (!(inode->i_state & 1 ))
		__mark_inode_dirty(inode);
}

struct fown_struct {
	int pid;		 
	uid_t uid, euid;	 
	int signum;		 
};

struct file {
	struct file		*f_next, **f_pprev;
	struct dentry		*f_dentry;
	struct file_operations	*f_op;
	mode_t			f_mode;
	loff_t			f_pos;
	unsigned int 		f_count, f_flags;
	unsigned long 		f_reada, f_ramax, f_raend, f_ralen, f_rawin;
	struct fown_struct	f_owner;
	unsigned int		f_uid, f_gid;
	int			f_error;

	unsigned long		f_version;

	 
	void			*private_data;
};

extern int init_private_file(struct file *, struct dentry *, int);







 






typedef struct files_struct *fl_owner_t;

struct file_lock {
	struct file_lock *fl_next;	 
	struct file_lock *fl_nextlink;	 
	struct file_lock *fl_prevlink;	 
	struct file_lock *fl_nextblock;  
	struct file_lock *fl_prevblock;
	fl_owner_t fl_owner;
	unsigned int fl_pid;
	struct wait_queue *fl_wait;
	struct file *fl_file;
	unsigned char fl_flags;
	unsigned char fl_type;
	off_t fl_start;
	off_t fl_end;

	void (*fl_notify)(struct file_lock *);	 

	union {
		struct nfs_lock_info	nfs_fl;
	} fl_u;
};

extern struct file_lock			*file_lock_table;

# 1 "/usr/src/linux/include/linux/fcntl.h" 1



# 1 "/usr/src/linux/include/asm/fcntl.h" 1



 

































 


 




 



 






struct flock {
	short l_type;
	short l_whence;
	off_t l_start;
	off_t l_len;
	pid_t l_pid;
};


# 4 "/usr/src/linux/include/linux/fcntl.h" 2



# 477 "/usr/src/linux/include/linux/fs.h" 2


extern int fcntl_getlk(unsigned int fd, struct flock *l);
extern int fcntl_setlk(unsigned int fd, unsigned int cmd, struct flock *l);

 
extern void locks_remove_posix(struct file *, fl_owner_t id);
extern void locks_remove_flock(struct file *);
extern struct file_lock *posix_test_lock(struct file *, struct file_lock *);
extern int posix_lock_file(struct file *, struct file_lock *, unsigned int);
extern void posix_block_lock(struct file_lock *, struct file_lock *);
extern void posix_unblock_lock(struct file_lock *);

struct fasync_struct {
	int    magic;
	int    fa_fd;
	struct fasync_struct	*fa_next;  
	struct file 		*fa_file;
};



extern int fasync_helper(int, struct file *, int, struct fasync_struct **);

# 1 "/usr/src/linux/include/linux/minix_fs_sb.h" 1



 


struct minix_sb_info {
			unsigned long s_ninodes;
			unsigned long s_nzones;
			unsigned long s_imap_blocks;
			unsigned long s_zmap_blocks;
			unsigned long s_firstdatazone;
			unsigned long s_log_zone_size;
			unsigned long s_max_size;
			int s_dirsize;
			int s_namelen;
			int s_link_max;
			struct buffer_head ** s_imap;
			struct buffer_head ** s_zmap;
			struct buffer_head * s_sbh;
			struct minix_super_block * s_ms;
			unsigned short s_mount_state;
			unsigned short s_version;
};


# 501 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/ext2_fs_sb.h" 1
 

















# 1 "/usr/src/linux/include/linux/ext2_fs.h" 1
 



















 



 




 





 





 












 









 


 




 




 






























 













 


struct ext2_acl_header	 
{
	__u32	aclh_size;
	__u32	aclh_file_count;
	__u32	aclh_acle_count;
	__u32	aclh_first_acle;
};

struct ext2_acl_entry	 
{
	__u32	acle_size;
	__u16	acle_perms;	 
	__u16	acle_type;	 
	__u16	acle_tag;	 
	__u16	acle_pad1;
	__u32	acle_next;	 
					 
};

 


struct ext2_group_desc
{
	__u32	bg_block_bitmap;		 
	__u32	bg_inode_bitmap;		 
	__u32	bg_inode_table;		 
	__u16	bg_free_blocks_count;	 
	__u16	bg_free_inodes_count;	 
	__u16	bg_used_dirs_count;	 
	__u16	bg_pad;
	__u32	bg_reserved[3];
};

 













 








 










 




 	






 







 


struct ext2_inode {
	__u16	i_mode;		 
	__u16	i_uid;		 
	__u32	i_size;		 
	__u32	i_atime;	 
	__u32	i_ctime;	 
	__u32	i_mtime;	 
	__u32	i_dtime;	 
	__u16	i_gid;		 
	__u16	i_links_count;	 
	__u32	i_blocks;	 
	__u32	i_flags;	 
	union {
		struct {
			__u32  l_i_reserved1;
		} linux1;
		struct {
			__u32  h_i_translator;
		} hurd1;
		struct {
			__u32  m_i_reserved1;
		} masix1;
	} osd1;				 
	__u32	i_block[(((12   + 1)  + 1)  + 1) ]; 
	__u32	i_version;	 
	__u32	i_file_acl;	 
	__u32	i_dir_acl;	 
	__u32	i_faddr;	 
	union {
		struct {
			__u8	l_i_frag;	 
			__u8	l_i_fsize;	 
			__u16	i_pad1;
			__u32	l_i_reserved2[2];
		} linux2;
		struct {
			__u8	h_i_frag;	 
			__u8	h_i_fsize;	 
			__u16	h_i_mode_high;
			__u16	h_i_uid_high;
			__u16	h_i_gid_high;
			__u32	h_i_author;
		} hurd2;
		struct {
			__u8	m_i_frag;	 
			__u8	m_i_fsize;	 
			__u16	m_pad1;
			__u32	m_i_reserved2[2];
		} masix2;
	} osd2;				 
};


























 





 

















 





 







 


struct ext2_super_block {
	__u32	s_inodes_count;		 
	__u32	s_blocks_count;		 
	__u32	s_r_blocks_count;	 
	__u32	s_free_blocks_count;	 
	__u32	s_free_inodes_count;	 
	__u32	s_first_data_block;	 
	__u32	s_log_block_size;	 
	__s32	s_log_frag_size;	 
	__u32	s_blocks_per_group;	 
	__u32	s_frags_per_group;	 
	__u32	s_inodes_per_group;	 
	__u32	s_mtime;		 
	__u32	s_wtime;		 
	__u16	s_mnt_count;		 
	__s16	s_max_mnt_count;	 
	__u16	s_magic;		 
	__u16	s_state;		 
	__u16	s_errors;		 
	__u16	s_minor_rev_level; 	 
	__u32	s_lastcheck;		 
	__u32	s_checkinterval;	 
	__u32	s_creator_os;		 
	__u32	s_rev_level;		 
	__u16	s_def_resuid;		 
	__u16	s_def_resgid;		 
	 












	__u32	s_first_ino; 		 
	__u16   s_inode_size; 		 
	__u16	s_block_group_nr; 	 
	__u32	s_feature_compat; 	 
	__u32	s_feature_incompat; 	 
	__u32	s_feature_ro_compat; 	 
	__u8	s_uuid[16];		 
	char	s_volume_name[16]; 	 
	char	s_last_mounted[64]; 	 
	__u32	s_algorithm_usage_bitmap;  
	 



	__u8	s_prealloc_blocks;	 
	__u8	s_prealloc_dir_blocks;	 
	__u16	s_padding1;
	__u32	s_reserved[204];	 
};










 








 










 

























 





 




struct ext2_dir_entry {
	__u32	inode;			 
	__u16	rec_len;		 
	__u16	name_len;		 
	char	name[255 ];	 
};

 





struct ext2_dir_entry_2 {
	__u32	inode;			 
	__u16	rec_len;		 
	__u8	name_len;		 
	__u8	file_type;
	char	name[255 ];	 
};

 














 











 
extern long long ext2_max_sizes[];

 



 







 
extern int ext2_permission (struct inode *, int);

 
extern int ext2_group_sparse(int group);
extern int ext2_new_block (const struct inode *, unsigned long,
			   __u32 *, __u32 *, int *);
extern void ext2_free_blocks (const struct inode *, unsigned long,
			      unsigned long);
extern unsigned long ext2_count_free_blocks (struct super_block *);
extern void ext2_check_blocks_bitmap (struct super_block *);
extern struct ext2_group_desc * ext2_get_group_desc(struct super_block * sb,
						    unsigned int block_group,
						    struct buffer_head ** bh);

 
extern unsigned long ext2_count_free (struct buffer_head *, unsigned);

 
extern int ext2_check_dir_entry (const char *, struct inode *,
				 struct ext2_dir_entry_2 *, struct buffer_head *,
				 unsigned long);

 
extern int ext2_read (struct inode *, struct file *, char *, int);
extern int ext2_write (struct inode *, struct file *, char *, int);

 
extern int ext2_sync_file (struct file *, struct dentry *);

 
extern struct inode * ext2_new_inode (const struct inode *, int, int *);
extern void ext2_free_inode (struct inode *);
extern unsigned long ext2_count_free_inodes (struct super_block *);
extern void ext2_check_inodes_bitmap (struct super_block *);

 
extern int ext2_bmap (struct inode *, int);

extern struct buffer_head * ext2_getblk (struct inode *, long, int, int *);
extern struct buffer_head * ext2_bread (struct inode *, int, int, int *);

extern int ext2_getcluster (struct inode * inode, long block);
extern void ext2_read_inode (struct inode *);
extern void ext2_write_inode (struct inode *);
extern void ext2_put_inode (struct inode *);
extern void ext2_delete_inode (struct inode *);
extern int ext2_sync_inode (struct inode *);
extern int ext2_notify_change(struct dentry *, struct iattr *);
extern void ext2_discard_prealloc (struct inode *);

 
extern int ext2_ioctl (struct inode *, struct file *, unsigned int,
		       unsigned long);

 
extern void ext2_release (struct inode *, struct file *);
extern struct dentry *ext2_lookup (struct inode *, struct dentry *);
extern int ext2_create (struct inode *,struct dentry *,int);
extern int ext2_mkdir (struct inode *,struct dentry *,int);
extern int ext2_rmdir (struct inode *,struct dentry *);
extern int ext2_unlink (struct inode *,struct dentry *);
extern int ext2_symlink (struct inode *,struct dentry *,const char *);
extern int ext2_link (struct dentry *, struct inode *, struct dentry *);
extern int ext2_mknod (struct inode *, struct dentry *, int, int);
extern int ext2_rename (struct inode *, struct dentry *,
			struct inode *, struct dentry *);

 
extern void ext2_error (struct super_block *, const char *, const char *, ...)
	__attribute__ ((format (printf, 3, 4)));
extern   void ext2_panic (struct super_block *, const char *,
				   const char *, ...)
	__attribute__ ((noreturn,  format (printf, 3, 4)));
extern void ext2_warning (struct super_block *, const char *, const char *, ...)
	__attribute__ ((format (printf, 3, 4)));
extern void ext2_put_super (struct super_block *);
extern void ext2_write_super (struct super_block *);
extern int ext2_remount (struct super_block *, int *, char *);
extern struct super_block * ext2_read_super (struct super_block *,void *,int);
extern int init_ext2_fs(void);
extern int ext2_statfs (struct super_block *, struct statfs *, int);

 
extern void ext2_truncate (struct inode *);

 



 
extern struct inode_operations ext2_dir_inode_operations;

 
extern struct inode_operations ext2_file_inode_operations;

 
extern struct inode_operations ext2_symlink_inode_operations;




# 19 "/usr/src/linux/include/linux/ext2_fs_sb.h" 2


 



 



 


struct ext2_sb_info {
	unsigned long s_frag_size;	 
	unsigned long s_frags_per_block; 
	unsigned long s_inodes_per_block; 
	unsigned long s_frags_per_group; 
	unsigned long s_blocks_per_group; 
	unsigned long s_inodes_per_group; 
	unsigned long s_itb_per_group;	 
	unsigned long s_db_per_group;	 
	unsigned long s_desc_per_block;	 
	unsigned long s_groups_count;	 
	struct buffer_head * s_sbh;	 
	struct ext2_super_block * s_es;	 
	struct buffer_head ** s_group_desc;
	unsigned short s_loaded_inode_bitmaps;
	unsigned short s_loaded_block_bitmaps;
	unsigned long s_inode_bitmap_number[8 ];
	struct buffer_head * s_inode_bitmap[8 ];
	unsigned long s_block_bitmap_number[8 ];
	struct buffer_head * s_block_bitmap[8 ];
	unsigned long  s_mount_opt;
	unsigned short s_resuid;
	unsigned short s_resgid;
	unsigned short s_mount_state;
	unsigned short s_pad;
	int s_addr_per_block_bits;
	int s_desc_per_block_bits;
	int s_inode_size;
	int s_first_ino;
	int s_feature_compat;
	int s_feature_incompat;
	int s_feature_ro_compat;
};


# 502 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/hpfs_fs_sb.h" 1



struct hpfs_sb_info {
	ino_t sb_root;			 
	unsigned sb_fs_size;		 
	unsigned sb_bitmaps;		 
	unsigned sb_dirband_size;	 
	unsigned sb_dmap;		 
	unsigned sb_n_free;		 
	unsigned sb_n_free_dnodes;	 
	uid_t sb_uid;			 
	gid_t sb_gid;			 
	umode_t sb_mode;		 
	unsigned sb_lowercase : 1;	 
	unsigned sb_conv : 2;		 
};















# 503 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/ntfs_fs_sb.h" 1



struct ntfs_sb_info{
	 
	ntfs_uid_t uid;
	ntfs_gid_t gid;
	ntmode_t umask;
        unsigned int nct;
	void *nls_map;
	unsigned int ngt;
	 
	ntfs_size_t partition_bias;	 
	 
	ntfs_u32 at_standard_information;
	ntfs_u32 at_attribute_list;
	ntfs_u32 at_file_name;
	ntfs_u32 at_volume_version;
	ntfs_u32 at_security_descriptor;
	ntfs_u32 at_volume_name;
	ntfs_u32 at_volume_information;
	ntfs_u32 at_data;
	ntfs_u32 at_index_root;
	ntfs_u32 at_index_allocation;
	ntfs_u32 at_bitmap;
	ntfs_u32 at_symlink;  
	 
	int blocksize;
	int clusterfactor;
	int clustersize;
	int mft_recordsize;
	int mft_clusters_per_record;
	int index_recordsize;
	int index_clusters_per_record;
	int mft_cluster;
	 
	unsigned char *mft;
	unsigned short *upcase;
	unsigned int upcase_length;
	 
	struct ntfs_inode_info *mft_ino;
	struct ntfs_inode_info *mftmirr;
	struct ntfs_inode_info *bitmap;
	struct super_block *sb;
};


# 504 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/msdos_fs_sb.h" 1


# 1 "/usr/src/linux/include/linux/fat_cvf.h" 1





struct cvf_format
{ int cvf_version;
  char* cvf_version_text;
  unsigned long flags;
  int (*detect_cvf) (struct super_block*sb);
  int (*mount_cvf) (struct super_block*sb,char*options);
  int (*unmount_cvf) (struct super_block*sb);
  struct buffer_head* (*cvf_bread) (struct super_block*sb,int block);
  struct buffer_head* (*cvf_getblk) (struct super_block*sb,int block);
  void (*cvf_brelse) (struct super_block *sb,struct buffer_head *bh);
  void (*cvf_mark_buffer_dirty) (struct super_block *sb,
                              struct buffer_head *bh,
                              int dirty_val);
  void (*cvf_set_uptodate) (struct super_block *sb,
                         struct buffer_head *bh,
                         int val);
  int (*cvf_is_uptodate) (struct super_block *sb,struct buffer_head *bh);
  void (*cvf_ll_rw_block) (struct super_block *sb,
                        int opr,
                        int nbreq,
                        struct buffer_head *bh[32]);
  int (*fat_access) (struct super_block *sb,int nr,int new_value);
  int (*cvf_statfs) (struct super_block *sb,struct statfs *buf, int bufsiz);
  int (*cvf_bmap) (struct inode *inode,int block);
  int (*cvf_smap) (struct inode *inode,int sector);
  ssize_t (*cvf_file_read) ( struct file *, char *, size_t, loff_t *);
  ssize_t (*cvf_file_write) ( struct file *, const char *, size_t, loff_t *);
  int (*cvf_mmap) (struct file *, struct vm_area_struct *);
  int (*cvf_readpage) (struct inode *, struct page *);
  int (*cvf_writepage) (struct inode *, struct page *);
  int (*cvf_dir_ioctl) (struct inode * inode, struct file * filp,
                        unsigned int cmd, unsigned long arg);
  void (*zero_out_cluster) (struct inode*, int clusternr);
};

int register_cvf_format(struct cvf_format*cvf_format);
int unregister_cvf_format(struct cvf_format*cvf_format);
void dec_cvf_format_use_count_by_version(int version);
int detect_cvf(struct super_block*sb,char*force);

extern struct cvf_format *cvf_formats[];
extern int cvf_format_use_count[];


# 3 "/usr/src/linux/include/linux/msdos_fs_sb.h" 2


 



struct fat_mount_options {
	uid_t fs_uid;
	gid_t fs_gid;
	unsigned short fs_umask;
	unsigned short codepage;   
	char *iocharset;           
	unsigned char name_check;  
	unsigned char conversion;  
	unsigned quiet:1,          
		 showexec:1,       
		 sys_immutable:1,  
		 dotsOK:1,         
		 isvfat:1,         
		 utf8:1,	   
		 unicode_xlate:1,  
		 posixfs:1,        
		 numtail:1,        
		 atari:1,          
		 fat32:1;	   
};

struct vfat_unicode {
	unsigned char uni1;
	unsigned char uni2;
};

struct msdos_sb_info {
	unsigned short cluster_size;  
	unsigned char fats,fat_bits;  
	unsigned short fat_start;
	unsigned long fat_length;     
	unsigned long dir_start;
	unsigned short dir_entries;   
	unsigned long data_start;     
	unsigned long clusters;       
	unsigned long root_cluster;   
	unsigned long fsinfo_offset;  
	struct wait_queue *fat_wait;
	int fat_lock;
	int prev_free;                
	int free_clusters;            
	struct fat_mount_options options;
	struct nls_table *nls_disk;   
	struct nls_table *nls_io;     
	struct cvf_format* cvf_format;
	void *dir_ops;		      
	void (*put_super_callback)(struct super_block *);
	void *private_data;	
};


# 505 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/iso_fs_sb.h" 1



 


struct isofs_sb_info {
	unsigned long s_ninodes;
	unsigned long s_nzones;
	unsigned long s_firstdatazone;
	unsigned long s_log_zone_size;
	unsigned long s_max_size;
	
	unsigned char s_high_sierra;  
	unsigned char s_mapping;
	unsigned char s_rock;
	unsigned char s_joliet_level;
	unsigned char s_utf8;
	unsigned char s_cruft;  


	unsigned char s_unhide;
	unsigned char s_nosuid;
	unsigned char s_nodev;
	mode_t s_mode;
	gid_t s_gid;
	uid_t s_uid;
	struct nls_table *s_nls_iocharset;  
};


# 506 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/nfs_fs_sb.h" 1




# 1 "/usr/src/linux/include/linux/in.h" 1
 





















 
enum {
  IPPROTO_IP = 0,		 
  IPPROTO_ICMP = 1,		 
  IPPROTO_IGMP = 2,		 
  IPPROTO_IPIP = 4,		 
  IPPROTO_TCP = 6,		 
  IPPROTO_EGP = 8,		 
  IPPROTO_PUP = 12,		 
  IPPROTO_UDP = 17,		 
  IPPROTO_IDP = 22,		 
  IPPROTO_RSVP = 46,		 
  IPPROTO_GRE = 47,		 

  IPPROTO_IPV6	 = 41,		 

  IPPROTO_PIM    = 103,		 

  IPPROTO_ESP = 50,             
  IPPROTO_AH = 51,              
  IPPROTO_COMP   = 108,                 

  IPPROTO_RAW	 = 255,		 
  IPPROTO_MAX
};


 
struct in_addr {
	__u32	s_addr;
};
















 


 










 



 

struct ip_mreq 
{
	struct in_addr imr_multiaddr;	 
	struct in_addr imr_interface;	 
};

struct ip_mreqn
{
	struct in_addr	imr_multiaddr;		 
	struct in_addr	imr_address;		 
	int		imr_ifindex;		 
};

struct in_pktinfo
{
	int		ipi_ifindex;
	struct in_addr	ipi_spec_dst;
	struct in_addr	ipi_addr;
};

 

struct sockaddr_in {
  sa_family_t		sin_family;	 
  unsigned short int	sin_port;	 
  struct in_addr	sin_addr;	 

   
  unsigned char		__pad[16  - sizeof(short int) -
			sizeof(unsigned short int) - sizeof(struct in_addr)];
};



 




























 


 


 


 


 



 






 



 









# 5 "/usr/src/linux/include/linux/nfs_fs_sb.h" 2


 


struct nfs_server {
	struct rpc_clnt *	client;		 
	int			flags;		 
	int			rsize;		 
	int			wsize;		 
	unsigned int		bsize;		 
	unsigned int		acregmin;	 
	unsigned int		acregmax;
	unsigned int		acdirmin;
	unsigned int		acdirmax;
	char *			hostname;	 
};

 


struct nfs_sb_info {
	struct nfs_server	s_server;
	struct nfs_fh		s_root;
};


# 507 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/sysv_fs_sb.h" 1



 








struct sysv_sb_info {
	int	       s_type;		 
	unsigned int   s_block_size;	 
	unsigned int   s_block_size_1;	 
	unsigned int   s_block_size_bits;	 
	unsigned int   s_block_size_inc_bits;	 
	unsigned int   s_block_size_dec_bits;	 
	char	       s_convert;	 
	char	       s_kludge_symlinks;  
	char	       s_truncate;	 
					 
	nlink_t        s_link_max;	 
	unsigned int   s_inodes_per_block;	 
	unsigned int   s_inodes_per_block_1;	 
	unsigned int   s_inodes_per_block_bits;	 
	unsigned int   s_ind_per_block;		 
	unsigned int   s_ind_per_block_1;	 
	unsigned int   s_ind_per_block_bits;	 
	unsigned int   s_ind_per_block_2;	 
	unsigned int   s_ind_per_block_2_1;	 
	unsigned int   s_ind_per_block_2_bits;	 
	unsigned int   s_ind_per_block_3;	 
	unsigned int   s_ind_per_block_block_size_1;	 
	unsigned int   s_ind_per_block_block_size_bits;	 
	unsigned int   s_ind_per_block_2_block_size_1;	 
	unsigned int   s_ind_per_block_2_block_size_bits;  
	unsigned int   s_ind0_size;		 
	unsigned int   s_ind1_size;		 
	unsigned int   s_ind2_size;		 
	unsigned int   s_toobig_block;		 
	unsigned int   s_block_base;	 
	unsigned short s_fic_size;	 
	unsigned short s_flc_size;	 
	 
	struct buffer_head *s_bh1;
	struct buffer_head *s_bh2;
	 

	char *         s_sbd1;		 
	char *         s_sbd2;		 
	u16            *s_sb_fic_count;	 
        u16            *s_sb_fic_inodes;  
	u16            *s_sb_total_free_inodes;  
	u16            *s_sb_flc_count;	 
	u32	       *s_sb_flc_blocks;  
	u32            *s_sb_total_free_blocks; 
	u32            *s_sb_time;	 
	u32            *s_sb_state;	 
	 

	u32            s_firstinodezone;  
	u32            s_firstdatazone;	 
	u32            s_ninodes;	 
	u32            s_ndatazones;	 
	u32            s_nzones;	 
};
 

 



















































# 508 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/affs_fs_sb.h" 1



 











struct affs_bm_info {
	struct buffer_head *bm_bh;	 
	s32 bm_firstblk;		 
	s32 bm_key;			 
	int bm_count;			 
};

struct affs_alloc_zone {
	short az_size;			 
	short az_count;			 
	int az_free;			 
};

struct affs_zone {
	unsigned long z_ino;		 
	struct affs_bm_info *z_bm;	 
	int z_start;			 
	int z_end;			 
	int z_az_no;			 
	unsigned long z_lru_time;	 
};

struct affs_sb_info {
	int s_partition_size;		 
	int s_blksize;			 
	s32 s_root_block;		 
	int s_hashsize;			 
	unsigned long s_flags;		 
	s16 s_uid;			 
	s16 s_gid;			 
	umode_t s_mode;			 
	int s_reserved;			 
	struct buffer_head *s_root_bh;	 
	struct affs_bm_info *s_bitmap;	 
	int s_bm_count;			 
	int s_nextzone;			 
	int s_num_az;			 
	struct affs_zone *s_zones;	 
	struct affs_alloc_zone *s_alloc; 
	char *s_zonemap;		 
	char *s_prefix;			 
	int s_prefix_len;		 
	char s_volume[32];		 
};















# 509 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/ufs_fs_sb.h" 1
 















# 1 "/usr/src/linux/include/linux/ufs_fs.h" 1
 




































































 
 


 







 



 




 





 





 



 



















 













            
 






 










 










 






 










 





















 







struct ufs_timeval {
	__s32	tv_sec;
	__s32	tv_usec;
};

 











   
struct ufs_dir_entry {
	__u32  d_ino;			 
	__u16  d_reclen;		 
	union {
		__u16	d_namlen;		 
		struct {
			__u8	d_type;		 
			__u8	d_namlen;	 
		} d_44;
	} d_u;
	__u8	d_name[255  + 1];	 
};

struct ufs_csum {
	__u32	cs_ndir;	 
	__u32	cs_nbfree;	 
	__u32	cs_nifree;	 
	__u32	cs_nffree;	 
};

 


struct ufs_super_block {
	__u32	fs_link;	 
	__u32	fs_rlink;	 
	__u32	fs_sblkno;	 
	__u32	fs_cblkno;	 
	__u32	fs_iblkno;	 
	__u32	fs_dblkno;	 
	__u32	fs_cgoffset;	 
	__u32	fs_cgmask;	 
	__u32	fs_time;	 
	__u32	fs_size;	 
	__u32	fs_dsize;	 
	__u32	fs_ncg;		 
	__u32	fs_bsize;	 
	__u32	fs_fsize;	 
	__u32	fs_frag;	 
 
	__u32	fs_minfree;	 
	__u32	fs_rotdelay;	 
	__u32	fs_rps;		 
 
	__u32	fs_bmask;	 
	__u32	fs_fmask;	 
	__u32	fs_bshift;	 
	__u32	fs_fshift;	 
 
	__u32	fs_maxcontig;	 
	__u32	fs_maxbpg;	 
 
	__u32	fs_fragshift;	 
	__u32	fs_fsbtodb;	 
	__u32	fs_sbsize;	 
	__u32	fs_csmask;	 
	__u32	fs_csshift;	 
	__u32	fs_nindir;	 
	__u32	fs_inopb;	 
	__u32	fs_nspf;	 
 
	__u32	fs_optim;	 
 
	union {
		struct {
			__u32	fs_npsect;	 
		} fs_sun;
		struct {
			__s32	fs_state;	 
		} fs_sunx86;
	} fs_u1;
	__u32	fs_interleave;	 
	__u32	fs_trackskew;	 
 
 
 
 
	__u32	fs_id[2];	 
 
	__u32	fs_csaddr;	 
	__u32	fs_cssize;	 
	__u32	fs_cgsize;	 
 
	__u32	fs_ntrak;	 
	__u32	fs_nsect;	 
	__u32	fs_spc;		 
 
	__u32	fs_ncyl;	 
 
	__u32	fs_cpg;		 
	__u32	fs_ipg;		 
	__u32	fs_fpg;		 
 
	struct ufs_csum fs_cstotal;	 
 
	__s8	fs_fmod;	 
	__s8	fs_clean;	 
	__s8	fs_ronly;	 
	__s8	fs_flags;	 
	__s8	fs_fsmnt[512 ];	 
 
	__u32	fs_cgrotor;	 
	__u32	fs_csp[31 ];	 
	__u32	fs_maxcluster;
	__u32	fs_cpc;		 
	__u16	fs_opostbl[16][8];	 	
	union {
		struct {
			__s32	fs_sparecon[53]; 
			__s32	fs_reclaim;
			__s32	fs_sparecon2[1];
			__s32	fs_state;	 
			__u32	fs_qbmask[2];	 
			__u32	fs_qfmask[2];	 
		} fs_sun;
		struct {
			__s32	fs_sparecon[53]; 
			__s32	fs_reclaim;
			__s32	fs_sparecon2[1];
			__u32	fs_npsect;	 
			__u32	fs_qbmask[2];	 
			__u32	fs_qfmask[2];	 
		} fs_sunx86;
		struct {
			__s32	fs_sparecon[50]; 
			__s32	fs_contigsumsize; 
			__s32	fs_maxsymlinklen; 
			__s32	fs_inodefmt;	 
			__u32	fs_maxfilesize[2];	 
			__u32	fs_qbmask[2];	 
			__u32	fs_qfmask[2];	 
			__s32	fs_state;	 
		} fs_44;
	} fs_u2;
	__s32	fs_postblformat;	 
	__s32	fs_nrpos;		 
	__s32	fs_postbloff;		 
	__s32	fs_rotbloff;		 
	__s32	fs_magic;		 
	__u8	fs_space[1];		 
};

 





 





 





 








 


struct	ufs_cylinder_group {
	__u32	cg_link;		 
	__u32	cg_magic;		 
	__u32	cg_time;		 
	__u32	cg_cgx;			 
	__u16	cg_ncyl;		 
	__u16	cg_niblk;		 
	__u32	cg_ndblk;		 
	struct	ufs_csum cg_cs;		 
	__u32	cg_rotor;		 
	__u32	cg_frotor;		 
	__u32	cg_irotor;		 
	__u32	cg_frsum[(8192  / 1024 ) ];	 
	__u32	cg_btotoff;		 
	__u32	cg_boff;		 
	__u32	cg_iusedoff;		 
	__u32	cg_freeoff;		 
	__u32	cg_nextfreeoff;		 
	union {
		struct {
			__u32	cg_clustersumoff;	 
			__u32	cg_clusteroff;		 
			__u32	cg_nclusterblks;	 
			__u32	cg_sparecon[13];	 
		} cg_44;
		__u32	cg_sparecon[16];	 
	} cg_u;
	__u8	cg_space[1];		 
 
};

 


struct ufs_inode {
	__u16	ui_mode;		 
	__u16	ui_nlink;		 
	union {
		struct {
			__u16	ui_suid;	 
			__u16	ui_sgid;	 
		} oldids;
		__u32	ui_inumber;		 
		__u32	ui_author;		 
	} ui_u1;
	__u64	ui_size;		 
	struct ufs_timeval ui_atime;	 
	struct ufs_timeval ui_mtime;	 
	struct ufs_timeval ui_ctime;	 
	union {
		struct {
			__u32	ui_db[12 ]; 
			__u32	ui_ib[3 ]; 
		} ui_addr;
		__u8	ui_symlink[4*(12 + 3 )]; 
	} ui_u2;
	__u32	ui_flags;		 
	__u32	ui_blocks;		 
	__u32	ui_gen;			 
	union {
		struct {
			__u32	ui_shadow;	 
			__u32	ui_uid;		 
			__u32	ui_gid;		 
			__u32	ui_oeftflag;	 
		} ui_sun;
		struct {
			__u32	ui_uid;		 
			__u32	ui_gid;		 
			__s32	ui_spare[2];	 
		} ui_44;
		struct {
			__u32	ui_uid;		 
			__u32	ui_gid;		 
			__u16	ui_modeh;	 
			__u16	ui_spare;	 
			__u32	ui_trans;	 
		} ui_hurd;
	} ui_u3;
};

 
 






 








 
extern int ufs_permission (struct inode *, int);

 
extern void ufs_free_fragments (struct inode *, unsigned, unsigned);
extern void ufs_free_blocks (struct inode *, unsigned, unsigned);
extern unsigned ufs_new_fragments (struct inode *, u32 *, unsigned, unsigned, unsigned, int *);

 
extern struct ufs_cg_private_info * ufs_load_cylinder (struct super_block *, unsigned);
extern void ufs_put_cylinder (struct super_block *, unsigned);

 
extern struct inode_operations ufs_dir_inode_operations;
extern struct file_operations ufs_dir_operations;
extern int ufs_check_dir_entry (const char *, struct inode *, struct ufs_dir_entry *, struct buffer_head *, unsigned long);

 
extern struct inode_operations ufs_file_inode_operations;
extern struct file_operations ufs_file_operations;

 
extern void ufs_free_inode (struct inode *inode);
extern struct inode * ufs_new_inode (const struct inode *, int, int *);

 
extern int ufs_bmap (struct inode *, int);
extern void ufs_read_inode (struct inode *);
extern void ufs_put_inode (struct inode *);
extern void ufs_write_inode (struct inode *);
extern int ufs_sync_inode (struct inode *);
extern void ufs_write_inode (struct inode *);
extern void ufs_delete_inode (struct inode *);
extern struct buffer_head * ufs_getfrag (struct inode *, unsigned, int, int *);
extern struct buffer_head * ufs_bread (struct inode *, unsigned, int, int *);

 
extern struct dentry *ufs_lookup (struct inode *, struct dentry *);
extern int ufs_mkdir(struct inode *, struct dentry *, int);
extern int ufs_rmdir (struct inode *, struct dentry *);
extern int ufs_unlink (struct inode *, struct dentry *);
extern int ufs_create (struct inode *, struct dentry *, int);
extern int ufs_rename (struct inode *, struct dentry *, struct inode *, struct dentry *);
extern int ufs_mknod (struct inode *, struct dentry *, int, int);
extern int ufs_symlink (struct inode *, struct dentry *, const char *);
extern int ufs_link (struct dentry *, struct inode *, struct dentry *);
        
 
extern struct super_operations ufs_super_ops;
extern struct file_system_type ufs_fs_type;
extern void ufs_warning (struct super_block *, const char *, const char *, ...) __attribute__ ((format (printf, 3, 4)));
extern void ufs_error (struct super_block *, const char *, const char *, ...) __attribute__ ((format (printf, 3, 4)));
extern void ufs_panic (struct super_block *, const char *, const char *, ...) __attribute__ ((format (printf, 3, 4)));
extern int init_ufs_fs(void);
extern void ufs_write_super (struct super_block *);

 
extern struct inode_operations ufs_symlink_inode_operations;

 
extern void ufs_truncate (struct inode *);




# 17 "/usr/src/linux/include/linux/ufs_fs_sb.h" 2


 



struct ufs_buffer_head {
	unsigned fragment;			 
	unsigned count;				 
	struct buffer_head * bh[(8192  / 1024 ) ];	 
};

struct ufs_cg_private_info {
	struct ufs_cylinder_group ucg;
	__u32	c_cgx;		 
	__u16	c_ncyl;		 
	__u16	c_niblk;	 
	__u32	c_ndblk;	 
	__u32	c_rotor;	 
	__u32	c_frotor;	 
	__u32	c_irotor;	 
	__u32	c_btotoff;	 
	__u32	c_boff;		 
	__u32	c_iusedoff;	 
	__u32	c_freeoff;	 
	__u32	c_nextfreeoff;	 
	__u32	c_clustersumoff; 
	__u32	c_clusteroff;	 
	__u32	c_nclusterblks;	 
};	

struct ufs_sb_private_info {
	struct ufs_buffer_head s_ubh;  
	__u32	s_sblkno;	 
	__u32	s_cblkno;	 
	__u32	s_iblkno;	 
	__u32	s_dblkno;	 
	__u32	s_cgoffset;	 
	__u32	s_cgmask;	 
	__u32	s_size;		 
	__u32	s_dsize;	 
	__u32	s_ncg;		 
	__u32	s_bsize;	 
	__u32	s_fsize;	 
	__u32	s_fpb;		 
	__u32	s_minfree;	 
	__u32	s_bmask;	 
	__u32	s_fmask;	 
	__u32	s_bshift;	 
	__u32   s_fshift;	 
	__u32	s_fpbshift;	 
	__u32	s_fsbtodb;	 
	__u32	s_sbsize;	 
	__u32   s_csmask;	 
	__u32	s_csshift;	 
	__u32	s_nindir;	 
	__u32	s_inopb;	 
	__u32	s_nspf;		 
	__u32	s_npsect;	 
	__u32	s_interleave;	 
	__u32	s_trackskew;	 
	__u32	s_csaddr;	 
	__u32	s_cssize;	 
	__u32	s_cgsize;	 
	__u32	s_ntrak;	 
	__u32	s_nsect;	 
	__u32	s_spc;		 
	__u32	s_ipg;		 
	__u32	s_fpg;		 
	__u32	s_cpc;		 
	__s32	s_contigsumsize; 
	__s64	s_qbmask;	 
	__s64	s_qfmask;	 
	__s32	s_postblformat;	 
	__s32	s_nrpos;	 
        __s32	s_postbloff;	 
	__s32	s_rotbloff;	 

	__u32	s_fpbmask;	 
	__u32	s_apb;		 
	__u32	s_2apb;		 
	__u32	s_3apb;		 
	__u32	s_apbmask;	 
	__u32	s_apbshift;	 
	__u32	s_2apbshift;	 
	__u32	s_3apbshift;	 
	__u32	s_nspfshift;	 
	__u32	s_nspb;		 
	__u32	s_inopf;	 
	__u32	s_sbbase;	 
	__u32	s_bpf;		 
	__u32	s_bpfshift;	 
	__u32	s_bpfmask;	 
};





struct ufs_sb_info {
	struct ufs_sb_private_info * s_uspi;	
	struct ufs_csum	* s_csp[31 ];
	unsigned s_swab;
	unsigned s_flags;
	struct buffer_head ** s_ucg;
	struct ufs_cg_private_info * s_ucpi[8 ]; 
	unsigned s_cgno[8 ];
	unsigned short s_cg_loaded;
	unsigned s_mount_opt;
};

 





struct ufs_super_block_first {
	__u32	fs_link;
	__u32	fs_rlink;
	__u32	fs_sblkno;
	__u32	fs_cblkno;
	__u32	fs_iblkno;
	__u32	fs_dblkno;
	__u32	fs_cgoffset;
	__u32	fs_cgmask;
	__u32	fs_time;
	__u32	fs_size;
	__u32	fs_dsize;
	__u32	fs_ncg;
	__u32	fs_bsize;
	__u32	fs_fsize;
	__u32	fs_frag;
	__u32	fs_minfree;
	__u32	fs_rotdelay;
	__u32	fs_rps;
	__u32	fs_bmask;
	__u32	fs_fmask;
	__u32	fs_bshift;
	__u32	fs_fshift;
	__u32	fs_maxcontig;
	__u32	fs_maxbpg;
	__u32	fs_fragshift;
	__u32	fs_fsbtodb;
	__u32	fs_sbsize;
	__u32	fs_csmask;
	__u32	fs_csshift;
	__u32	fs_nindir;
	__u32	fs_inopb;
	__u32	fs_nspf;
	__u32	fs_optim;
	union {
		struct {
			__u32	fs_npsect;
		} fs_sun;
		struct {
			__s32	fs_state;
		} fs_sunx86;
	} fs_u1;
	__u32	fs_interleave;
	__u32	fs_trackskew;
	__u32	fs_id[2];
	__u32	fs_csaddr;
	__u32	fs_cssize;
	__u32	fs_cgsize;
	__u32	fs_ntrak;
	__u32	fs_nsect;
	__u32	fs_spc;
	__u32	fs_ncyl;
	__u32	fs_cpg;
	__u32	fs_ipg;
	__u32	fs_fpg;
	struct ufs_csum fs_cstotal;
	__s8	fs_fmod;
	__s8	fs_clean;
	__s8	fs_ronly;
	__s8	fs_flags;
	__s8	fs_fsmnt[512  - 212];

};

struct ufs_super_block_second {
	__s8	fs_fsmnt[212];
	__u32	fs_cgrotor;
	__u32	fs_csp[31 ];
	__u32	fs_maxcluster;
	__u32	fs_cpc;
	__u16	fs_opostbl[82];
};	

struct ufs_super_block_third {
	__u16	fs_opostbl[46];
	union {
		struct {
			__s32	fs_sparecon[53]; 
			__s32	fs_reclaim;
			__s32	fs_sparecon2[1];
			__s32	fs_state;	 
			__u32	fs_qbmask[2];	 
			__u32	fs_qfmask[2];	 
		} fs_sun;
		struct {
			__s32	fs_sparecon[53]; 
			__s32	fs_reclaim;
			__s32	fs_sparecon2[1];
			__u32	fs_npsect;	 
			__u32	fs_qbmask[2];	 
			__u32	fs_qfmask[2];	 
		} fs_sunx86;
		struct {
			__s32	fs_sparecon[50]; 
			__s32	fs_contigsumsize; 
			__s32	fs_maxsymlinklen; 
			__s32	fs_inodefmt;	 
			__u32	fs_maxfilesize[2];	 
			__u32	fs_qbmask[2];	 
			__u32	fs_qfmask[2];	 
			__s32	fs_state;	 
		} fs_44;
	} fs_u2;
	__s32	fs_postblformat;
	__s32	fs_nrpos;
	__s32	fs_postbloff;
	__s32	fs_rotbloff;
	__s32	fs_magic;
	__u8	fs_space[1];
};


# 510 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/efs_fs_sb.h" 1
 










 


 








 
struct efs_super {
	int32_t		fs_size;         
	int32_t		fs_firstcg;      
	int32_t		fs_cgfsize;      
	short		fs_cgisize;      
	short		fs_sectors;      
	short		fs_heads;        
	short		fs_ncg;          
	short		fs_dirty;        
	short		fs_filler;	 
	int32_t		fs_time;         
	int32_t		fs_magic;        
	char		fs_fname[6];     
	char		fs_fpack[6];     
	int32_t		fs_bmsize;       
	int32_t		fs_tfree;        
	int32_t		fs_tinode;       
	int32_t		fs_bmblock;      
	int32_t		fs_replsb;       
	int32_t		fs_lastialloc;   
	char		fs_spare[20];    
	int32_t		fs_checksum;     
};

 
struct efs_sb_info {
	int32_t	fs_magic;	 
	int32_t	fs_start;	 
	int32_t	first_block;	 
	int32_t	total_blocks;	 
	int32_t	group_size;	  
	int32_t	data_free;	 
	int32_t	inode_free;	 
	short	inode_blocks;	 
	short	total_groups;	 
};



# 511 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/romfs_fs_sb.h" 1



 

struct romfs_sb_info {
	unsigned long s_maxsize;
};


# 512 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/smb_fs_sb.h" 1
 













# 1 "/usr/src/linux/include/linux/smb.h" 1
 












enum smb_protocol { 
	SMB_PROTOCOL_NONE, 
	SMB_PROTOCOL_CORE, 
	SMB_PROTOCOL_COREPLUS, 
	SMB_PROTOCOL_LANMAN1, 
	SMB_PROTOCOL_LANMAN2, 
	SMB_PROTOCOL_NT1 
};

enum smb_case_hndl {
	SMB_CASE_DEFAULT,
	SMB_CASE_LOWER,
	SMB_CASE_UPPER
};

struct smb_dskattr {
        __u16 total;
        __u16 allocblocks;
        __u16 blocksize;
        __u16 free;
};

struct smb_conn_opt {

         
	unsigned int fd;

	enum smb_protocol protocol;
	enum smb_case_hndl case_handling;

	 

	__u32              max_xmit;
	__u16              server_uid;
	__u16              tid;

         
        __u16              secmode;
        __u16              maxmux;
        __u16              maxvcs;
        __u16              rawmode;
        __u32              sesskey;

	 
	__u32              maxraw;
	__u32              capabilities;
	__s16              serverzone;
};






 


struct smb_fattr {

	__u16 attr;

	unsigned long	f_ino;
	umode_t		f_mode;
	nlink_t		f_nlink;
	uid_t		f_uid;
	gid_t		f_gid;
	kdev_t		f_rdev;
	off_t		f_size;
	time_t		f_atime;
	time_t		f_mtime;
	time_t		f_ctime;
	unsigned long	f_blksize;
	unsigned long	f_blocks;
};

struct smb_dirent {
	struct smb_fattr attr;

	int f_pos;
	int len;
	__u8 name[255 ];
};

enum smb_conn_state {
        CONN_VALID,              
        CONN_INVALID,            

        CONN_RETRIED             
};

 














 




# 15 "/usr/src/linux/include/linux/smb_fs_sb.h" 2


 




struct smb_sb_info {
        enum smb_conn_state state;
	struct file * sock_file;

        struct smb_mount_data *mnt;
        unsigned char *temp_buf;

	 


	unsigned int generation;
	pid_t conn_pid;
	struct smb_conn_opt opt;

	struct semaphore sem;
	struct wait_queue * wait;

	__u32              packet_size;
	unsigned char *    packet;
        unsigned short     rcls;  
        unsigned short     err;

         
        void *data_ready;
};




# 513 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/hfs_fs_sb.h" 1
 












 
struct hfs_name;

typedef int (*hfs_namein_fn) (char *, const struct hfs_name *);
typedef void (*hfs_nameout_fn) (struct hfs_name *, const char *, int);
typedef void (*hfs_ifill_fn) (struct inode *, ino_t, const int);

 




struct hfs_sb_info {
	int			magic;		 
	struct hfs_mdb		*s_mdb;		 
	int			s_quiet;	 

	int			s_lowercase;	 
	int			s_afpd;		 
	int                     s_version;       
	hfs_namein_fn		s_namein;	 


	hfs_nameout_fn		s_nameout;	 


	hfs_ifill_fn		s_ifill;	 

	const struct hfs_name	*s_reserved1;	 
	const struct hfs_name	*s_reserved2;	 
	__u32			s_type;		 
	__u32			s_creator;	 
	umode_t			s_umask;	 

	uid_t			s_uid;		 
	gid_t			s_gid;		 
	char			s_conv;		 
};


# 514 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/adfs_fs_sb.h" 1
 








# 1 "/usr/src/linux/include/linux/adfs_fs.h" 1




 



 


struct adfs_discrecord {
    unsigned char  log2secsize;
    unsigned char  secspertrack;
    unsigned char  heads;
    unsigned char  density;
    unsigned char  idlen;
    unsigned char  log2bpmb;
    unsigned char  skew;
    unsigned char  bootoption;
    unsigned char  lowsector;
    unsigned char  nzones;
    unsigned short zone_spare;
    unsigned long  root;
    unsigned long  disc_size;
    unsigned short disc_id;
    unsigned char  disc_name[10];
    unsigned long  disc_type;
    unsigned long  disc_size_high;
    unsigned char  log2sharesize:4;
    unsigned char  unused:4;
    unsigned char  big_flag:1;
};









 


struct adfs_dirheader {
	unsigned char startmasseq;
	unsigned char startname[4];
};





 


struct adfs_direntry {
	char dirobname[10];

	__u8 dirload[4];
	__u8 direxec[4];
	__u8 dirlen[4];
	__u8 dirinddiscadd[3];
	__u8 newdiratts;







};


struct adfs_idir_entry {
	__u32		inode_no;			 
	__u32		file_id;			 
	__u32		name_len;			 
	__u32		size;				 
	__u32		mtime;				 
	__u32		filetype;			 
	__u8		mode;				 
	char		name[255 ];	 
};

 


union adfs_dirtail {
	struct {
		unsigned char dirlastmask;
		char dirname[10];
		unsigned char dirparent[3];
		char dirtitle[19];
		unsigned char reserved[14];
		unsigned char endmasseq;
		unsigned char endname[4];
		unsigned char dircheckbyte;
	} old;
	struct {
		unsigned char dirlastmask;
		unsigned char reserved[2];
		unsigned char dirparent[3];
		char dirtitle[19];
		char dirname[10];
		unsigned char endmasseq;
		unsigned char endname[4];
		unsigned char dircheckbyte;
	} new;
};


 




extern inline int adfs_checkbblk(unsigned char *ptr)
{
	unsigned int result = 0;
	unsigned char *p = ptr + 511;

	do {
	        result = (result & 0xff) + (result >> 8);
        	result = result + *--p;
	} while (p != ptr);

	return (result & 0xff) != ptr[511];
}

 
extern unsigned int adfs_val (unsigned char *p, int len);
extern int adfs_dir_read_parent (struct inode *inode, struct buffer_head **bhp);
extern int adfs_dir_read (struct inode *inode, struct buffer_head **bhp);
extern int adfs_dir_check (struct inode *inode, struct buffer_head **bhp,
			   int buffers, union adfs_dirtail *dtp);
extern void adfs_dir_free (struct buffer_head **bhp, int buffers);
extern int adfs_dir_get (struct super_block *sb, struct buffer_head **bhp,
			 int buffers, int pos, unsigned long parent_object_id,
			 struct adfs_idir_entry *ide);
extern int adfs_dir_find_entry (struct super_block *sb, struct buffer_head **bhp,
				int buffers, unsigned int index,
				struct adfs_idir_entry *ide);

 
extern int adfs_inode_validate (struct inode *inode);
extern unsigned long adfs_inode_generate (unsigned long parent_id, int diridx);
extern unsigned long adfs_inode_objid (struct inode *inode);
extern unsigned int adfs_parent_bmap (struct inode *inode, int block);
extern int adfs_bmap (struct inode *inode, int block);
extern void adfs_read_inode (struct inode *inode);

 
extern int adfs_map_lookup (struct super_block *sb, int frag_id, int offset);

 
extern struct dentry *adfs_lookup (struct inode *dir, struct dentry *dentry);

 
extern int init_adfs_fs (void);
extern void adfs_error (struct super_block *, const char *, const char *, ...);

 



 
extern struct inode_operations adfs_dir_inode_operations;

 
extern struct inode_operations adfs_file_inode_operations;



# 10 "/usr/src/linux/include/linux/adfs_fs_sb.h" 2


 


struct adfs_sb_info {
	struct buffer_head *s_sbh;	 
	struct adfs_discrecord *s_dr;	 
	uid_t	s_uid;			 
	gid_t	s_gid;			 
	int	s_owner_mask;		 
	int	s_other_mask;		 
	__u16	s_zone_size;		 
	__u16	s_ids_per_zone;		 
	__u32	s_idlen;		 
	__u32	s_map_size;		 
	__u32	s_zonesize;		 
	__u32	s_map_block;		 
	struct buffer_head **s_map;	 
	__u32	s_root;			 
	__s8	s_map2blk;		 
};


# 515 "/usr/src/linux/include/linux/fs.h" 2

# 1 "/usr/src/linux/include/linux/qnx4_fs_sb.h" 1
 












# 1 "/usr/src/linux/include/linux/qnx4_fs.h" 1
 
















 



















 



 


struct qnx4_inode_entry {
	char		di_fname[16 ];
	qnx4_off_t	di_size;
	qnx4_xtnt_t	di_first_xtnt;
	__u32		di_xblk;
	__s32		di_ftime;
	__s32		di_mtime;
	__s32		di_atime;
	__s32		di_ctime;
	qnx4_nxtnt_t	di_num_xtnts;
	qnx4_mode_t	di_mode;
	qnx4_muid_t	di_uid;
	qnx4_mgid_t	di_gid;
	qnx4_nlink_t	di_nlink;
	__u8		di_zero[4];
	qnx4_ftype_t	di_type;
	__u8		di_status;
};

struct qnx4_link_info {
	char		dl_fname[48 ];
	__u32		dl_inode_blk;
	__u8		dl_inode_ndx;
	__u8		dl_spare[10];
	__u8		dl_status;
};

struct qnx4_xblk {
	__u32		xblk_next_xblk;
	__u32		xblk_prev_xblk;
	__u8		xblk_num_xtnts;
	__u8		xblk_spare[3];
	__s32		xblk_num_blocks;
	qnx4_xtnt_t	xblk_xtnts[60 ];
	char		xblk_signature[8];
	qnx4_xtnt_t	xblk_first_xtnt;
};

struct qnx4_super_block {
	struct qnx4_inode_entry RootDir;
	struct qnx4_inode_entry Inode;
	struct qnx4_inode_entry Boot;
	struct qnx4_inode_entry AltBoot;
};











extern struct dentry *qnx4_lookup(struct inode *dir, struct dentry *dentry);
extern unsigned long qnx4_count_free_blocks(struct super_block *sb);
extern unsigned long qnx4_block_map(struct inode *inode, long iblock);

extern struct buffer_head *qnx4_getblk(struct inode *, int, int);
extern struct buffer_head *qnx4_bread(struct inode *, int, int);

extern int init_qnx4_fs(void);
extern int qnx4_create(struct inode *dir, struct dentry *dentry, int mode);
extern struct inode_operations qnx4_file_inode_operations;
extern struct inode_operations qnx4_dir_inode_operations;
extern struct inode_operations qnx4_symlink_inode_operations;
extern int qnx4_is_free(struct super_block *sb, long block);
extern int qnx4_set_bitmap(struct super_block *sb, long block, int busy);
extern int qnx4_create(struct inode *inode, struct dentry *dentry, int mode);
extern void qnx4_truncate(struct inode *inode);
extern void qnx4_free_inode(struct inode *inode);
extern int qnx4_unlink(struct inode *dir, struct dentry *dentry);
extern int qnx4_rmdir(struct inode *dir, struct dentry *dentry);
extern int qnx4_sync_file(struct file *file, struct dentry *dentry);
extern int qnx4_sync_inode(struct inode *inode);
extern int qnx4_bmap(struct inode *inode, int iblock);




# 14 "/usr/src/linux/include/linux/qnx4_fs_sb.h" 2


 



struct qnx4_sb_info {
	struct buffer_head	*sb_buf;	 
	struct qnx4_super_block	*sb;		 
	unsigned int		Version;	 
	struct qnx4_inode_entry	*BitMap;	 
};


# 516 "/usr/src/linux/include/linux/fs.h" 2


extern struct list_head super_blocks;


struct super_block {
	struct list_head	s_list;		 
	kdev_t			s_dev;
	unsigned long		s_blocksize;
	unsigned char		s_blocksize_bits;
	unsigned char		s_lock;
	unsigned char		s_rd_only;
	unsigned char		s_dirt;
	struct file_system_type	*s_type;
	struct super_operations	*s_op;
	struct dquot_operations	*dq_op;
	unsigned long		s_flags;
	unsigned long		s_magic;
	unsigned long		s_time;
	struct dentry		*s_root;
	struct wait_queue	*s_wait;

	struct inode		*s_ibasket;
	short int		s_ibasket_count;
	short int		s_ibasket_max;
	struct list_head	s_dirty;	 

	union {
		struct minix_sb_info	minix_sb;
		struct ext2_sb_info	ext2_sb;
		struct hpfs_sb_info	hpfs_sb;
		struct ntfs_sb_info     ntfs_sb;
		struct msdos_sb_info	msdos_sb;
		struct isofs_sb_info	isofs_sb;
		struct nfs_sb_info	nfs_sb;
		struct sysv_sb_info	sysv_sb;
		struct affs_sb_info	affs_sb;
		struct ufs_sb_info	ufs_sb;
		struct efs_sb_info	efs_sb;
		struct romfs_sb_info	romfs_sb;
		struct smb_sb_info	smbfs_sb;
		struct hfs_sb_info	hfs_sb;
		struct adfs_sb_info	adfs_sb;
		struct qnx4_sb_info	qnx4_sb;	   
		void			*generic_sbp;
	} u;
	 



	struct semaphore s_vfs_rename_sem;	 
};

 


extern int vfs_rmdir(struct inode *, struct dentry *);
extern int vfs_unlink(struct inode *, struct dentry *);
extern int vfs_rename(struct inode *, struct dentry *, struct inode *, struct dentry *);

 





typedef int (*filldir_t)(void *, const char *, int, off_t, ino_t);
	
struct file_operations {
	loff_t (*llseek) (struct file *, loff_t, int);
	ssize_t (*read) (struct file *, char *, size_t, loff_t *);
	ssize_t (*write) (struct file *, const char *, size_t, loff_t *);
	int (*readdir) (struct file *, void *, filldir_t);
	unsigned int (*poll) (struct file *, struct poll_table_struct *);
	int (*ioctl) (struct inode *, struct file *, unsigned int, unsigned long);
	int (*mmap) (struct file *, struct vm_area_struct *);
	int (*open) (struct inode *, struct file *);
	int (*flush) (struct file *);
	int (*release) (struct inode *, struct file *);
	int (*fsync) (struct file *, struct dentry *);
	int (*fasync) (int, struct file *, int);
	int (*check_media_change) (kdev_t dev);
	int (*revalidate) (kdev_t dev);
	int (*lock) (struct file *, int, struct file_lock *);
};

struct inode_operations {
	struct file_operations * default_file_ops;
	int (*create) (struct inode *,struct dentry *,int);
	struct dentry * (*lookup) (struct inode *,struct dentry *);
	int (*link) (struct dentry *,struct inode *,struct dentry *);
	int (*unlink) (struct inode *,struct dentry *);
	int (*symlink) (struct inode *,struct dentry *,const char *);
	int (*mkdir) (struct inode *,struct dentry *,int);
	int (*rmdir) (struct inode *,struct dentry *);
	int (*mknod) (struct inode *,struct dentry *,int,int);
	int (*rename) (struct inode *, struct dentry *,
			struct inode *, struct dentry *);
	int (*readlink) (struct dentry *, char *,int);
	struct dentry * (*follow_link) (struct dentry *, struct dentry *, unsigned int);
	int (*readpage) (struct file *, struct page *);
	int (*writepage) (struct file *, struct page *);
	int (*bmap) (struct inode *,int);
	void (*truncate) (struct inode *);
	int (*permission) (struct inode *, int);
	int (*smap) (struct inode *,int);
	int (*updatepage) (struct file *, struct page *, unsigned long, unsigned int, int);
	int (*revalidate) (struct dentry *);
};

struct super_operations {
	void (*read_inode) (struct inode *);
	void (*write_inode) (struct inode *);
	void (*put_inode) (struct inode *);
	void (*delete_inode) (struct inode *);
	int (*notify_change) (struct dentry *, struct iattr *);
	void (*put_super) (struct super_block *);
	void (*write_super) (struct super_block *);
	int (*statfs) (struct super_block *, struct statfs *, int);
	int (*remount_fs) (struct super_block *, int *, char *);
	void (*clear_inode) (struct inode *);
	void (*umount_begin) (struct super_block *);
};

struct dquot_operations {
	void (*initialize) (struct inode *, short);
	void (*drop) (struct inode *);
	int (*alloc_block) (const struct inode *, unsigned long, uid_t, char);
	int (*alloc_inode) (const struct inode *, unsigned long, uid_t);
	void (*free_block) (const struct inode *, unsigned long);
	void (*free_inode) (const struct inode *, unsigned long);
	int (*transfer) (struct dentry *, struct iattr *, uid_t);
};

struct file_system_type {
	const char *name;
	int fs_flags;
	struct super_block *(*read_super) (struct super_block *, void *, int);
	struct file_system_type * next;
};

extern int register_filesystem(struct file_system_type *);
extern int unregister_filesystem(struct file_system_type *);

 

 





extern int locks_mandatory_locked(struct inode *inode);
extern int locks_mandatory_area(int read_write, struct inode *inode,
				struct file *filp, loff_t offset,
				size_t count);

extern inline int locks_verify_locked(struct inode *inode)
{
	 


	if ((((  inode  )->i_sb && (  inode  )->i_sb->s_flags & (  64  )) || (  inode  )->i_flags & (  64  ))   &&
	    (inode->i_mode & (0002000  | 00010 )) == 0002000 )
		return (locks_mandatory_locked(inode));
	return (0);
}

extern inline int locks_verify_area(int read_write, struct inode *inode,
				    struct file *filp, loff_t offset,
				    size_t count)
{
	 


	if ((((  inode  )->i_sb && (  inode  )->i_sb->s_flags & (  64  )) || (  inode  )->i_flags & (  64  ))   &&
	    (inode->i_mode & (0002000  | 00010 )) == 0002000 )
		return (locks_mandatory_area(read_write, inode, filp, offset,
					     count));
	return (0);
}


 

  __attribute__((regparm(0)))  int sys_open(const char *, int, int);
  __attribute__((regparm(0)))  int sys_close(unsigned int);		 
extern int do_truncate(struct dentry *, unsigned long);
extern int get_unused_fd(void);
extern void put_unused_fd(unsigned int);

extern struct file *filp_open(const char *, int, int);
extern int filp_close(struct file *, fl_owner_t id);

extern char * getname(const char * filename);



extern void kill_fasync(struct fasync_struct *fa, int sig);
extern int register_blkdev(unsigned int, const char *, struct file_operations *);
extern int unregister_blkdev(unsigned int major, const char * name);
extern int blkdev_open(struct inode * inode, struct file * filp);
extern int blkdev_release (struct inode * inode);
extern struct file_operations def_blk_fops;
extern struct inode_operations blkdev_inode_operations;

 
extern int register_chrdev(unsigned int, const char *, struct file_operations *);
extern int unregister_chrdev(unsigned int major, const char * name);
extern int chrdev_open(struct inode * inode, struct file * filp);
extern struct file_operations def_chr_fops;
extern struct inode_operations chrdev_inode_operations;
extern char * bdevname(kdev_t dev);
extern char * cdevname(kdev_t dev);
extern char * kdevname(kdev_t dev);


extern void init_fifo(struct inode * inode);
extern struct inode_operations fifo_inode_operations;

 
extern void make_bad_inode(struct inode * inode);
extern int is_bad_inode(struct inode * inode);

extern struct file_operations connecting_fifo_fops;
extern struct file_operations read_fifo_fops;
extern struct file_operations write_fifo_fops;
extern struct file_operations rdwr_fifo_fops;
extern struct file_operations read_pipe_fops;
extern struct file_operations write_pipe_fops;
extern struct file_operations rdwr_pipe_fops;

extern struct file_system_type *get_fs_type(const char *name);

extern int fs_may_remount_ro(struct super_block *);
extern int fs_may_mount(kdev_t dev);

extern struct file *inuse_filps;

extern void refile_buffer(struct buffer_head * buf);
extern void set_writetime(struct buffer_head * buf, int flag);
extern int try_to_free_buffers(struct page *, int wait);

extern int nr_buffers;
extern long buffermem;
extern int nr_buffer_heads;






void mark_buffer_uptodate(struct buffer_head * bh, int on);

extern inline void mark_buffer_clean(struct buffer_head * bh)
{
	if (test_and_clear_bit(1 , &bh->b_state)) {
		if (bh->b_list == 2 )
			refile_buffer(bh);
	}
}

extern inline void mark_buffer_dirty(struct buffer_head * bh, int flag)
{
	if (!test_and_set_bit(1 , &bh->b_state)) {
		set_writetime(bh, flag);
		if (bh->b_list != 2 )
			refile_buffer(bh);
	}
}

extern int check_disk_change(kdev_t dev);
extern int invalidate_inodes(struct super_block * sb);
extern void invalidate_inode_pages(struct inode *);


extern void __invalidate_buffers(kdev_t dev, int);
extern int floppy_is_wp(int minor);
extern void sync_inodes(kdev_t dev);
extern void write_inode_now(struct inode *inode);
extern void sync_dev(kdev_t dev);
extern int fsync_dev(kdev_t dev);
extern void sync_supers(kdev_t dev);
extern int bmap(struct inode * inode,int block);
extern int notify_change(struct dentry *, struct iattr *);
extern int permission(struct inode * inode,int mask);
extern int get_write_access(struct inode *inode);
extern void put_write_access(struct inode *inode);
extern struct dentry * open_namei(const char * pathname, int flag, int mode);
extern struct dentry * do_mknod(const char * filename, int mode, dev_t dev);
extern int do_pipe(int *);

 
extern int is_subdir(struct dentry *, struct dentry *);
extern ino_t find_inode_number(struct dentry *, struct qstr *);

 











 











extern struct dentry * lookup_dentry(const char *, struct dentry *, unsigned int);
extern struct dentry * __namei(const char *, unsigned int);




extern void iput(struct inode *);
extern struct inode * igrab(struct inode *inode);
extern ino_t iunique(struct super_block *, ino_t);
extern struct inode * iget(struct super_block *, unsigned long);
extern struct inode * iget_in_use (struct super_block *, unsigned long);
extern void clear_inode(struct inode *);
extern struct inode * get_empty_inode(void);

extern void insert_inode_hash(struct inode *);
extern void remove_inode_hash(struct inode *);
extern struct file * get_empty_filp(void);
extern struct buffer_head * get_hash_table(kdev_t, int, int);
extern struct buffer_head * getblk(kdev_t, int, int);
extern struct buffer_head * find_buffer(kdev_t dev, int block, int size);
extern void ll_rw_block(int, int, struct buffer_head * bh[]);
extern int is_read_only(kdev_t);
extern void __brelse(struct buffer_head *);
extern inline void brelse(struct buffer_head *buf)
{
	if (buf)
		__brelse(buf);
}
extern void __bforget(struct buffer_head *buf);
extern inline void bforget(struct buffer_head *buf)
{
	if (buf)
		__bforget(buf);
}
extern void set_blocksize(kdev_t dev, int size);
extern unsigned int get_hardblocksize(kdev_t dev);
extern struct buffer_head * bread(kdev_t dev, int block, int size);
extern struct buffer_head * breada(kdev_t dev,int block, int size, 
				   unsigned int pos, unsigned int filesize);

extern int brw_page(int, struct page *, kdev_t, int [], int, int);

extern int generic_readpage(struct file *, struct page *);
extern int generic_file_mmap(struct file *, struct vm_area_struct *);
extern ssize_t generic_file_read(struct file *, char *, size_t, loff_t *);
extern ssize_t generic_file_write(struct file *, const char*, size_t, loff_t*);

extern struct super_block *get_super(kdev_t dev);
extern void put_super(kdev_t dev);
unsigned long generate_cluster(kdev_t dev, int b[], int size);
unsigned long generate_cluster_swab32(kdev_t dev, int b[], int size);
extern kdev_t ROOT_DEV;

extern void show_buffers(void);
extern void mount_root(void);






extern ssize_t char_read(struct file *, char *, size_t, loff_t *);
extern ssize_t block_read(struct file *, char *, size_t, loff_t *);
extern int read_ahead[];

extern ssize_t char_write(struct file *, const char *, size_t, loff_t *);
extern ssize_t block_write(struct file *, const char *, size_t, loff_t *);

extern int block_fsync(struct file *, struct dentry *dir);
extern int file_fsync(struct file *, struct dentry *dir);

extern int inode_change_ok(struct inode *, struct iattr *);
extern void inode_setattr(struct inode *, struct iattr *);

extern __u32 inode_generation_count;




# 20 "/usr/src/linux/include/linux/tty.h" 2

# 1 "/usr/src/linux/include/linux/major.h" 1



 




 

 



























































                                 




















































 





  




static __inline__ int scsi_blk_major(int m) {
	return (((  m  ) == 8  || ((  m  ) >= 65  && (  m  ) <= 71 )) 	|| ( m ) == 11 ) ;
}


# 21 "/usr/src/linux/include/linux/tty.h" 2

# 1 "/usr/src/linux/include/linux/termios.h" 1




# 1 "/usr/src/linux/include/asm/termios.h" 1



# 1 "/usr/src/linux/include/asm/termbits.h" 1





typedef unsigned char	cc_t;
typedef unsigned int	speed_t;
typedef unsigned int	tcflag_t;


struct termios {
	tcflag_t c_iflag;		 
	tcflag_t c_oflag;		 
	tcflag_t c_cflag;		 
	tcflag_t c_lflag;		 
	cc_t c_line;			 
	cc_t c_cc[19 ];		 
};

 


















 















 
































 


















































 
















 





 




 





# 4 "/usr/src/linux/include/asm/termios.h" 2

# 1 "/usr/src/linux/include/asm/ioctls.h" 1





 
































































 











# 5 "/usr/src/linux/include/asm/termios.h" 2


struct winsize {
	unsigned short ws_row;
	unsigned short ws_col;
	unsigned short ws_xpixel;
	unsigned short ws_ypixel;
};


struct termio {
	unsigned short c_iflag;		 
	unsigned short c_oflag;		 
	unsigned short c_cflag;		 
	unsigned short c_lflag;		 
	unsigned char c_line;		 
	unsigned char c_cc[8 ];	 
};

 














 

 

















 







 

















 



# 97 "/usr/src/linux/include/asm/termios.h"







# 5 "/usr/src/linux/include/linux/termios.h" 2



# 22 "/usr/src/linux/include/linux/tty.h" 2

# 1 "/usr/src/linux/include/linux/tqueue.h" 1
 


















 






















struct tq_struct {
	struct tq_struct *next;		 
	unsigned long sync;		 
	void (*routine)(void *);	 
	void *data;			 
};

typedef struct tq_struct * task_queue;



extern task_queue tq_timer, tq_immediate, tq_scheduler, tq_disk;

 





















extern spinlock_t tqueue_lock;

 


extern __inline__ void queue_task(struct tq_struct *bh_pointer,
			   task_queue *bh_list)
{
	if (!test_and_set_bit(0,&bh_pointer->sync)) {
		unsigned long flags;
		do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
		bh_pointer->next = *bh_list;
		*bh_list = bh_pointer;
		__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
	}
}

 


extern __inline__ void run_task_queue(task_queue *list)
{
	if (*list) {
		unsigned long flags;
		struct tq_struct *p;

		do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
		p = *list;
		*list = ((void *)0) ;
		__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
		
		while (p) {
			void *arg;
			void (*f) (void *);
			struct tq_struct *save_p;
			arg    = p -> data;
			f      = p -> routine;
			save_p = p;
			p      = p -> next;
			__asm__ __volatile__ ("lock; addl $0,0(%%esp)": : :"memory") ;
			save_p -> sync = 0;
			(*f)(arg);
		}
	}
}


# 23 "/usr/src/linux/include/linux/tty.h" 2

# 1 "/usr/src/linux/include/linux/tty_driver.h" 1



 



















































































































struct tty_driver {
	int	magic;		 
	const char	*driver_name;
	const char	*name;
	int	name_base;	 
	short	major;		 
	short	minor_start;	 
	short	num;		 
	short	type;		 
	short	subtype;	 
	struct termios init_termios;  
	int	flags;		 
	int	*refcount;	 
	struct proc_dir_entry *proc_entry;  
	struct tty_driver *other;  

	 


	struct tty_struct **table;
	struct termios **termios;
	struct termios **termios_locked;
	void *driver_state;	 
	
	 



	int  (*open)(struct tty_struct * tty, struct file * filp);
	void (*close)(struct tty_struct * tty, struct file * filp);
	int  (*write)(struct tty_struct * tty, int from_user,
		      const unsigned char *buf, int count);
	void (*put_char)(struct tty_struct *tty, unsigned char ch);
	void (*flush_chars)(struct tty_struct *tty);
	int  (*write_room)(struct tty_struct *tty);
	int  (*chars_in_buffer)(struct tty_struct *tty);
	int  (*ioctl)(struct tty_struct *tty, struct file * file,
		    unsigned int cmd, unsigned long arg);
	void (*set_termios)(struct tty_struct *tty, struct termios * old);
	void (*throttle)(struct tty_struct * tty);
	void (*unthrottle)(struct tty_struct * tty);
	void (*stop)(struct tty_struct *tty);
	void (*start)(struct tty_struct *tty);
	void (*hangup)(struct tty_struct *tty);
	void (*break_ctl)(struct tty_struct *tty, int state);
	void (*flush_buffer)(struct tty_struct *tty);
	void (*set_ldisc)(struct tty_struct *tty);
	void (*wait_until_sent)(struct tty_struct *tty, int timeout);
	void (*send_xchar)(struct tty_struct *tty, char ch);
	int (*read_proc)(char *page, char **start, off_t off,
			  int count, int *eof, void *data);
	int (*write_proc)(struct file *file, const char *buffer,
			  unsigned long count, void *data);

	 


	struct tty_driver *next;
	struct tty_driver *prev;
};

 


 




















 







 





 



 




# 24 "/usr/src/linux/include/linux/tty.h" 2

# 1 "/usr/src/linux/include/linux/tty_ldisc.h" 1



 


































































































struct tty_ldisc {
	int	magic;
	char	*name;
	int	num;
	int	flags;
	 


	int	(*open)(struct tty_struct *);
	void	(*close)(struct tty_struct *);
	void	(*flush_buffer)(struct tty_struct *tty);
	ssize_t	(*chars_in_buffer)(struct tty_struct *tty);
	ssize_t	(*read)(struct tty_struct * tty, struct file * file,
			unsigned char * buf, size_t nr);
	ssize_t	(*write)(struct tty_struct * tty, struct file * file,
			 const unsigned char * buf, size_t nr);	
	int	(*ioctl)(struct tty_struct * tty, struct file * file,
			 unsigned int cmd, unsigned long arg);
	void	(*set_termios)(struct tty_struct *tty, struct termios * old);
	unsigned int (*poll)(struct tty_struct *, struct file *,
			     struct poll_table_struct *);
	
	 


	void	(*receive_buf)(struct tty_struct *, const unsigned char *cp,
			       char *fp, int count);
	int	(*receive_room)(struct tty_struct *);
	void	(*write_wakeup)(struct tty_struct *);
};






# 25 "/usr/src/linux/include/linux/tty.h" 2

# 1 "/usr/src/linux/include/linux/serialP.h" 1
 











 











 


struct async_icount {
	__u32	cts, dsr, rng, dcd, tx, rx;
	__u32	frame, parity, overrun, brk;
	__u32	buf_overrun;
};

struct serial_state {
	int	magic;
	int	baud_base;
	int	port;
	int	irq;
	int	flags;
	int	hub6;
	int	type;
	int	line;
	int	xmit_fifo_size;
	int	custom_divisor;
	int	count;
	unsigned short	close_delay;
	unsigned short	closing_wait;  
	struct async_icount	icount;	
	struct termios		normal_termios;
	struct termios		callout_termios;
	struct async_struct *info;
};

struct async_struct {
	int			magic;
	int			port;
	int			hub6;
	int			flags;
	int			xmit_fifo_size;
	struct serial_state	*state;
	struct tty_struct 	*tty;
	int			read_status_mask;
	int			ignore_status_mask;
	int			timeout;
	int			quot;
	int			x_char;	 
	int			close_delay;
	unsigned short		closing_wait;
	unsigned short		closing_wait2;
	int			IER; 	 
	int			MCR; 	 
	unsigned long		event;
	unsigned long		last_active;
	int			line;
	int			blocked_open;  
	long			session;  
	long			pgrp;  
	unsigned char 		*xmit_buf;
	int			xmit_head;
	int			xmit_tail;
	int			xmit_cnt;
	struct tq_struct	tqueue;
	struct wait_queue	*open_wait;
	struct wait_queue	*close_wait;
	struct wait_queue	*delta_msr_wait;
	struct async_struct	*next_port;  
	struct async_struct	*prev_port;
};




 




 





 


struct rs_multiport_struct {
	int		port1;
	unsigned char	mask1, match1;
	int		port2;
	unsigned char	mask2, match2;
	int		port3;
	unsigned char	mask3, match3;
	int		port4;
	unsigned char	mask4, match4;
	int		port_monitor;
};


# 26 "/usr/src/linux/include/linux/tty.h" 2





 








 















 



struct screen_info {
	unsigned char  orig_x;			 
	unsigned char  orig_y;			 
	unsigned short dontuse1;		 
	unsigned short orig_video_page;		 
	unsigned char  orig_video_mode;		 
	unsigned char  orig_video_cols;		 
	unsigned short unused2;			 
	unsigned short orig_video_ega_bx;	 
	unsigned short unused3;			 
	unsigned char  orig_video_lines;	 
	unsigned char  orig_video_isVGA;	 
	unsigned short orig_video_points;	 

	 
	unsigned short lfb_width;		 
	unsigned short lfb_height;		 
	unsigned short lfb_depth;		 
	unsigned long  lfb_base;		 
	unsigned long  lfb_size;		 
	unsigned short dontuse2, dontuse3;	 
	unsigned short lfb_linelength;		 
	unsigned char  red_size;		 
	unsigned char  red_pos;			 
	unsigned char  green_size;		 
	unsigned char  green_pos;		 
	unsigned char  blue_size;		 
	unsigned char  blue_pos;		 
	unsigned char  rsvd_size;		 
	unsigned char  rsvd_pos;		 
	unsigned short vesapm_seg;		 
	unsigned short vesapm_off;		 
	unsigned short pages;			 
						 
};

extern struct screen_info screen_info;



























 






 






struct tty_flip_buffer {
	struct tq_struct tqueue;
	struct semaphore pty_sem;
	char		*char_buf_ptr;
	unsigned char	*flag_buf_ptr;
	int		count;
	int		buf_num;
	unsigned char	char_buf[2* 512 ];
	char		flag_buf[2* 512 ];
	unsigned char	slop[4];  
};
 




 

























































































 













struct tty_struct {
	int	magic;
	struct tty_driver driver;
	struct tty_ldisc ldisc;
	struct termios *termios, *termios_locked;
	int pgrp;
	int session;
	kdev_t	device;
	unsigned long flags;
	int count;
	struct winsize winsize;
	unsigned char stopped:1, hw_stopped:1, flow_stopped:1, packet:1;
	unsigned char low_latency:1, warned:1;
	unsigned char ctrl_status;

	struct tty_struct *link;
	struct fasync_struct *fasync;
	struct tty_flip_buffer flip;
	int max_flip_cnt;
	int alt_speed;		 
	struct wait_queue *write_wait;
	struct wait_queue *read_wait;
	struct wait_queue *poll_wait;
	struct tq_struct tq_hangup;
	void *disc_data;
	void *driver_data;


	
	 



	unsigned int column;
	unsigned char lnext:1, erasing:1, raw:1, real_raw:1, icanon:1;
	unsigned char closing:1;
	unsigned short minimum_to_wake;
	unsigned overrun_time;
	int num_overrun;
	unsigned long process_char_map[256/(8*sizeof(unsigned long))];
	char *read_buf;
	int read_head;
	int read_tail;
	int read_cnt;
	unsigned long read_flags[4096 /(8*sizeof(unsigned long))];
	int canon_data;
	unsigned long canon_head;
	unsigned int canon_column;
	struct semaphore atomic_read;
	struct semaphore atomic_write;
	spinlock_t read_lock;
};

 


 























extern void tty_write_flush(struct tty_struct *);

extern struct termios tty_std_termios;
extern struct tty_struct * redirect;
extern struct tty_ldisc ldiscs[];
extern int fg_console, last_console, want_console;

extern int kmsg_redirect;

extern unsigned long con_init(unsigned long);

extern int rs_init(void);
extern int lp_init(void);
extern int pty_init(void);
extern int tty_init(void);
extern int mxser_init(void);
extern int moxa_init(void);
extern int ip2_init(void);
extern int pcxe_init(void);
extern int pc_init(void);
extern int vcs_init(void);
extern int rp_init(void);
extern int cy_init(void);
extern int stl_init(void);
extern int stli_init(void);
extern int riscom8_init(void);
extern int specialix_init(void);
extern int espserial_init(void);
extern int macserial_init(void);

extern int tty_paranoia_check(struct tty_struct *tty, kdev_t device,
			      const char *routine);
extern char *tty_name(struct tty_struct *tty, char *buf);
extern void tty_wait_until_sent(struct tty_struct * tty, long timeout);
extern int tty_check_change(struct tty_struct * tty);
extern void stop_tty(struct tty_struct * tty);
extern void start_tty(struct tty_struct * tty);
extern int tty_register_ldisc(int disc, struct tty_ldisc *new_ldisc);
extern int tty_register_driver(struct tty_driver *driver);
extern int tty_unregister_driver(struct tty_driver *driver);
extern int tty_read_raw_data(struct tty_struct *tty, unsigned char *bufp,
			     int buflen);
extern void tty_write_message(struct tty_struct *tty, char *msg);

extern int is_orphaned_pgrp(int pgrp);
extern int is_ignored(int sig);
extern int tty_signal(int sig, struct tty_struct *tty);
extern void tty_hangup(struct tty_struct * tty);
extern void tty_vhangup(struct tty_struct * tty);
extern void tty_unhangup(struct file *filp);
extern int tty_hung_up_p(struct file * filp);
extern void do_SAK(struct tty_struct *tty);
extern void disassociate_ctty(int priv);
extern void tty_flip_buffer_push(struct tty_struct *tty);
extern int tty_get_baud_rate(struct tty_struct *tty);

 
extern struct tty_ldisc tty_ldisc_N_TTY;

 
extern int n_tty_ioctl(struct tty_struct * tty, struct file * file,
		       unsigned int cmd, unsigned long arg);

 

extern long serial_console_init(long kmem_start, long kmem_end);
 
 

extern int pcxe_open(struct tty_struct *tty, struct file *filp);

 

extern void console_print(const char *);

 

extern int vt_ioctl(struct tty_struct *tty, struct file * file,
		    unsigned int cmd, unsigned long arg);



# 21 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/linux/sem.h" 1



# 1 "/usr/src/linux/include/linux/ipc.h" 1







struct ipc_perm
{
	__kernel_key_t	key;
	__kernel_uid_t	uid;
	__kernel_gid_t	gid;
	__kernel_uid_t	cuid;
	__kernel_gid_t	cgid;
	__kernel_mode_t	mode; 
	unsigned short	seq;
};

 




 

   



 










 








# 4 "/usr/src/linux/include/linux/sem.h" 2


 


 








 



 
struct semid_ds {
	struct ipc_perm	sem_perm;		 
	__kernel_time_t	sem_otime;		 
	__kernel_time_t	sem_ctime;		 
	struct sem	*sem_base;		 
	struct sem_queue *sem_pending;		 
	struct sem_queue **sem_pending_last;	 
	struct sem_undo	*undo;			 
	unsigned short	sem_nsems;		 
};

 
struct sembuf {
	unsigned short  sem_num;	 
	short		sem_op;		 
	short		sem_flg;	 
};

 
union semun {
	int val;			 
	struct semid_ds *buf;		 
	unsigned short *array;		 
	struct seminfo *__buf;		 
	void *__pad;
};

struct  seminfo {
	int semmap;
	int semmni;
	int semmns;
	int semmnu;
	int semmsl;
	int semopm;
	int semume;
	int semusz;
	int semvmx;
	int semaem;
};







 








 
struct sem {
	int	semval;		 
	int	sempid;		 
};

 
struct sem_queue {
	struct sem_queue *	next;	  
	struct sem_queue **	prev;	  
	struct wait_queue *	sleeper;  
	struct sem_undo *	undo;	  
	int    			pid;	  
	int    			status;	  
	struct semid_ds *	sma;	  
	struct sembuf *		sops;	  
	int			nsops;	  
	int			alter;	  
};

 


struct sem_undo {
	struct sem_undo *	proc_next;	 
	struct sem_undo *	id_next;	 
	int			semid;		 
	short *			semadj;		 
};

  __attribute__((regparm(0)))  int sys_semget (key_t key, int nsems, int semflg);
  __attribute__((regparm(0)))  int sys_semop (int semid, struct sembuf *sops, unsigned nsops);
  __attribute__((regparm(0)))  int sys_semctl (int semid, int semnum, int cmd, union semun arg);




# 22 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/linux/signal.h" 1



# 1 "/usr/src/linux/include/asm/signal.h" 1





 
struct siginfo;


 






typedef unsigned long old_sigset_t;		 

typedef struct {
	unsigned long sig[(64  / 32 ) ];
} sigset_t;








































 





 



 



























 










 















 
typedef void (*__sighandler_t)(int);






struct old_sigaction {
	__sighandler_t sa_handler;
	old_sigset_t sa_mask;
	unsigned long sa_flags;
	void (*sa_restorer)(void);
};

struct sigaction {
	__sighandler_t sa_handler;
	unsigned long sa_flags;
	void (*sa_restorer)(void);
	sigset_t sa_mask;		 
};

struct k_sigaction {
	struct sigaction sa;
};
# 168 "/usr/src/linux/include/asm/signal.h"


typedef struct sigaltstack {
	void *ss_sp;
	int ss_flags;
	size_t ss_size;
} stack_t;


# 1 "/usr/src/linux/include/asm/sigcontext.h" 1



 







struct _fpreg {
	unsigned short significand[4];
	unsigned short exponent;
};

struct _fpstate {
	unsigned long 	cw,
			sw,
			tag,
			ipoff,
			cssel,
			dataoff,
			datasel;
	struct _fpreg	_st[8];
	unsigned long	status;
};

struct sigcontext {
	unsigned short gs, __gsh;
	unsigned short fs, __fsh;
	unsigned short es, __esh;
	unsigned short ds, __dsh;
	unsigned long edi;
	unsigned long esi;
	unsigned long ebp;
	unsigned long esp;
	unsigned long ebx;
	unsigned long edx;
	unsigned long ecx;
	unsigned long eax;
	unsigned long trapno;
	unsigned long err;
	unsigned long eip;
	unsigned short cs, __csh;
	unsigned long eflags;
	unsigned long esp_at_signal;
	unsigned short ss, __ssh;
	struct _fpstate * fpstate;
	unsigned long oldmask;
	unsigned long cr2;
};



# 177 "/usr/src/linux/include/asm/signal.h" 2




extern __inline__ void sigaddset(sigset_t *set, int _sig)
{
	__asm__("btsl %1,%0" : "=m"(*set) : "ir"(_sig - 1) : "cc");
}

extern __inline__ void sigdelset(sigset_t *set, int _sig)
{
	__asm__("btrl %1,%0" : "=m"(*set) : "ir"(_sig - 1) : "cc");
}

extern __inline__ int __const_sigismember(sigset_t *set, int _sig)
{
	unsigned long sig = _sig - 1;
	return 1 & (set->sig[sig / 32 ] >> (sig % 32 ));
}

extern __inline__ int __gen_sigismember(sigset_t *set, int _sig)
{
	int ret;
	__asm__("btl %2,%1\n\tsbbl %0,%0"
		: "=r"(ret) : "m"(*set), "ir"(_sig-1) : "cc");
	return ret;
}








extern __inline__ int sigfindinword(unsigned long word)
{
	__asm__("bsfl %1,%0" : "=r"(word) : "rm"(word) : "cc");
	return word;
}




# 4 "/usr/src/linux/include/linux/signal.h" 2

# 1 "/usr/src/linux/include/asm/siginfo.h" 1





 

typedef union sigval {
	int sival_int;
	void *sival_ptr;
} sigval_t;




typedef struct siginfo {
	int si_signo;
	int si_errno;
	int si_code;

	union {
		int _pad[((128 /sizeof(int)) - 3) ];

		 
		struct {
			pid_t _pid;		 
			uid_t _uid;		 
		} _kill;

		 
		struct {
			unsigned int _timer1;
			unsigned int _timer2;
		} _timer;

		 
		struct {
			pid_t _pid;		 
			uid_t _uid;		 
			sigval_t _sigval;
		} _rt;

		 
		struct {
			pid_t _pid;		 
			uid_t _uid;		 
			int _status;		 
			clock_t _utime;
			clock_t _stime;
		} _sigchld;

		 
		struct {
			void *_addr;  
		} _sigfault;

		 
		struct {
			int _band;	 
			int _fd;
		} _sigpoll;
	} _sifields;
} siginfo_t;

 














 














 












 












 






 







 






 










 










 














typedef struct sigevent {
	sigval_t sigev_value;
	int sigev_signo;
	int sigev_notify;
	union {
		int _pad[((64 /sizeof(int)) - 3) ];

		struct {
			void (*_function)(sigval_t);
			void *_attribute;	 
		} _sigev_thread;
	} _sigev_un;
} sigevent_t;





# 5 "/usr/src/linux/include/linux/signal.h" 2



 



struct signal_queue
{
	struct signal_queue *next;
	siginfo_t info;
};

 



# 61 "/usr/src/linux/include/linux/signal.h"



# 1 "/usr/src/linux/include/linux/string.h" 1










extern char * ___strtok;
extern char * strcpy(char *,const char *);
extern char * strncpy(char *,const char *, __kernel_size_t);
extern char * strcat(char *, const char *);
extern char * strncat(char *, const char *, __kernel_size_t);
extern char * strchr(const char *,int);
extern char * strrchr(const char *,int);
extern char * strpbrk(const char *,const char *);
extern char * strtok(char *,const char *);
extern char * strstr(const char *,const char *);
extern __kernel_size_t strlen(const char *);
extern __kernel_size_t strnlen(const char *,__kernel_size_t);
extern __kernel_size_t strspn(const char *,const char *);
extern int strcmp(const char *,const char *);
extern int strncmp(const char *,const char *,__kernel_size_t);
extern int strnicmp(const char *, const char *, __kernel_size_t);

extern void * memset(void *,int,__kernel_size_t);
extern void * memcpy(void *,const void *,__kernel_size_t);
extern void * memmove(void *,const void *,__kernel_size_t);
extern void * memscan(void *,int,__kernel_size_t);
extern int memcmp(const void *,const void *,__kernel_size_t);

 


# 1 "/usr/src/linux/include/asm/string.h" 1



 












 













extern inline char * strcpy(char * dest,const char *src)
{
int d0, d1, d2;
__asm__ __volatile__(
	"cld\n"
	"1:\tlodsb\n\t"
	"stosb\n\t"
	"testb %%al,%%al\n\t"
	"jne 1b"
	: "=&S" (d0), "=&D" (d1), "=&a" (d2)
	:"0" (src),"1" (dest) : "memory");
return dest;
}


extern inline char * strncpy(char * dest,const char *src,size_t count)
{
int d0, d1, d2, d3;
__asm__ __volatile__(
	"cld\n"
	"1:\tdecl %2\n\t"
	"js 2f\n\t"
	"lodsb\n\t"
	"stosb\n\t"
	"testb %%al,%%al\n\t"
	"jne 1b\n\t"
	"rep\n\t"
	"stosb\n"
	"2:"
	: "=&S" (d0), "=&D" (d1), "=&c" (d2), "=&a" (d3)
	:"0" (src),"1" (dest),"2" (count) : "memory");
return dest;
}


extern inline char * strcat(char * dest,const char * src)
{
int d0, d1, d2, d3;
__asm__ __volatile__(
	"cld\n\t"
	"repne\n\t"
	"scasb\n\t"
	"decl %1\n"
	"1:\tlodsb\n\t"
	"stosb\n\t"
	"testb %%al,%%al\n\t"
	"jne 1b"
	: "=&S" (d0), "=&D" (d1), "=&a" (d2), "=&c" (d3)
	: "0" (src), "1" (dest), "2" (0), "3" (0xffffffff):"memory");
return dest;
}


extern inline char * strncat(char * dest,const char * src,size_t count)
{
int d0, d1, d2, d3;
__asm__ __volatile__(
	"cld\n\t"
	"repne\n\t"
	"scasb\n\t"
	"decl %1\n\t"
	"movl %8,%3\n"
	"1:\tdecl %3\n\t"
	"js 2f\n\t"
	"lodsb\n\t"
	"stosb\n\t"
	"testb %%al,%%al\n\t"
	"jne 1b\n"
	"2:\txorl %2,%2\n\t"
	"stosb"
	: "=&S" (d0), "=&D" (d1), "=&a" (d2), "=&c" (d3)
	: "0" (src),"1" (dest),"2" (0),"3" (0xffffffff), "g" (count)
	: "memory");
return dest;
}


extern inline int strcmp(const char * cs,const char * ct)
{
int d0, d1;
register int __res;
__asm__ __volatile__(
	"cld\n"
	"1:\tlodsb\n\t"
	"scasb\n\t"
	"jne 2f\n\t"
	"testb %%al,%%al\n\t"
	"jne 1b\n\t"
	"xorl %%eax,%%eax\n\t"
	"jmp 3f\n"
	"2:\tsbbl %%eax,%%eax\n\t"
	"orb $1,%%al\n"
	"3:"
	:"=a" (__res), "=&S" (d0), "=&D" (d1)
		     :"1" (cs),"2" (ct));
return __res;
}


extern inline int strncmp(const char * cs,const char * ct,size_t count)
{
register int __res;
int d0, d1, d2;
__asm__ __volatile__(
	"cld\n"
	"1:\tdecl %3\n\t"
	"js 2f\n\t"
	"lodsb\n\t"
	"scasb\n\t"
	"jne 3f\n\t"
	"testb %%al,%%al\n\t"
	"jne 1b\n"
	"2:\txorl %%eax,%%eax\n\t"
	"jmp 4f\n"
	"3:\tsbbl %%eax,%%eax\n\t"
	"orb $1,%%al\n"
	"4:"
		     :"=a" (__res), "=&S" (d0), "=&D" (d1), "=&c" (d2)
		     :"1" (cs),"2" (ct),"3" (count));
return __res;
}


extern inline char * strchr(const char * s, int c)
{
int d0;
register char * __res;
__asm__ __volatile__(
	"cld\n\t"
	"movb %%al,%%ah\n"
	"1:\tlodsb\n\t"
	"cmpb %%ah,%%al\n\t"
	"je 2f\n\t"
	"testb %%al,%%al\n\t"
	"jne 1b\n\t"
	"movl $1,%1\n"
	"2:\tmovl %1,%0\n\t"
	"decl %0"
	:"=a" (__res), "=&S" (d0) : "1" (s),"0" (c));
return __res;
}


extern inline char * strrchr(const char * s, int c)
{
int d0, d1;
register char * __res;
__asm__ __volatile__(
	"cld\n\t"
	"movb %%al,%%ah\n"
	"1:\tlodsb\n\t"
	"cmpb %%ah,%%al\n\t"
	"jne 2f\n\t"
	"leal -1(%%esi),%0\n"
	"2:\ttestb %%al,%%al\n\t"
	"jne 1b"
	:"=g" (__res), "=&S" (d0), "=&a" (d1) :"0" (0),"1" (s),"2" (c));
return __res;
}


extern inline size_t strlen(const char * s)
{
int d0;
register int __res;
__asm__ __volatile__(
	"cld\n\t"
	"repne\n\t"
	"scasb\n\t"
	"notl %0\n\t"
	"decl %0"
	:"=c" (__res), "=&D" (d0) :"1" (s),"a" (0), "0" (0xffffffff));
return __res;
}

extern inline void * __memcpy(void * to, const void * from, size_t n)
{
int d0, d1, d2;
__asm__ __volatile__(
	"cld\n\t"
	"rep ; movsl\n\t"
	"testb $2,%b4\n\t"
	"je 1f\n\t"
	"movsw\n"
	"1:\ttestb $1,%b4\n\t"
	"je 2f\n\t"
	"movsb\n"
	"2:"
	: "=&c" (d0), "=&D" (d1), "=&S" (d2)
	:"0" (n/4), "q" (n),"1" ((long) to),"2" ((long) from)
	: "memory");
return (to);
}

 



extern inline void * __constant_memcpy(void * to, const void * from, size_t n)
{
	switch (n) {
		case 0:
			return to;
		case 1:
			*(unsigned char *)to = *(const unsigned char *)from;
			return to;
		case 2:
			*(unsigned short *)to = *(const unsigned short *)from;
			return to;
		case 3:
			*(unsigned short *)to = *(const unsigned short *)from;
			*(2+(unsigned char *)to) = *(2+(const unsigned char *)from);
			return to;
		case 4:
			*(unsigned long *)to = *(const unsigned long *)from;
			return to;
		case 6:	 
			*(unsigned long *)to = *(const unsigned long *)from;
			*(2+(unsigned short *)to) = *(2+(const unsigned short *)from);
			return to;
		case 8:
			*(unsigned long *)to = *(const unsigned long *)from;
			*(1+(unsigned long *)to) = *(1+(const unsigned long *)from);
			return to;
		case 12:
			*(unsigned long *)to = *(const unsigned long *)from;
			*(1+(unsigned long *)to) = *(1+(const unsigned long *)from);
			*(2+(unsigned long *)to) = *(2+(const unsigned long *)from);
			return to;
		case 16:
			*(unsigned long *)to = *(const unsigned long *)from;
			*(1+(unsigned long *)to) = *(1+(const unsigned long *)from);
			*(2+(unsigned long *)to) = *(2+(const unsigned long *)from);
			*(3+(unsigned long *)to) = *(3+(const unsigned long *)from);
			return to;
		case 20:
			*(unsigned long *)to = *(const unsigned long *)from;
			*(1+(unsigned long *)to) = *(1+(const unsigned long *)from);
			*(2+(unsigned long *)to) = *(2+(const unsigned long *)from);
			*(3+(unsigned long *)to) = *(3+(const unsigned long *)from);
			*(4+(unsigned long *)to) = *(4+(const unsigned long *)from);
			return to;
	}








{
	int d0, d1, d2;
	switch (n % 4) {
		case 0: __asm__ __volatile__( "cld\n\t" "rep ; movsl"  ""  : "=&c" (d0), "=&D" (d1), "=&S" (d2) : "0" (n/4),"1" ((long) to),"2" ((long) from) : "memory"); ; return to;
		case 1: __asm__ __volatile__( "cld\n\t" "rep ; movsl"  "\n\tmovsb"  : "=&c" (d0), "=&D" (d1), "=&S" (d2) : "0" (n/4),"1" ((long) to),"2" ((long) from) : "memory"); ; return to;
		case 2: __asm__ __volatile__( "cld\n\t" "rep ; movsl"  "\n\tmovsw"  : "=&c" (d0), "=&D" (d1), "=&S" (d2) : "0" (n/4),"1" ((long) to),"2" ((long) from) : "memory"); ; return to;
		default: __asm__ __volatile__( "cld\n\t" "rep ; movsl"  "\n\tmovsw\n\tmovsb"  : "=&c" (d0), "=&D" (d1), "=&S" (d2) : "0" (n/4),"1" ((long) to),"2" ((long) from) : "memory"); ; return to;
	}
}
  

}








extern inline void * memmove(void * dest,const void * src, size_t n)
{
int d0, d1, d2;
if (dest<src)
__asm__ __volatile__(
	"cld\n\t"
	"rep\n\t"
	"movsb"
	: "=&c" (d0), "=&S" (d1), "=&D" (d2)
	:"0" (n),"1" (src),"2" (dest)
	: "memory");
else
__asm__ __volatile__(
	"std\n\t"
	"rep\n\t"
	"movsb\n\t"
	"cld"
	: "=&c" (d0), "=&S" (d1), "=&D" (d2)
	:"0" (n),
	 "1" (n-1+(const char *)src),
	 "2" (n-1+(char *)dest)
	:"memory");
return dest;
}




extern inline void * memchr(const void * cs,int c,size_t count)
{
int d0;
register void * __res;
if (!count)
	return ((void *)0) ;
__asm__ __volatile__(
	"cld\n\t"
	"repne\n\t"
	"scasb\n\t"
	"je 1f\n\t"
	"movl $1,%0\n"
	"1:\tdecl %0"
	:"=D" (__res), "=&c" (d0) : "a" (c),"0" (cs),"1" (count));
return __res;
}

extern inline void * __memset_generic(void * s, char c,size_t count)
{
int d0, d1;
__asm__ __volatile__(
	"cld\n\t"
	"rep\n\t"
	"stosb"
	: "=&c" (d0), "=&D" (d1)
	:"a" (c),"1" (s),"0" (count)
	:"memory");
return s;
}

 


 




extern inline void * __constant_c_memset(void * s, unsigned long c, size_t count)
{
int d0, d1;
__asm__ __volatile__(
	"cld\n\t"
	"rep ; stosl\n\t"
	"testb $2,%b3\n\t"
	"je 1f\n\t"
	"stosw\n"
	"1:\ttestb $1,%b3\n\t"
	"je 2f\n\t"
	"stosb\n"
	"2:"
	: "=&c" (d0), "=&D" (d1)
	:"a" (c), "q" (count), "0" (count/4), "1" ((long) s)
	:"memory");
return (s);	
}

 

extern inline size_t strnlen(const char * s, size_t count)
{
int d0;
register int __res;
__asm__ __volatile__(
	"movl %2,%0\n\t"
	"jmp 2f\n"
	"1:\tcmpb $0,(%0)\n\t"
	"je 3f\n\t"
	"incl %0\n"
	"2:\tdecl %1\n\t"
	"cmpl $-1,%1\n\t"
	"jne 1b\n"
	"3:\tsubl %2,%0"
	:"=a" (__res), "=&d" (d0)
	:"c" (s),"1" (count));
return __res;
}
 

 



extern inline void * __constant_c_and_count_memset(void * s, unsigned long pattern, size_t count)
{
	switch (count) {
		case 0:
			return s;
		case 1:
			*(unsigned char *)s = pattern;
			return s;
		case 2:
			*(unsigned short *)s = pattern;
			return s;
		case 3:
			*(unsigned short *)s = pattern;
			*(2+(unsigned char *)s) = pattern;
			return s;
		case 4:
			*(unsigned long *)s = pattern;
			return s;
	}







{
	int d0, d1;
	switch (count % 4) {
		case 0: __asm__  __volatile__("cld\n\t" "rep ; stosl"  ""  : "=&c" (d0), "=&D" (d1) : "a" (pattern),"0" (count/4),"1" ((long) s) : "memory") ; return s;
		case 1: __asm__  __volatile__("cld\n\t" "rep ; stosl"  "\n\tstosb"  : "=&c" (d0), "=&D" (d1) : "a" (pattern),"0" (count/4),"1" ((long) s) : "memory") ; return s;
		case 2: __asm__  __volatile__("cld\n\t" "rep ; stosl"  "\n\tstosw"  : "=&c" (d0), "=&D" (d1) : "a" (pattern),"0" (count/4),"1" ((long) s) : "memory") ; return s;
		default: __asm__  __volatile__("cld\n\t" "rep ; stosl"  "\n\tstosw\n\tstosb"  : "=&c" (d0), "=&D" (d1) : "a" (pattern),"0" (count/4),"1" ((long) s) : "memory") ; return s;
	}
}
  

}

















 



extern inline void * memscan(void * addr, int c, size_t size)
{
	if (!size)
		return addr;
	__asm__("cld
		repnz; scasb
		jnz 1f
		dec %%edi
1:		"
		: "=D" (addr), "=c" (size)
		: "0" (addr), "1" (size), "a" (c));
	return addr;
}



# 37 "/usr/src/linux/include/linux/string.h" 2







# 64 "/usr/src/linux/include/linux/signal.h" 2



# 102 "/usr/src/linux/include/linux/signal.h"


extern inline void  sigorsets (sigset_t *r, const sigset_t *a, const sigset_t *b) {	unsigned long a0, a1, a2, a3, b0, b1, b2, b3;	unsigned long i;	for (i = 0; i < (64  / 32 ) /4; ++i) {	a0 = a->sig[4*i+0]; a1 = a->sig[4*i+1];	a2 = a->sig[4*i+2]; a3 = a->sig[4*i+3];	b0 = b->sig[4*i+0]; b1 = b->sig[4*i+1];	b2 = b->sig[4*i+2]; b3 = b->sig[4*i+3];	r->sig[4*i+0] =   (( a0 ) | (  b0 )) ;	r->sig[4*i+1] =   (( a1 ) | (  b1 )) ;	r->sig[4*i+2] =   (( a2 ) | (  b2 )) ;	r->sig[4*i+3] =   (( a3 ) | (  b3 )) ;	}	switch ((64  / 32 )  % 4) {	case 3:	a0 = a->sig[4*i+0]; a1 = a->sig[4*i+1]; a2 = a->sig[4*i+2]; b0 = b->sig[4*i+0]; b1 = b->sig[4*i+1]; b2 = b->sig[4*i+2]; r->sig[4*i+0] =   (( a0 ) | (  b0 )) ;	r->sig[4*i+1] =   (( a1 ) | (  b1 )) ;	r->sig[4*i+2] =   (( a2 ) | (  b2 )) ;	break;	case 2:	a0 = a->sig[4*i+0]; a1 = a->sig[4*i+1];	b0 = b->sig[4*i+0]; b1 = b->sig[4*i+1];	r->sig[4*i+0] =   (( a0 ) | (  b0 )) ;	r->sig[4*i+1] =   (( a1 ) | (  b1 )) ;	break;	case 1:	a0 = a->sig[4*i+0]; b0 = b->sig[4*i+0];	r->sig[4*i+0] =   (( a0 ) | (  b0 )) ;	break;	}	}


extern inline void  sigandsets (sigset_t *r, const sigset_t *a, const sigset_t *b) {	unsigned long a0, a1, a2, a3, b0, b1, b2, b3;	unsigned long i;	for (i = 0; i < (64  / 32 ) /4; ++i) {	a0 = a->sig[4*i+0]; a1 = a->sig[4*i+1];	a2 = a->sig[4*i+2]; a3 = a->sig[4*i+3];	b0 = b->sig[4*i+0]; b1 = b->sig[4*i+1];	b2 = b->sig[4*i+2]; b3 = b->sig[4*i+3];	r->sig[4*i+0] =   (( a0 ) & (  b0 )) ;	r->sig[4*i+1] =   (( a1 ) & (  b1 )) ;	r->sig[4*i+2] =   (( a2 ) & (  b2 )) ;	r->sig[4*i+3] =   (( a3 ) & (  b3 )) ;	}	switch ((64  / 32 )  % 4) {	case 3:	a0 = a->sig[4*i+0]; a1 = a->sig[4*i+1]; a2 = a->sig[4*i+2]; b0 = b->sig[4*i+0]; b1 = b->sig[4*i+1]; b2 = b->sig[4*i+2]; r->sig[4*i+0] =   (( a0 ) & (  b0 )) ;  r->sig[4*i+1] =   (( a1 ) & (  b1 )) ;  r->sig[4*i+2] =   (( a2 ) & (  b2 )) ;  break;  case 2:	a0 = a->sig[4*i+0]; a1 = a->sig[4*i+1];	b0 = b->sig[4*i+0]; b1 = b->sig[4*i+1];	r->sig[4*i+0] =   (( a0 ) & (  b0 )) ;  r->sig[4*i+1] =   (( a1 ) & (  b1 )) ;  break;  case 1:	a0 = a->sig[4*i+0]; b0 = b->sig[4*i+0];	r->sig[4*i+0] =   (( a0 ) & (  b0 )) ;  break;  }       }   // AMBIGUOUS


extern inline void  signandsets (sigset_t *r, const sigset_t *a, const sigset_t *b) {	unsigned long a0, a1, a2, a3, b0, b1, b2, b3;	unsigned long i;	for (i = 0; i < (64  / 32 ) /4; ++i) {	a0 = a->sig[4*i+0]; a1 = a->sig[4*i+1];	a2 = a->sig[4*i+2]; a3 = a->sig[4*i+3];	b0 = b->sig[4*i+0]; b1 = b->sig[4*i+1];	b2 = b->sig[4*i+2]; b3 = b->sig[4*i+3];	r->sig[4*i+0] =   (( a0 ) & ~(  b0 )) ;	r->sig[4*i+1] =   (( a1 ) & ~(  b1 )) ;	r->sig[4*i+2] =   (( a2 ) & ~(  b2 )) ;	r->sig[4*i+3] =   (( a3 ) & ~(  b3 )) ;	}	switch ((64  / 32 )  % 4) {	case 3:	a0 = a->sig[4*i+0]; a1 = a->sig[4*i+1]; a2 = a->sig[4*i+2]; b0 = b->sig[4*i+0]; b1 = b->sig[4*i+1]; b2 = b->sig[4*i+2]; r->sig[4*i+0] =   (( a0 ) & ~(  b0 )) ;	r->sig[4*i+1] =   (( a1 ) & ~(  b1 )) ;	r->sig[4*i+2] =   (( a2 ) & ~(  b2 )) ;	break;	case 2:	a0 = a->sig[4*i+0]; a1 = a->sig[4*i+1];	b0 = b->sig[4*i+0]; b1 = b->sig[4*i+1];	r->sig[4*i+0] =   (( a0 ) & ~(  b0 )) ;	r->sig[4*i+1] =   (( a1 ) & ~(  b1 )) ;	break;	case 1:	a0 = a->sig[4*i+0]; b0 = b->sig[4*i+0];	r->sig[4*i+0] =   (( a0 ) & ~(  b0 )) ;	break;	}	}   // AMBIGUOUS







# 134 "/usr/src/linux/include/linux/signal.h"


extern inline void  signotset (sigset_t *set)	{	unsigned long i;	for (i = 0; i < (64  / 32 ) /4; ++i) {	set->sig[4*i+0] =   (~( set->sig[4*i+0] )) ;	set->sig[4*i+1] =   (~( set->sig[4*i+1] )) ;	set->sig[4*i+2] =   (~( set->sig[4*i+2] )) ;	set->sig[4*i+3] =   (~( set->sig[4*i+3] )) ;	}	switch ((64  / 32 )  % 4) {	case 3: set->sig[4*i+2] =   (~( set->sig[4*i+2] )) ;    case 2: set->sig[4*i+1] =   (~( set->sig[4*i+1] )) ;    case 1: set->sig[4*i+0] =   (~( set->sig[4*i+0] )) ;    }       }




extern inline void sigemptyset(sigset_t *set)
{
	switch ((64  / 32 ) ) {
	default:
		(__builtin_constant_p(  0 ) ? (__builtin_constant_p( (  sizeof(sigset_t) ) ) ? __constant_c_and_count_memset(( ( set ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  sizeof(sigset_t) ) )) : __constant_c_memset(( ( set ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  sizeof(sigset_t) ) )))  : (__builtin_constant_p( (  sizeof(sigset_t) ) ) ? __memset_generic(( ( ( set ) ) ),( ( (  0 ) ) ),( ( (  sizeof(sigset_t) ) ) ))  : __memset_generic(( ( set ) ),( (  0 ) ),( (  sizeof(sigset_t) ) ))) ) ;
		break;
	case 2: set->sig[1] = 0;
	case 1:	set->sig[0] = 0;
		break;
	}
}

extern inline void sigfillset(sigset_t *set)
{
	switch ((64  / 32 ) ) {
	default:
		(__builtin_constant_p(  -1 ) ? (__builtin_constant_p( (  sizeof(sigset_t) ) ) ? __constant_c_and_count_memset(( ( set ) ),( (0x01010101UL*(unsigned char)(  -1 )) ),( (  sizeof(sigset_t) ) )) : __constant_c_memset(( ( set ) ),( (0x01010101UL*(unsigned char)(  -1 )) ),( (  sizeof(sigset_t) ) )))  : (__builtin_constant_p( (  sizeof(sigset_t) ) ) ? __memset_generic(( ( ( set ) ) ),( ( (  -1 ) ) ),( ( (  sizeof(sigset_t) ) ) ))  : __memset_generic(( ( set ) ),( (  -1 ) ),( (  sizeof(sigset_t) ) ))) ) ;
		break;
	case 2: set->sig[1] = -1;
	case 1:	set->sig[0] = -1;
		break;
	}
}

extern char * render_sigset_t(sigset_t *set, char *buffer);

 

extern inline void sigaddsetmask(sigset_t *set, unsigned long mask)
{
	set->sig[0] |= mask;
}

extern inline void sigdelsetmask(sigset_t *set, unsigned long mask)
{
	set->sig[0] &= ~mask;
}

extern inline int sigtestsetmask(sigset_t *set, unsigned long mask)
{
	return (set->sig[0] & mask) != 0;
}

extern inline void siginitset(sigset_t *set, unsigned long mask)
{
	set->sig[0] = mask;
	switch ((64  / 32 ) ) {
	default:
		(__builtin_constant_p(  0 ) ? (__builtin_constant_p( (  sizeof(long)*((64  / 32 ) -1) ) ) ? __constant_c_and_count_memset(( ( &set->sig[1] ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  sizeof(long)*((64  / 32 ) -1) ) )) : __constant_c_memset(( ( &set->sig[1] ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  sizeof(long)*((64  / 32 ) -1) ) )))  : (__builtin_constant_p( (  sizeof(long)*((64  / 32 ) -1) ) ) ? __memset_generic(( ( ( &set->sig[1] ) ) ),( ( (  0 ) ) ),( ( (  sizeof(long)*((64  / 32 ) -1) ) ) ))  : __memset_generic(( ( &set->sig[1] ) ),( (  0 ) ),( (  sizeof(long)*((64  / 32 ) -1) ) ))) ) ;
		break;
	case 2: set->sig[1] = 0;
	case 1:
	}
}

extern inline void siginitsetinv(sigset_t *set, unsigned long mask)
{
	set->sig[0] = ~mask;
	switch ((64  / 32 ) ) {
	default:
		(__builtin_constant_p(  -1 ) ? (__builtin_constant_p( (  sizeof(long)*((64  / 32 ) -1) ) ) ? __constant_c_and_count_memset(( ( &set->sig[1] ) ),( (0x01010101UL*(unsigned char)(  -1 )) ),( (  sizeof(long)*((64  / 32 ) -1) ) )) : __constant_c_memset(( ( &set->sig[1] ) ),( (0x01010101UL*(unsigned char)(  -1 )) ),( (  sizeof(long)*((64  / 32 ) -1) ) )))  : (__builtin_constant_p( (  sizeof(long)*((64  / 32 ) -1) ) ) ? __memset_generic(( ( ( &set->sig[1] ) ) ),( ( (  -1 ) ) ),( ( (  sizeof(long)*((64  / 32 ) -1) ) ) ))  : __memset_generic(( ( &set->sig[1] ) ),( (  -1 ) ),( (  sizeof(long)*((64  / 32 ) -1) ) ))) ) ;
		break;
	case 2: set->sig[1] = -1;
	case 1:
	}
}






# 23 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/linux/securebits.h" 1





extern unsigned securebits;

 







 




 









# 24 "/usr/src/linux/include/linux/sched.h" 2


 











 









extern unsigned long avenrun[];		 
















extern int nr_running, nr_tasks;
extern int last_pid;



# 1 "/usr/src/linux/include/linux/param.h" 1






# 70 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/linux/resource.h" 1





 



 










struct	rusage {
	struct timeval ru_utime;	 
	struct timeval ru_stime;	 
	long	ru_maxrss;		 
	long	ru_ixrss;		 
	long	ru_idrss;		 
	long	ru_isrss;		 
	long	ru_minflt;		 
	long	ru_majflt;		 
	long	ru_nswap;		 
	long	ru_inblock;		 
	long	ru_oublock;		 
	long	ru_msgsnd;		 
	long	ru_msgrcv;		 
	long	ru_nsignals;		 
	long	ru_nvcsw;		 
	long	ru_nivcsw;		 
};



struct rlimit {
	long	rlim_cur;
	long	rlim_max;
};








 



# 1 "/usr/src/linux/include/asm/resource.h" 1



 



















# 36 "/usr/src/linux/include/asm/resource.h"




# 58 "/usr/src/linux/include/linux/resource.h" 2



# 71 "/usr/src/linux/include/linux/sched.h" 2

# 1 "/usr/src/linux/include/linux/timer.h" 1



 






















struct timer_struct {
	unsigned long expires;
	void (*fn)(void);
};

extern unsigned long timer_active;
extern struct timer_struct timer_table[32];

 












struct timer_list {
	struct timer_list *next;  
	struct timer_list *prev;
	unsigned long expires;
	unsigned long data;
	void (*function)(unsigned long);
};

extern void add_timer(struct timer_list * timer);
extern int  del_timer(struct timer_list * timer);

 




void mod_timer(struct timer_list *timer, unsigned long expires);

extern void it_real_fn(unsigned long);

extern inline void init_timer(struct timer_list * timer)
{
	timer->next = ((void *)0) ;
	timer->prev = ((void *)0) ;
}

extern inline int timer_pending(struct timer_list * timer)
{
	return timer->prev != ((void *)0) ;
}

 

















# 72 "/usr/src/linux/include/linux/sched.h" 2


# 1 "/usr/src/linux/include/asm/processor.h" 1
 








# 1 "/usr/src/linux/include/asm/vm86.h" 1



 





























 










 





 










 





struct vm86_regs {
 


	long ebx;
	long ecx;
	long edx;
	long esi;
	long edi;
	long ebp;
	long eax;
	long __null_ds;
	long __null_es;
	long __null_fs;
	long __null_gs;
	long orig_eax;
	long eip;
	unsigned short cs, __csh;
	long eflags;
	long esp;
	unsigned short ss, __ssh;
 


	unsigned short es, __esh;
	unsigned short ds, __dsh;
	unsigned short fs, __fsh;
	unsigned short gs, __gsh;
};

struct revectored_struct {
	unsigned long __map[8];			 
};

struct vm86_struct {
	struct vm86_regs regs;
	unsigned long flags;
	unsigned long screen_bitmap;
	unsigned long cpu_type;
	struct revectored_struct int_revectored;
	struct revectored_struct int21_revectored;
};

 




struct vm86plus_info_struct {
	unsigned long force_return_for_pic:1;
	unsigned long vm86dbg_active:1;        
	unsigned long vm86dbg_TFpendig:1;      
	unsigned long unused:28;
	unsigned long is_vm86pus:1;	       
	unsigned char vm86dbg_intxxtab[32];    
};

struct vm86plus_struct {
	struct vm86_regs regs;
	unsigned long flags;
	unsigned long screen_bitmap;
	unsigned long cpu_type;
	struct revectored_struct int_revectored;
	struct revectored_struct int21_revectored;
	struct vm86plus_info_struct vm86plus;
};


 








struct kernel_vm86_regs {
 


	long ebx;
	long ecx;
	long edx;
	long esi;
	long edi;
	long ebp;
	long eax;
	long __null_ds;
	long __null_es;
	long orig_eax;
	long eip;
	unsigned short cs, __csh;
	long eflags;
	long esp;
	unsigned short ss, __ssh;
 


	unsigned short es, __esh;
	unsigned short ds, __dsh;
	unsigned short fs, __fsh;
	unsigned short gs, __gsh;
};

struct kernel_vm86_struct {
	struct kernel_vm86_regs regs;
 








	unsigned long flags;
	unsigned long screen_bitmap;
	unsigned long cpu_type;
	struct revectored_struct int_revectored;
	struct revectored_struct int21_revectored;
	struct vm86plus_info_struct vm86plus;
	struct pt_regs *regs32;    
 









};

void handle_vm86_fault(struct kernel_vm86_regs *, long);
int handle_vm86_trap(struct kernel_vm86_regs *, long, int);




# 10 "/usr/src/linux/include/asm/processor.h" 2

# 1 "/usr/src/linux/include/asm/math_emu.h" 1





int restore_i387_soft(void *s387, struct _fpstate *buf);
int save_i387_soft(void *s387, struct _fpstate * buf);

 



struct info {
	long ___orig_eip;
	long ___ret_from_system_call;
	long ___ebx;
	long ___ecx;
	long ___edx;
	long ___esi;
	long ___edi;
	long ___ebp;
	long ___eax;
	long ___ds;
	long ___es;
	long ___orig_eax;
	long ___eip;
	long ___cs;
	long ___eflags;
	long ___esp;
	long ___ss;
	long ___vm86_es;  
	long ___vm86_ds;
	long ___vm86_fs;
	long ___vm86_gs;
};

# 11 "/usr/src/linux/include/asm/processor.h" 2




 





struct cpuinfo_x86 {
	__u8	x86;		 
	__u8	x86_vendor;	 
	__u8	x86_model;
	__u8	x86_mask;
	char	wp_works_ok;	 
	char	hlt_works_ok;	 
	char	hard_math;
	char	rfu;
	int	cpuid_level;	 
	__u32	x86_capability;
	char	x86_vendor_id[16];
	char	x86_model_id[64];
	int 	x86_cache_size;   

	int	fdiv_bug;
	int	f00f_bug;
	int	coma_bug;
	unsigned long loops_per_sec;
	unsigned long *pgd_quick;
	unsigned long *pte_quick;
	unsigned long pgtable_cache_sz;
};











 














 





















extern struct cpuinfo_x86 boot_cpu_data;









extern char ignore_irq13;

extern void identify_cpu(struct cpuinfo_x86 *);
extern void print_cpu_info(struct cpuinfo_x86 *);
extern void dodgy_tsc(void);

 


extern inline void cpuid(int op, int *eax, int *ebx, int *ecx, int *edx)
{
	__asm__("cpuid"
		: "=a" (*eax),
		  "=b" (*ebx),
		  "=c" (*ecx),
		  "=d" (*edx)
		: "a" (op)
		: "cc");
}

 














 










 


extern int EISA_bus;
extern int MCA_bus;

 

extern unsigned int machine_id;
extern unsigned int machine_submodel_id;
extern unsigned int BIOS_revision;
extern unsigned int mca_pentium_flag;

 




 




 




struct i387_hard_struct {
	long	cwd;
	long	swd;
	long	twd;
	long	fip;
	long	fcs;
	long	foo;
	long	fos;
	long	st_space[20];	 
	long	status;		 
};

struct i387_soft_struct {
	long	cwd;
	long	swd;
	long	twd;
	long	fip;
	long	fcs;
	long	foo;
	long	fos;
	long	st_space[20];	 
	unsigned char	ftop, changed, lookahead, no_update, rm, alimit;
	struct info	*info;
	unsigned long	entry_eip;
};

union i387_union {
	struct i387_hard_struct hard;
	struct i387_soft_struct soft;
};

typedef struct {
	unsigned long seg;
} mm_segment_t;

struct thread_struct {
	unsigned short	back_link,__blh;
	unsigned long	esp0;
	unsigned short	ss0,__ss0h;
	unsigned long	esp1;
	unsigned short	ss1,__ss1h;
	unsigned long	esp2;
	unsigned short	ss2,__ss2h;
	unsigned long	cr3;
	unsigned long	eip;
	unsigned long	eflags;
	unsigned long	eax,ecx,edx,ebx;
	unsigned long	esp;
	unsigned long	ebp;
	unsigned long	esi;
	unsigned long	edi;
	unsigned short	es, __esh;
	unsigned short	cs, __csh;
	unsigned short	ss, __ssh;
	unsigned short	ds, __dsh;
	unsigned short	fs, __fsh;
	unsigned short	gs, __gsh;
	unsigned short	ldt, __ldth;
	unsigned short	trace, bitmap;
	unsigned long	io_bitmap[32 +1];
	unsigned long	tr;
	unsigned long	cr2, trap_no, error_code;
	mm_segment_t	segment;
 
	long debugreg[8];   
 
	union i387_union i387;
 
	struct vm86_struct * vm86_info;
	unsigned long screen_bitmap;
	unsigned long v86flags, v86mask, v86mode, saved_esp0;
};





# 271 "/usr/src/linux/include/asm/processor.h"


# 282 "/usr/src/linux/include/asm/processor.h"

 
struct mm_struct;

 
extern void release_thread(struct task_struct *);
extern int kernel_thread(int (*fn)(void *), void * arg, unsigned long flags);

 
extern void copy_segments(int nr, struct task_struct *p, struct mm_struct * mm);
extern void release_segments(struct mm_struct * mm);
extern void forget_segments(void);

 




















 


extern inline unsigned long thread_saved_pc(struct thread_struct *t)
{
	return ((unsigned long *)t->esp)[3];
}

extern struct task_struct * alloc_task_struct(void);
extern void free_task_struct(struct task_struct *);





# 74 "/usr/src/linux/include/linux/sched.h" 2









 






 





struct sched_param {
	int sched_priority;
};





 





extern rwlock_t tasklist_lock;
extern spinlock_t runqueue_lock;

extern void sched_init(void);
extern void init_idle(void);
extern void show_state(void);
extern void trap_init(void);


extern signed long  schedule_timeout(signed long timeout)  __attribute__((regparm(3))) ;
  __attribute__((regparm(0)))  void schedule(void);

 





 


struct files_struct {
	atomic_t count;
	int max_fds;
	int max_fdset;
	int next_fd;
	struct file ** fd;	 
	fd_set *close_on_exec;
	fd_set *open_fds;
	fd_set close_on_exec_init;
	fd_set open_fds_init;
	struct file * fd_array[32  ];
};


# 156 "/usr/src/linux/include/linux/sched.h"

struct fs_struct {
	atomic_t count;
	int umask;
	struct dentry * root, * pwd;
};







 


 


struct mm_struct {
	struct vm_area_struct *mmap;		 
	struct vm_area_struct *mmap_avl;	 
	struct vm_area_struct *mmap_cache;	 
	pgd_t * pgd;
	atomic_t count;
	int map_count;				 
	struct semaphore mmap_sem;
	unsigned long context;
	unsigned long start_code, end_code, start_data, end_data;
	unsigned long start_brk, brk, start_stack;
	unsigned long arg_start, arg_end, env_start, env_end;
	unsigned long rss, total_vm, locked_vm;
	unsigned long def_flags;
	unsigned long cpu_vm_mask;
	unsigned long swap_cnt;	 
	unsigned long swap_address;
	 



	void * segments;
};


# 210 "/usr/src/linux/include/linux/sched.h"

struct signal_struct {
	atomic_t		count;
	struct k_sigaction	action[64 ];
	spinlock_t		siglock;
};







 




struct user_struct;

struct task_struct {
 
	volatile long state;	 
	unsigned long flags;	 
	int sigpending;
	mm_segment_t addr_limit;	 



	struct exec_domain *exec_domain;
	long need_resched;

 
	long counter;
	long priority;
	cycles_t avg_slice;
 
	int has_cpu;
	int processor;
	int last_processor;
	int lock_depth;		 	
	struct task_struct *next_task, *prev_task;
	struct task_struct *next_run,  *prev_run;

 
	struct linux_binfmt *binfmt;
	int exit_code, exit_signal;
	int pdeath_signal;   
	 
	unsigned long personality;
	int dumpable:1;
	int did_exec:1;
	pid_t pid;
	pid_t pgrp;
	pid_t tty_old_pgrp;
	pid_t session;
	 
	int leader;
	 




	struct task_struct *p_opptr, *p_pptr, *p_cptr, *p_ysptr, *p_osptr;

	 
	struct task_struct *pidhash_next;
	struct task_struct **pidhash_pprev;

	 
	struct task_struct **tarray_ptr;

	struct wait_queue *wait_chldexit;	 
	struct semaphore *vfork_sem;		 
	unsigned long policy, rt_priority;
	unsigned long it_real_value, it_prof_value, it_virt_value;
	unsigned long it_real_incr, it_prof_incr, it_virt_incr;
	struct timer_list real_timer;
	struct tms times;
	unsigned long start_time;
	long per_cpu_utime[1 ], per_cpu_stime[1 ];
 
	unsigned long min_flt, maj_flt, nswap, cmin_flt, cmaj_flt, cnswap;
	int swappable:1;
 
	uid_t uid,euid,suid,fsuid;
	gid_t gid,egid,sgid,fsgid;
	int ngroups;
	gid_t	groups[32 ];
        kernel_cap_t   cap_effective, cap_inheritable, cap_permitted;
	struct user_struct *user;
 
	struct rlimit rlim[10 ];
	unsigned short used_math;
	char comm[16];
 
	int link_count;
	struct tty_struct *tty;  
 
	struct sem_undo *semundo;
	struct sem_queue *semsleeping;
 
	struct thread_struct tss;
 
	struct fs_struct *fs;
 
	struct files_struct *files;
 
	struct mm_struct *mm;

 
	spinlock_t sigmask_lock;	 
	struct signal_struct *sig;
	sigset_t signal, blocked;
	struct signal_queue *sigqueue, **sigqueue_tail;
	unsigned long sas_ss_sp;
	size_t sas_ss_size;
	
 
   	u32 parent_exec_id;
   	u32 self_exec_id;

 
	int oom_kill_try;
};

 



					 














 







 




# 403 "/usr/src/linux/include/linux/sched.h"

union task_union {
	struct task_struct task;
	unsigned long stack[2048];
};

extern union task_union init_task_union;

extern struct   mm_struct init_mm;
extern struct task_struct *task[512 ];

extern struct task_struct **tarray_freelist;
extern spinlock_t taskslot_lock;

extern __inline__ void add_free_taskslot(struct task_struct **t)
{
	(void)( &taskslot_lock ) ;
	*t = (struct task_struct *) tarray_freelist;
	tarray_freelist = t;
	do { } while(0) ;
}

extern __inline__ struct task_struct **get_free_taskslot(void)
{
	struct task_struct **tslot;

	(void)( &taskslot_lock ) ;
	if((tslot = tarray_freelist) != ((void *)0) )
		tarray_freelist = (struct task_struct **) *tslot;
	do { } while(0) ;

	return tslot;
}

 

extern struct task_struct *pidhash[(512  >> 2) ];



extern __inline__ void hash_pid(struct task_struct *p)
{
	struct task_struct **htable = &pidhash[(((( p->pid ) >> 8) ^ ( p->pid )) & ((512  >> 2)  - 1)) ];

	if((p->pidhash_next = *htable) != ((void *)0) )
		(*htable)->pidhash_pprev = &p->pidhash_next;
	*htable = p;
	p->pidhash_pprev = htable;
}

extern __inline__ void unhash_pid(struct task_struct *p)
{
	if(p->pidhash_next)
		p->pidhash_next->pidhash_pprev = p->pidhash_pprev;
	*p->pidhash_pprev = p->pidhash_next;
}

extern __inline__ struct task_struct *find_task_by_pid(int pid)
{
	struct task_struct *p, **htable = &pidhash[(((( pid ) >> 8) ^ ( pid )) & ((512  >> 2)  - 1)) ];

	for(p = *htable; p && p->pid != pid; p = p->pidhash_next)
		;

	return p;
}

 
extern int alloc_uid(struct task_struct *p);
void free_uid(struct task_struct *p);

# 1 "/usr/src/linux/include/asm/current.h" 1



struct task_struct;

static inline struct task_struct * get_current(void)
{
	struct task_struct *current;
	__asm__("andl %%esp,%0; ":"=r" (current) : "0" (~8191UL));
	return current;
 }
 



# 474 "/usr/src/linux/include/linux/sched.h" 2


extern unsigned long volatile jiffies;
extern unsigned long itimer_ticks;
extern unsigned long itimer_next;
extern struct timeval xtime;
extern void do_timer(struct pt_regs *);

extern unsigned int * prof_buffer;
extern unsigned long prof_len;
extern unsigned long prof_shift;



extern void  __wake_up(struct wait_queue ** p, unsigned int mode)  __attribute__((regparm(3))) ;
extern void  sleep_on(struct wait_queue ** p)  __attribute__((regparm(3))) ;
extern long  sleep_on_timeout(struct wait_queue ** p,
				      signed long timeout)  __attribute__((regparm(3))) ;
extern void  interruptible_sleep_on(struct wait_queue ** p)  __attribute__((regparm(3))) ;
extern long  interruptible_sleep_on_timeout(struct wait_queue ** p,
						    signed long timeout)  __attribute__((regparm(3))) ;
extern void  wake_up_process(struct task_struct * tsk)  __attribute__((regparm(3))) ;




extern int in_group_p(gid_t grp);
extern int in_egroup_p(gid_t grp);

extern void flush_signals(struct task_struct *);
extern void flush_signal_handlers(struct task_struct *);
extern int dequeue_signal(sigset_t *block, siginfo_t *);
extern int send_sig_info(int, struct siginfo *info, struct task_struct *);
extern int force_sig_info(int, struct siginfo *info, struct task_struct *);
extern int kill_pg_info(int, struct siginfo *info, pid_t);
extern int kill_sl_info(int, struct siginfo *info, pid_t);
extern int kill_proc_info(int, struct siginfo *info, pid_t);
extern int kill_something_info(int, struct siginfo *info, int);
extern void notify_parent(struct task_struct * tsk, int);
extern void force_sig(int sig, struct task_struct * p);
extern int send_sig(int sig, struct task_struct * p, int priv);
extern int kill_pg(pid_t, int, int);
extern int kill_sl(pid_t, int, int);
extern int kill_proc(pid_t, int, int);
extern int do_sigaction(int sig, const struct k_sigaction *act,
			struct k_sigaction *oact);
extern int do_sigaltstack(const stack_t *ss, stack_t *oss, unsigned long sp);

extern inline int signal_pending(struct task_struct *p)
{
	return (p->sigpending != 0);
}

 



static inline void recalc_sigpending(struct task_struct *t)
{
	unsigned long ready;
	long i;

	switch ((64  / 32 ) ) {
	default:
		for (i = (64  / 32 ) , ready = 0; --i >= 0 ;)
			ready |= t->signal.sig[i] &~ t->blocked.sig[i];
		break;

	case 4: ready  = t->signal.sig[3] &~ t->blocked.sig[3];
		ready |= t->signal.sig[2] &~ t->blocked.sig[2];
		ready |= t->signal.sig[1] &~ t->blocked.sig[1];
		ready |= t->signal.sig[0] &~ t->blocked.sig[0];
		break;

	case 2: ready  = t->signal.sig[1] &~ t->blocked.sig[1];
		ready |= t->signal.sig[0] &~ t->blocked.sig[0];
		break;

	case 1: ready  = t->signal.sig[0] &~ t->blocked.sig[0];
	}

	t->sigpending = (ready != 0);
}

 

static inline int on_sig_stack(unsigned long sp)
{
	return (sp >= get_current() ->sas_ss_sp
		&& sp < get_current() ->sas_ss_sp + get_current() ->sas_ss_size);
}

static inline int sas_ss_flags(unsigned long sp)
{
	return (get_current() ->sas_ss_size == 0 ? 2 
		: on_sig_stack(sp) ? 1  : 0);
}

extern int request_irq(unsigned int irq,
		       void (*handler)(int, void *, struct pt_regs *),
		       unsigned long flags, 
		       const char *device,
		       void *dev_id);
extern void free_irq(unsigned int irq, void *dev_id);

 













extern inline int suser(void)
{
	if (! ( (1 << ( 0  +1)) & 0x00000000  ? (1 << ( 0  )) & 0x00000000  :	(1 << ( 0  )) & securebits )  && get_current() ->euid == 0) { 
		get_current() ->flags |= 0x00000100 ;
		return 1;
	}
	return 0;
}

extern inline int fsuser(void)
{
	if (! ( (1 << ( 0  +1)) & 0x00000000  ? (1 << ( 0  )) & 0x00000000  :	(1 << ( 0  )) & securebits )  && get_current() ->fsuid == 0) {
		get_current() ->flags |= 0x00000100 ;
		return 1;
	}
	return 0;
}

 





extern inline int capable(int cap)
{

	if (((  get_current() ->cap_effective  )  & (1 << (   cap  )) ) )



        {
		get_current() ->flags |= 0x00000100 ;
		return 1;
	}
	return 0;
}

 


extern struct mm_struct * mm_alloc(void);
static inline void mmget(struct mm_struct * mm)
{
	atomic_inc(&mm->count);
}
extern void mmput(struct mm_struct *);
 
extern void mm_release(void);

 


extern struct file ** alloc_fd_array(int);
extern int expand_fd_array(struct files_struct *, int nr);
extern void free_fd_array(struct file **, int);

extern fd_set *alloc_fdset(int);
extern int expand_fdset(struct files_struct *, int nr);
extern void free_fdset(fd_set *, int);

 

static inline int expand_files(struct files_struct *files, int nr)
{
	int err, expand = 0;



	
	if (nr >= files->max_fdset) {
		expand = 1;
		if ((err = expand_fdset(files, nr + 1)))
			goto out;
	}
	if (nr >= files->max_fds) {
		expand = 1;
		if ((err = expand_fd_array(files, nr + 1)))
			goto out;
	}
	err = expand;
 out:




	return err;
}

extern int  copy_thread(int, unsigned long, unsigned long, struct task_struct *, struct pt_regs *);
extern void flush_thread(void);
extern void exit_thread(void);

extern void exit_mm(struct task_struct *);
extern void exit_fs(struct task_struct *);
extern void exit_files(struct task_struct *);
extern void exit_sighand(struct task_struct *);

extern int do_execve(char *, char **, char **, struct pt_regs *);
extern int do_fork(unsigned long, unsigned long, struct pt_regs *);

 




extern inline void __add_wait_queue(struct wait_queue ** p, struct wait_queue * wait)
{
//	wait->next = *p ? : ((struct wait_queue *)(( p )-1)) ;   // INVALID
	*p = wait;
}

extern rwlock_t waitqueue_lock;

extern inline void add_wait_queue(struct wait_queue ** p, struct wait_queue * wait)
{
	unsigned long flags;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	__add_wait_queue(p, wait);
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
}

extern inline void __remove_wait_queue(struct wait_queue ** p, struct wait_queue * wait)
{
	struct wait_queue * next = wait->next;
	struct wait_queue * head = next;
	struct wait_queue * tmp;

	while ((tmp = head->next) != wait) {
		head = tmp;
	}
	head->next = next;
}

extern inline void remove_wait_queue(struct wait_queue ** p, struct wait_queue * wait)
{
	unsigned long flags;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	__remove_wait_queue(p, wait);
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ; 
}


# 753 "/usr/src/linux/include/linux/sched.h"









# 782 "/usr/src/linux/include/linux/sched.h"
	









# 801 "/usr/src/linux/include/linux/sched.h"


# 812 "/usr/src/linux/include/linux/sched.h"







# 21 "pc_keyb.c" 2

# 1 "/usr/src/linux/include/linux/interrupt.h" 1
 







struct irqaction {
	void (*handler)(int, void *, struct pt_regs *);
	unsigned long flags;
	unsigned long mask;
	const char *name;
	void *dev_id;
	struct irqaction *next;
};

extern volatile unsigned char bh_running;

extern atomic_t bh_mask_count[32];
extern unsigned long bh_active;
extern unsigned long bh_mask;
extern void (*bh_base[32])(void);

  __attribute__((regparm(0)))  void do_bottom_half(void);

 

   
enum {
	TIMER_BH = 0,
	CONSOLE_BH,
	TQUEUE_BH,
	DIGI_BH,
	SERIAL_BH,
	RISCOM8_BH,
	SPECIALIX_BH,
	AURORA_BH,
	ESP_BH,
	NET_BH,
	SCSI_BH,
	IMMEDIATE_BH,
	KEYBOARD_BH,
	CYCLADES_BH,
	CM206_BH,
	JS_BH,
	MACSERIAL_BH,
	ISICOM_BH
};

# 1 "/usr/src/linux/include/asm/hardirq.h" 1





extern unsigned int local_irq_count[1 ];

 
















# 63 "/usr/src/linux/include/asm/hardirq.h"



# 51 "/usr/src/linux/include/linux/interrupt.h" 2

# 1 "/usr/src/linux/include/asm/softirq.h" 1






extern unsigned int local_bh_count[1 ];








# 58 "/usr/src/linux/include/asm/softirq.h"


extern inline void start_bh_atomic(void)
{
	local_bh_count[0 ]++;
	__asm__ __volatile__("": : :"memory") ;
}

extern inline void end_bh_atomic(void)
{
	__asm__ __volatile__("": : :"memory") ;
	local_bh_count[0 ]--;
}

 






extern inline void init_bh(int nr, void (*routine)(void))
{
	unsigned long flags;

	bh_base[nr] = routine;
	((( &bh_mask_count[nr] )->counter) = (  0 )) ;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	bh_mask |= 1 << nr;
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
}

extern inline void remove_bh(int nr)
{
	unsigned long flags;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	bh_mask &= ~(1 << nr);
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;

	__asm__ __volatile__("": : :"memory")  ;
	bh_base[nr] = ((void *)0) ;
}

extern inline void mark_bh(int nr)
{
	set_bit(nr, &bh_active);
}

 



extern inline void disable_bh(int nr)
{
	unsigned long flags;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	bh_mask &= ~(1 << nr);
	atomic_inc(&bh_mask_count[nr]);
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
	__asm__ __volatile__("": : :"memory")  ;
}

extern inline void enable_bh(int nr)
{
	unsigned long flags;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	if (atomic_dec_and_test(&bh_mask_count[nr]))
		bh_mask |= 1 << nr;
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
}


# 52 "/usr/src/linux/include/linux/interrupt.h" 2


 


























extern unsigned long probe_irq_on(void);	 
extern int probe_irq_off(unsigned long);	 


# 22 "pc_keyb.c" 2


# 1 "/usr/src/linux/include/linux/mm.h" 1










extern unsigned long max_mapnr;
extern unsigned long num_physpages;
extern void * high_memory;
extern int page_cluster;




 








 





struct vm_area_struct {
	struct mm_struct * vm_mm;	 
	unsigned long vm_start;
	unsigned long vm_end;

	 
	struct vm_area_struct *vm_next;

	pgprot_t vm_page_prot;
	unsigned short vm_flags;

	 
	short vm_avl_height;
	struct vm_area_struct * vm_avl_left;
	struct vm_area_struct * vm_avl_right;

	 


	struct vm_area_struct *vm_next_share;
	struct vm_area_struct **vm_pprev_share;

	struct vm_operations_struct * vm_ops;
	unsigned long vm_offset;
	struct file * vm_file;
	unsigned long vm_pte;			 
};

 























 



extern pgprot_t protection_map[16];


 




struct vm_operations_struct {
	void (*open)(struct vm_area_struct * area);
	void (*close)(struct vm_area_struct * area);
	void (*unmap)(struct vm_area_struct *area, unsigned long, size_t);
	void (*protect)(struct vm_area_struct *area, unsigned long, size_t, unsigned int newprot);
	int (*sync)(struct vm_area_struct *area, unsigned long, size_t, unsigned int flags);
	void (*advise)(struct vm_area_struct *area, unsigned long, size_t, unsigned int advise);
	unsigned long (*nopage)(struct vm_area_struct * area, unsigned long address, int write_access);
	unsigned long (*wppage)(struct vm_area_struct * area, unsigned long address,
		unsigned long page);
	int (*swapout)(struct vm_area_struct *, struct page *);
	pte_t (*swapin)(struct vm_area_struct *, unsigned long, unsigned long);
};

 







typedef struct page {
	 
	struct page *next;
	struct page *prev;
	struct inode *inode;
	unsigned long offset;
	struct page *next_hash;
	atomic_t count;
	unsigned long flags;	 
	struct wait_queue *wait;
	struct page **pprev_hash;
	struct buffer_head * buffers;
} mem_map_t;

 














 





























 







































































extern mem_map_t * mem_map;

 






extern unsigned long  __get_free_pages(int gfp_mask, unsigned long gfp_order)  __attribute__((regparm(3))) ;

extern inline unsigned long get_free_page(int gfp_mask)
{
	unsigned long page;

	page = __get_free_pages(( gfp_mask ),0) ;
	if (page)
		(__builtin_constant_p(  0 ) ? (__builtin_constant_p( (  (1UL << 12 )  ) ) ? __constant_c_and_count_memset(( ( (void *)( page ) ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  (1UL << 12 )  ) )) : __constant_c_memset(( ( (void *)( page ) ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  (1UL << 12 )  ) )))  : (__builtin_constant_p( (  (1UL << 12 )  ) ) ? __memset_generic(( ( ( (void *)( page ) ) ) ),( ( (  0 ) ) ),( ( (  (1UL << 12 )  ) ) ))  : __memset_generic(( ( (void *)( page ) ) ),( (  0 ) ),( (  (1UL << 12 )  ) ))) )  ;
	return page;
}

extern int low_on_memory;

 


extern void  free_pages(unsigned long addr, unsigned long order)  __attribute__((regparm(3))) ;

extern void  __free_pages(struct page *, unsigned long)  __attribute__((regparm(3))) ;

extern void show_free_areas(void);
extern unsigned long put_dirty_page(struct task_struct * tsk,unsigned long page,
	unsigned long address);

extern void free_page_tables(struct mm_struct * mm);
extern void clear_page_tables(struct mm_struct *, unsigned long, int);
extern int new_page_tables(struct task_struct * tsk);

extern void zap_page_range(struct mm_struct *mm, unsigned long address, unsigned long size);
extern int copy_page_range(struct mm_struct *dst, struct mm_struct *src, struct vm_area_struct *vma);
extern int remap_page_range(unsigned long from, unsigned long to, unsigned long size, pgprot_t prot);
extern int zeromap_page_range(unsigned long from, unsigned long size, pgprot_t prot);

extern void vmtruncate(struct inode * inode, unsigned long offset);
extern int handle_mm_fault(struct task_struct *tsk,struct vm_area_struct *vma, unsigned long address, int write_access);
extern int make_pages_present(unsigned long addr, unsigned long end);

extern int pgt_cache_water[2];
extern int check_pgt_cache(void);

extern unsigned long paging_init(unsigned long start_mem, unsigned long end_mem);
extern void mem_init(unsigned long start_mem, unsigned long end_mem);
extern void show_mem(void);
extern void si_meminfo(struct sysinfo * val);

 
extern void vma_init(void);
extern void merge_segments(struct mm_struct *, unsigned long, unsigned long);
extern void insert_vm_struct(struct mm_struct *, struct vm_area_struct *);
extern void build_mmap_avl(struct mm_struct *);
extern void exit_mmap(struct mm_struct *);
extern unsigned long get_unmapped_area(unsigned long, unsigned long);

extern unsigned long do_mmap(struct file *, unsigned long, unsigned long,
	unsigned long, unsigned long, unsigned long);
extern int do_munmap(unsigned long, size_t);

 
extern void remove_inode_page(struct page *);
extern unsigned long page_unuse(struct page *);
extern int shrink_mmap(int, int);
extern void truncate_inode_pages(struct inode *, unsigned long);
extern unsigned long get_cached_page(struct inode *, unsigned long, int);
extern void put_cached_page(unsigned long);

 


















 




 

static inline int expand_stack(struct vm_area_struct * vma, unsigned long address)
{
	unsigned long grow;

	address &= (~((1UL << 12 ) -1)) ;
	grow = vma->vm_start - address;
	if ((vma->vm_end - address
	    > get_current() ->rlim[3 ].rlim_cur) ||
	    ((get_current() ->rlim[9 ].rlim_cur < ((long)(~0UL>>1)) ) &&
	    ((vma->vm_mm->total_vm << 12 ) + grow
	    > get_current() ->rlim[9 ].rlim_cur)))
		return - 12 ;
	vma->vm_start = address;
	vma->vm_offset -= grow;
	vma->vm_mm->total_vm += grow >> 12 ;
	if (vma->vm_flags & 0x2000 )
		vma->vm_mm->locked_vm += grow >> 12 ;
	return 0;
}

 
extern struct vm_area_struct * find_vma(struct mm_struct * mm, unsigned long addr);

 

static inline struct vm_area_struct * find_vma_intersection(struct mm_struct * mm, unsigned long start_addr, unsigned long end_addr)
{
	struct vm_area_struct * vma = find_vma(mm,start_addr);

	if (vma && end_addr <= vma->vm_start)
		vma = ((void *)0) ;
	return vma;
}









# 24 "pc_keyb.c" 2


# 1 "/usr/src/linux/include/linux/init.h" 1



 







































 






# 1 "/usr/src/linux/include/asm/init.h" 1








 








# 51 "/usr/src/linux/include/linux/init.h" 2

# 60 "/usr/src/linux/include/linux/init.h"









# 26 "pc_keyb.c" 2

# 1 "/usr/src/linux/include/linux/kbd_ll.h" 1
 






extern struct pt_regs *kbd_pt_regs;

void handle_scancode(unsigned char scancode, int down);


# 27 "pc_keyb.c" 2

# 1 "/usr/src/linux/include/linux/delay.h" 1



 





extern unsigned long loops_per_sec;

# 1 "/usr/src/linux/include/asm/delay.h" 1



 




 
extern void __const_udelay(unsigned long usecs);
extern void __udelay(unsigned long usecs);
extern void __delay(unsigned long loops);





	

# 12 "/usr/src/linux/include/linux/delay.h" 2


 























# 28 "pc_keyb.c" 2

# 1 "/usr/src/linux/include/linux/random.h" 1
 










 

 


 


 


 





 


 


struct rand_pool_info {
	int	entropy_count;
	int	buf_size;
	__u32	buf[0];
};

 



extern void rand_initialize(void);
extern void rand_initialize_irq(int irq);
extern void rand_initialize_blkdev(int irq, int mode);

extern void add_keyboard_randomness(unsigned char scancode);
extern void add_mouse_randomness(__u32 mouse_data);
extern void add_interrupt_randomness(int irq);
extern void add_blkdev_randomness(int major);

extern void get_random_bytes(void *buf, int nbytes);

extern __u32 secure_tcp_sequence_number(__u32 saddr, __u32 daddr,
					__u16 sport, __u16 dport);
extern __u32 secure_tcp_syn_cookie(__u32 saddr, __u32 daddr,
				   __u16 sport, __u16 dport,
				   __u32 sseq, __u32 count,
				   __u32 data);
extern __u32 check_tcp_syn_cookie(__u32 cookie, __u32 saddr,
				  __u32 daddr, __u16 sport,
				  __u16 dport, __u32 sseq,
				  __u32 count, __u32 maxdiff);


extern struct file_operations random_fops, urandom_fops;





# 29 "pc_keyb.c" 2

# 1 "/usr/src/linux/include/linux/poll.h" 1



# 1 "/usr/src/linux/include/asm/poll.h" 1



 







 






struct pollfd {
	int fd;
	short events;
	short revents;
};


# 4 "/usr/src/linux/include/linux/poll.h" 2







# 1 "/usr/src/linux/include/asm/uaccess.h" 1



 









 



















extern int __verify_write(const void *, unsigned long);



 






















extern inline int verify_area(int type, const void * addr, unsigned long size)
{
	return (({ unsigned long flag,sum; asm("addl %3,%1 ; sbbl %0,%0; cmpl %1,%4; sbbl $0,%0" :"=&r" (flag), "=r" (sum) :"1" (  addr  ),"g" ((int)  size  ),"g" (get_current() ->addr_limit.seg)); flag; })  == 0)  ? 0 : - 14 ;
}


 












struct exception_table_entry
{
	unsigned long insn, fixup;
};

 
extern unsigned long search_exception_table(unsigned long);


 














extern void __get_user_1(void);
extern void __get_user_2(void);
extern void __get_user_4(void);






 

# 125 "/usr/src/linux/include/asm/uaccess.h"

extern void __put_user_1(void);
extern void __put_user_2(void);
extern void __put_user_4(void);

extern void __put_user_bad(void);








# 148 "/usr/src/linux/include/asm/uaccess.h"














# 171 "/usr/src/linux/include/asm/uaccess.h"

struct __large_struct { unsigned long buf[100]; };


 





# 194 "/usr/src/linux/include/asm/uaccess.h"










extern long __get_user_bad(void);


# 216 "/usr/src/linux/include/asm/uaccess.h"


# 232 "/usr/src/linux/include/asm/uaccess.h"

 














 



 

# 274 "/usr/src/linux/include/asm/uaccess.h"


# 302 "/usr/src/linux/include/asm/uaccess.h"

 


static inline unsigned long
__generic_copy_from_user_nocheck(void *to, const void *from, unsigned long n)
{
	do {	int __d0, __d1;	__asm__ __volatile__(	"0:	rep; movsl\n"	"	movl %3,%0\n"	"1:	rep; movsb\n"	"2:\n"	".section .fixup,\"ax\"\n"	"3:	lea 0(%3,%0,4),%0\n"	"4:	pushl %0\n"	"	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	rep; stosb\n"	"	popl %%eax\n"	"	popl %0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,3b\n"	"	.long 1b,4b\n"	".previous"	: "=&c"( n ), "=&D" (__d0), "=&S" (__d1)	: "r"( n  & 3), "0"( n  / 4), "1"( to ), "2"( from )	: "memory");	} while (0) ;
	return n;
}

static inline unsigned long
__generic_copy_to_user_nocheck(void *to, const void *from, unsigned long n)
{
	do {	int __d0, __d1;	__asm__ __volatile__(	"0:	rep; movsl\n"	"	movl %3,%0\n"	"1:	rep; movsb\n"	"2:\n"	".section .fixup,\"ax\"\n"	"3:	lea 0(%3,%0,4),%0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,3b\n"	"	.long 1b,2b\n"	".previous"	: "=&c"( n ), "=&D" (__d0), "=&S" (__d1)	: "r"( n  & 3), "0"( n  / 4), "1"( to ), "2"( from )	: "memory");	} while (0) ;
	return n;
}


 

# 404 "/usr/src/linux/include/asm/uaccess.h"

 

# 540 "/usr/src/linux/include/asm/uaccess.h"

unsigned long __generic_copy_to_user(void *, const void *, unsigned long);
unsigned long __generic_copy_from_user(void *, const void *, unsigned long);

static inline unsigned long
__constant_copy_to_user(void *to, const void *from, unsigned long n)
{
	if ((({ unsigned long flag,sum; asm("addl %3,%1 ; sbbl %0,%0; cmpl %1,%4; sbbl $0,%0" :"=&r" (flag), "=r" (sum) :"1" (   to  ),"g" ((int)   n  ),"g" (get_current() ->addr_limit.seg)); flag; })  == 0) )
		do {	int __d0, __d1;	switch ( n  & 3) {	default:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:\n"	".section .fixup,\"ax\"\n"	"2:	shl $2,%0\n"	"	jmp 1b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,2b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 1:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsb\n"	"2:\n"	".section .fixup,\"ax\"\n"	"3:	shl $2,%0\n"	"4:	incl %0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,3b\n"	"	.long 1b,4b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 2:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsw\n"	"2:\n"	".section .fixup,\"ax\"\n"	"3:	shl $2,%0\n"	"4:	addl $2,%0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,3b\n"	"	.long 1b,4b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 3:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsw\n"	"2:	movsb\n"	"3:\n"	".section .fixup,\"ax\"\n"	"4:	shl $2,%0\n"	"5:	addl $2,%0\n"	"6:	incl %0\n"	"	jmp 3b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,4b\n"	"	.long 1b,5b\n"	"	.long 2b,6b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	}	} while (0) ;
	return n;
}

static inline unsigned long
__constant_copy_from_user(void *to, const void *from, unsigned long n)
{
	if ((({ unsigned long flag,sum; asm("addl %3,%1 ; sbbl %0,%0; cmpl %1,%4; sbbl $0,%0" :"=&r" (flag), "=r" (sum) :"1" (   from  ),"g" ((int)   n  ),"g" (get_current() ->addr_limit.seg)); flag; })  == 0) )
		do {	int __d0, __d1;	switch ( n  & 3) {	default:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:\n"	".section .fixup,\"ax\"\n"	"2:	pushl %0\n"	"	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	rep; stosl\n"	"	popl %%eax\n"	"	popl %0\n"	"	shl $2,%0\n"	"	jmp 1b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,2b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 1:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsb\n"	"2:\n"	".section .fixup,\"ax\"\n"	"3:	pushl %0\n"	"	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	rep; stosl\n"	"	stosb\n"	"	popl %%eax\n"	"	popl %0\n"	"	shl $2,%0\n"	"	incl %0\n"	"	jmp 2b\n"	"4:	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	stosb\n"	"	popl %%eax\n"	"	incl %0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,3b\n"	"	.long 1b,4b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 2:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsw\n"	"2:\n"	".section .fixup,\"ax\"\n"	"3:	pushl %0\n"	"	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	rep; stosl\n"	"	stosw\n"	"	popl %%eax\n"	"	popl %0\n"	"	shl $2,%0\n"	"	addl $2,%0\n"	"	jmp 2b\n"	"4:	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	stosw\n"	"	popl %%eax\n"	"	addl $2,%0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,3b\n"	"	.long 1b,4b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 3:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsw\n"	"2:	movsb\n"	"3:\n"	".section .fixup,\"ax\"\n"	"4:	pushl %0\n"	"	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	rep; stosl\n"	"	stosw\n"	"	stosb\n"	"	popl %%eax\n"	"	popl %0\n"	"	shl $2,%0\n"	"	addl $3,%0\n"	"	jmp 2b\n"	"5:	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	stosw\n"	"	stosb\n"	"	popl %%eax\n"	"	addl $3,%0\n"	"	jmp 2b\n"	"6:	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	stosb\n"	"	popl %%eax\n"	"	incl %0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,4b\n"	"	.long 1b,5b\n"	"	.long 2b,6b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	}	} while (0) ;
	return n;
}

static inline unsigned long
__constant_copy_to_user_nocheck(void *to, const void *from, unsigned long n)
{
	do {	int __d0, __d1;	switch ( n  & 3) {	default:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:\n"	".section .fixup,\"ax\"\n"	"2:	shl $2,%0\n"	"	jmp 1b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,2b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 1:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsb\n"	"2:\n"	".section .fixup,\"ax\"\n"	"3:	shl $2,%0\n"	"4:	incl %0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,3b\n"	"	.long 1b,4b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 2:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsw\n"	"2:\n"	".section .fixup,\"ax\"\n"	"3:	shl $2,%0\n"	"4:	addl $2,%0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,3b\n"	"	.long 1b,4b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 3:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsw\n"	"2:	movsb\n"	"3:\n"	".section .fixup,\"ax\"\n"	"4:	shl $2,%0\n"	"5:	addl $2,%0\n"	"6:	incl %0\n"	"	jmp 3b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,4b\n"	"	.long 1b,5b\n"	"	.long 2b,6b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	}	} while (0) ;
	return n;
}

static inline unsigned long
__constant_copy_from_user_nocheck(void *to, const void *from, unsigned long n)
{
	do {	int __d0, __d1;	switch ( n  & 3) {	default:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:\n"	".section .fixup,\"ax\"\n"	"2:	pushl %0\n"	"	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	rep; stosl\n"	"	popl %%eax\n"	"	popl %0\n"	"	shl $2,%0\n"	"	jmp 1b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,2b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 1:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsb\n"	"2:\n"	".section .fixup,\"ax\"\n"	"3:	pushl %0\n"	"	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	rep; stosl\n"	"	stosb\n"	"	popl %%eax\n"	"	popl %0\n"	"	shl $2,%0\n"	"	incl %0\n"	"	jmp 2b\n"	"4:	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	stosb\n"	"	popl %%eax\n"	"	incl %0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,3b\n"	"	.long 1b,4b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 2:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsw\n"	"2:\n"	".section .fixup,\"ax\"\n"	"3:	pushl %0\n"	"	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	rep; stosl\n"	"	stosw\n"	"	popl %%eax\n"	"	popl %0\n"	"	shl $2,%0\n"	"	addl $2,%0\n"	"	jmp 2b\n"	"4:	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	stosw\n"	"	popl %%eax\n"	"	addl $2,%0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,3b\n"	"	.long 1b,4b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	case 3:	__asm__ __volatile__(	"0:	rep; movsl\n"	"1:	movsw\n"	"2:	movsb\n"	"3:\n"	".section .fixup,\"ax\"\n"	"4:	pushl %0\n"	"	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	rep; stosl\n"	"	stosw\n"	"	stosb\n"	"	popl %%eax\n"	"	popl %0\n"	"	shl $2,%0\n"	"	addl $3,%0\n"	"	jmp 2b\n"	"5:	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	stosw\n"	"	stosb\n"	"	popl %%eax\n"	"	addl $3,%0\n"	"	jmp 2b\n"	"6:	pushl %%eax\n"	"	xorl %%eax,%%eax\n"	"	stosb\n"	"	popl %%eax\n"	"	incl %0\n"	"	jmp 2b\n"	".previous\n"	".section __ex_table,\"a\"\n"	"	.align 4\n"	"	.long 0b,4b\n"	"	.long 1b,5b\n"	"	.long 2b,6b\n"	".previous"	: "=c"( n ), "=&S" (__d0), "=&D" (__d1)	: "1"( from ), "2"( to ), "0"( n /4)	: "memory");	break;	}	} while (0) ;
	return n;
}

























long strncpy_from_user(char *dst, const char *src, long count);
long __strncpy_from_user(char *dst, const char *src, long count);

long strnlen_user(const char *str, long n);
unsigned long clear_user(void *mem, unsigned long len);
unsigned long __clear_user(void *mem, unsigned long len);


# 11 "/usr/src/linux/include/linux/poll.h" 2



struct poll_table_entry {
	struct file * filp;
	struct wait_queue wait;
	struct wait_queue ** wait_address;
};

typedef struct poll_table_struct {
	struct poll_table_struct * next;
	unsigned int nr;
	struct poll_table_entry * entry;
} poll_table;



extern void __pollwait(struct file * filp, struct wait_queue ** wait_address, poll_table *p);

extern inline void poll_wait(struct file * filp, struct wait_queue ** wait_address, poll_table *p)
{
	if (p && wait_address)
		__pollwait(filp, wait_address, p);
}

 














typedef unsigned long kernel_fd_set[((((1UL << 12 ) /(6*64))*64) *8 > (1024*1024)  ? (1024*1024)  : (((1UL << 12 ) /(6*64))*64) *8) / (8 * sizeof(unsigned long)) ];

 



typedef struct {
	unsigned long *in, *out, *ex;
	unsigned long *res_in, *res_out, *res_ex;
} fd_set_bits;

 






 





static inline
int get_fd_set(unsigned long nr, void *ufdset, unsigned long *fdset)
{
	nr = ((((  nr  )+ (8*sizeof(long)) -1)/ (8*sizeof(long)) ) *sizeof(long)) ;   // AMBIGUOUS
	if (ufdset) {
		int error;
		error = verify_area(1 , ufdset, nr);
		if (!error && (__builtin_constant_p(  nr ) ?	__constant_copy_from_user_nocheck(( fdset ),(  ufdset ),(  nr )) :	__generic_copy_from_user_nocheck(( fdset ),(  ufdset ),(  nr ))) )
			error = - 14 ;
		return error;
	}
	(__builtin_constant_p(  0 ) ? (__builtin_constant_p( (  nr ) ) ? __constant_c_and_count_memset(( ( fdset ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  nr ) )) : __constant_c_memset(( ( fdset ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  nr ) )))  : (__builtin_constant_p( (  nr ) ) ? __memset_generic(( ( ( fdset ) ) ),( ( (  0 ) ) ),( ( (  nr ) ) ))  : __memset_generic(( ( fdset ) ),( (  0 ) ),( (  nr ) ))) ) ;
	return 0;
}

static inline
void set_fd_set(unsigned long nr, void *ufdset, unsigned long *fdset)
{
	if (ufdset)
		(__builtin_constant_p(  ((((  nr  )+ (8*sizeof(long)) -1)/ (8*sizeof(long)) ) *sizeof(long))  ) ?	__constant_copy_to_user_nocheck(( ufdset ),(  fdset ),(  ((((  nr  )+ (8*sizeof(long)) -1)/ (8*sizeof(long)) ) *sizeof(long))  )) :	__generic_copy_to_user_nocheck(( ufdset ),(  fdset ),(  ((((  nr  )+ (8*sizeof(long)) -1)/ (8*sizeof(long)) ) *sizeof(long))  ))) ;   // AMBIGUOUS
}

static inline
void zero_fd_set(unsigned long nr, unsigned long *fdset)
{
        (__builtin_constant_p(  0 ) ? (__builtin_constant_p( (  ((((  nr  )+ (8*sizeof(long)) -1)/ (8*sizeof(long)) ) *sizeof(long))  ) ) ? __constant_c_and_count_memset(( ( fdset ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  ((((  nr  )+ (8*sizeof(long)) -1)/ (8*sizeof(long)) ) *sizeof(long))  ) )) : __constant_c_memset(( ( fdset ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  ((((  nr  )+ (8*sizeof(long)) -1)/ (8*sizeof(long)) ) *sizeof(long))  ) )))  : (__builtin_constant_p( (  ((((  nr  )+ (8*sizeof(long)) -1)/ (8*sizeof(long)) ) *sizeof(long))  ) ) ? __memset_generic(( ( ( fdset ) ) ),( ( (  0 ) ) ),( ( (  ((((  nr  )+ (8*sizeof(long)) -1)/ (8*sizeof(long)) ) *sizeof(long))  ) ) ))  : __memset_generic(( ( fdset ) ),( (  0 ) ),( (  ((((  nr  )+ (8*sizeof(long)) -1)/ (8*sizeof(long)) ) *sizeof(long))  ) ))) ) ;  // AMBIGUOUS
}

extern int do_select(int n, fd_set_bits *fds, long *timeout);




# 30 "pc_keyb.c" 2

# 1 "/usr/src/linux/include/linux/miscdevice.h" 1


























 


extern int misc_init(void);

struct miscdevice 
{
	int minor;
	const char *name;
	struct file_operations *fops;
	struct miscdevice * next, * prev;
};

extern int misc_register(struct miscdevice * misc);
extern int misc_deregister(struct miscdevice * misc);


# 31 "pc_keyb.c" 2

# 1 "/usr/src/linux/include/linux/malloc.h" 1



# 1 "/usr/src/linux/include/linux/slab.h" 1
 










typedef struct kmem_cache_s kmem_cache_t;




 










 













 




 
extern long kmem_cache_init(long, long);
extern void kmem_cache_sizes_init(void);
extern kmem_cache_t *kmem_find_general_cachep(size_t);
extern kmem_cache_t *kmem_cache_create(const char *, size_t, size_t, unsigned long,
				       void (*)(void *, kmem_cache_t *, unsigned long),
				       void (*)(void *, kmem_cache_t *, unsigned long));
extern int kmem_cache_shrink(kmem_cache_t *);
extern void *kmem_cache_alloc(kmem_cache_t *, int);
extern void kmem_cache_free(kmem_cache_t *, void *);

extern void *kmalloc(size_t, int);
extern void kfree(const void *);
extern void kfree_s(const void *, size_t);

extern void kmem_cache_reap(int);
extern int get_slabinfo(char *);

 
extern kmem_cache_t	*vm_area_cachep;
extern kmem_cache_t	*mm_cachep;




# 4 "/usr/src/linux/include/linux/malloc.h" 2


# 32 "pc_keyb.c" 2


# 1 "/usr/src/linux/include/asm/keyboard.h" 1
 





 









# 1 "/usr/src/linux/include/linux/ioport.h" 1
 












 




extern void reserve_setup(char *str, int *ints);
extern int check_region(unsigned long from, unsigned long extent);
extern void request_region(unsigned long from, unsigned long extent,const char *name);
extern void release_region(unsigned long from, unsigned long extent);
extern int get_ioport_list(char *);








extern void autoirq_setup(int waittime);
extern int autoirq_report(int waittime);


# 17 "/usr/src/linux/include/asm/keyboard.h" 2

# 1 "/usr/src/linux/include/asm/io.h" 1



 












 










  















 

































extern inline unsigned char  inb  (unsigned short port) { unsigned char  _v;  __asm__ __volatile__ ("in" "b" " %"  "w"  "1,%"   ""   "0"  : "=a" (_v) : "Nd" (port)   ); return _v; } extern inline unsigned char  inb_p (unsigned short port) { unsigned char  _v;  __asm__ __volatile__ ("in" "b" " %"  "w"  "1,%"   ""   "0"  "\noutb %%al,$0x80"   : "=a" (_v) : "Nd" (port)   ); return _v; } 


extern inline unsigned short  inw  (unsigned short port) { unsigned short  _v;  __asm__ __volatile__ ("in" "w" " %"  "w"  "1,%"   ""   "0"  : "=a" (_v) : "Nd" (port)   ); return _v; } extern inline unsigned short  inw_p (unsigned short port) { unsigned short  _v;  __asm__ __volatile__ ("in" "w" " %"  "w"  "1,%"   ""   "0"  "\noutb %%al,$0x80"   : "=a" (_v) : "Nd" (port)   ); return _v; } 


extern inline unsigned int  inl  (unsigned short port) { unsigned int  _v;  __asm__ __volatile__ ("in" "l" " %"  "w"  "1,%"   ""   "0"  : "=a" (_v) : "Nd" (port)   ); return _v; } extern inline unsigned int  inl_p (unsigned short port) { unsigned int  _v;  __asm__ __volatile__ ("in" "l" " %"  "w"  "1,%"   ""   "0"  "\noutb %%al,$0x80"   : "=a" (_v) : "Nd" (port)   ); return _v; } 


extern inline void outb  (unsigned   char   value, unsigned short port) {  __asm__ __volatile__ ("out" "b" " %"   "b"   "0,%"  "w"  "1"  : : "a" (value), "Nd" (port)); } extern inline void outb_p (unsigned   char   value, unsigned short port) {  __asm__ __volatile__ ("out" "b" " %"   "b"   "0,%"  "w"  "1"  "\noutb %%al,$0x80"   : : "a" (value), "Nd" (port));} 
extern inline void outw  (unsigned   short   value, unsigned short port) {  __asm__ __volatile__ ("out" "w" " %"   "w"   "0,%"  "w"  "1"  : : "a" (value), "Nd" (port)); } extern inline void outw_p (unsigned   short   value, unsigned short port) {  __asm__ __volatile__ ("out" "w" " %"   "w"   "0,%"  "w"  "1"  "\noutb %%al,$0x80"   : : "a" (value), "Nd" (port));} 
extern inline void outl  (unsigned   int   value, unsigned short port) {  __asm__ __volatile__ ("out" "l" " %"      "0,%"  "w"  "1"  : : "a" (value), "Nd" (port)); } extern inline void outl_p (unsigned   int   value, unsigned short port) {  __asm__ __volatile__ ("out" "l" " %"      "0,%"  "w"  "1"  "\noutb %%al,$0x80"   : : "a" (value), "Nd" (port));} 

extern inline void insb (unsigned short port, void * addr, unsigned long count) { __asm__ __volatile__ ("cld ; rep ; ins" "b" : "=D" (addr), "=c" (count) : "d" (port),"0" (addr),"1" (count)); } 
extern inline void insw (unsigned short port, void * addr, unsigned long count) { __asm__ __volatile__ ("cld ; rep ; ins" "w" : "=D" (addr), "=c" (count) : "d" (port),"0" (addr),"1" (count)); } 
extern inline void insl (unsigned short port, void * addr, unsigned long count) { __asm__ __volatile__ ("cld ; rep ; ins" "l" : "=D" (addr), "=c" (count) : "d" (port),"0" (addr),"1" (count)); } 

extern inline void outsb (unsigned short port, const void * addr, unsigned long count) { __asm__ __volatile__ ("cld ; rep ; outs" "b" : "=S" (addr), "=c" (count) : "d" (port),"0" (addr),"1" (count)); } 
extern inline void outsw (unsigned short port, const void * addr, unsigned long count) { __asm__ __volatile__ ("cld ; rep ; outs" "w" : "=S" (addr), "=c" (count) : "d" (port),"0" (addr),"1" (count)); } 
extern inline void outsl (unsigned short port, const void * addr, unsigned long count) { __asm__ __volatile__ ("cld ; rep ; outs" "l" : "=S" (addr), "=c" (count) : "d" (port),"0" (addr),"1" (count)); } 



# 1 "/usr/src/linux/include/linux/vmalloc.h" 1






# 1 "/usr/src/linux/include/asm/pgtable.h" 1





 










# 1 "/usr/src/linux/include/asm/fixmap.h" 1
 
















 


















 





enum fixed_addresses {















	__end_of_fixed_addresses
};

extern void set_fixmap (enum fixed_addresses idx, unsigned long phys);

 












extern void __this_fixmap_does_not_exist(void);

 




extern inline unsigned long fix_to_virt(const unsigned int idx)
{
	 








	if (idx >= __end_of_fixed_addresses)
		__this_fixmap_does_not_exist();

        return ((0xffffe000UL)  - (( idx ) << 12 )) ;
}


# 17 "/usr/src/linux/include/asm/pgtable.h" 2



 








 





















 






static inline void flush_tlb_mm(struct mm_struct *mm)
{
	if (mm == get_current() ->mm)
		do { unsigned long tmpreg; __asm__ __volatile__("movl %%cr3,%0\n\tmovl %0,%%cr3":"=r" (tmpreg) : :"memory"); } while (0) ;
}

static inline void flush_tlb_page(struct vm_area_struct *vma,
	unsigned long addr)
{
	if (vma->vm_mm == get_current() ->mm)
		__asm__ __volatile__("invlpg %0": :"m" (*(char *)  addr )) ;
}

static inline void flush_tlb_range(struct mm_struct *mm,
	unsigned long start, unsigned long end)
{
	if (mm == get_current() ->mm)
		do { unsigned long tmpreg; __asm__ __volatile__("movl %%cr3,%0\n\tmovl %0,%%cr3":"=r" (tmpreg) : :"memory"); } while (0) ;
}

# 163 "/usr/src/linux/include/asm/pgtable.h"




 





 




 




 








 









 











 





























 





















 






 
extern unsigned long pg0[1024];
 
extern unsigned long empty_zero_page[1024];

 






extern pte_t __bad_page(void);
extern pte_t * __bad_pagetable(void);





 


 


 
 


 



 

















 




extern inline int pgd_none(pgd_t pgd)		{ return 0; }
extern inline int pgd_bad(pgd_t pgd)		{ return 0; }
extern inline int pgd_present(pgd_t pgd)	{ return 1; }
extern inline void pgd_clear(pgd_t * pgdp)	{ }

 



extern inline int pte_read(pte_t pte)		{ return (( pte ).pte)  & 0x004 ; }
extern inline int pte_exec(pte_t pte)		{ return (( pte ).pte)  & 0x004 ; }
extern inline int pte_dirty(pte_t pte)		{ return (( pte ).pte)  & 0x040 ; }
extern inline int pte_young(pte_t pte)		{ return (( pte ).pte)  & 0x020 ; }
extern inline int pte_write(pte_t pte)		{ return (( pte ).pte)  & 0x002 ; }

extern inline pte_t pte_rdprotect(pte_t pte)	{ (( pte ).pte)  &= ~0x004 ; return pte; }
extern inline pte_t pte_exprotect(pte_t pte)	{ (( pte ).pte)  &= ~0x004 ; return pte; }
extern inline pte_t pte_mkclean(pte_t pte)	{ (( pte ).pte)  &= ~0x040 ; return pte; }
extern inline pte_t pte_mkold(pte_t pte)	{ (( pte ).pte)  &= ~0x020 ; return pte; }
extern inline pte_t pte_wrprotect(pte_t pte)	{ (( pte ).pte)  &= ~0x002 ; return pte; }
extern inline pte_t pte_mkread(pte_t pte)	{ (( pte ).pte)  |= 0x004 ; return pte; }
extern inline pte_t pte_mkexec(pte_t pte)	{ (( pte ).pte)  |= 0x004 ; return pte; }
extern inline pte_t pte_mkdirty(pte_t pte)	{ (( pte ).pte)  |= 0x040 ; return pte; }
extern inline pte_t pte_mkyoung(pte_t pte)	{ (( pte ).pte)  |= 0x020 ; return pte; }
extern inline pte_t pte_mkwrite(pte_t pte)	{ (( pte ).pte)  |= 0x002 ; return pte; }

 






 



extern inline pte_t pte_modify(pte_t pte, pgprot_t newprot)
{ (( pte ).pte)  = ((( pte ).pte)  & ((~((1UL << 12 ) -1))  | 0x020  | 0x040 ) ) | (( newprot ).pgprot) ; return pte; }







 



 


 
extern inline pmd_t * pmd_offset(pgd_t * dir, unsigned long address)
{
	return (pmd_t *) dir;
}

  



 










extern __inline__ pgd_t *get_pgd_slow(void)
{
	pgd_t *ret = (pgd_t *)__get_free_pages(( (0x04  | 0x01  | 0x10 )  ),0) , *init;

	if (ret) {
		init = (( &init_mm )->pgd + ((  0 ) >> 22 )) ;
		(__builtin_constant_p(  0 ) ? (__builtin_constant_p( (  ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) )  * sizeof(pgd_t) ) ) ? __constant_c_and_count_memset(( ( ret ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) )  * sizeof(pgd_t) ) )) : __constant_c_memset(( ( ret ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) )  * sizeof(pgd_t) ) )))  : (__builtin_constant_p( (  ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) )  * sizeof(pgd_t) ) ) ? __memset_generic(( ( ( ret ) ) ),( ( (  0 ) ) ),( ( (  ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) )  * sizeof(pgd_t) ) ) ))  : __memset_generic(( ( ret ) ),( (  0 ) ),( (  ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) )  * sizeof(pgd_t) ) ))) ) ;
		(__builtin_constant_p( 
			(1024  - ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) ) ) * sizeof(pgd_t) ) ? __constant_memcpy(( ret + ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) )  ),(  init + ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) )  ),(  			(1024  - ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) ) ) * sizeof(pgd_t) )) : __memcpy(( ret + ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) )  ),(  init + ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) )  ),(  			(1024  - ((((unsigned long)(0xC0000000 ) ) ) / (1UL << 22 ) ) ) * sizeof(pgd_t) ))) ;
	}
	return ret;
}

extern __inline__ pgd_t *get_pgd_fast(void)
{
	unsigned long *ret;

	if((ret = (boot_cpu_data .pgd_quick) ) != ((void *)0) ) {
		(boot_cpu_data .pgd_quick)  = (unsigned long *)(*ret);
		ret[0] = ret[1];
		(boot_cpu_data .pgtable_cache_sz) --;
	} else
		ret = (unsigned long *)get_pgd_slow();
	return (pgd_t *)ret;
}

extern __inline__ void free_pgd_fast(pgd_t *pgd)
{
	*(unsigned long *)pgd = (unsigned long) (boot_cpu_data .pgd_quick) ;
	(boot_cpu_data .pgd_quick)  = (unsigned long *) pgd;
	(boot_cpu_data .pgtable_cache_sz) ++;
}

extern __inline__ void free_pgd_slow(pgd_t *pgd)
{
	free_pages(( (unsigned long)pgd ),0) ;
}

extern pte_t *get_pte_slow(pmd_t *pmd, unsigned long address_preadjusted);
extern pte_t *get_pte_kernel_slow(pmd_t *pmd, unsigned long address_preadjusted);

extern __inline__ pte_t *get_pte_fast(void)
{
	unsigned long *ret;

	if((ret = (unsigned long *)(boot_cpu_data .pte_quick) ) != ((void *)0) ) {
		(boot_cpu_data .pte_quick)  = (unsigned long *)(*ret);
		ret[0] = ret[1];
		(boot_cpu_data .pgtable_cache_sz) --;
	}
	return (pte_t *)ret;
}

extern __inline__ void free_pte_fast(pte_t *pte)
{
	*(unsigned long *)pte = (unsigned long) (boot_cpu_data .pte_quick) ;
	(boot_cpu_data .pte_quick)  = (unsigned long *) pte;
	(boot_cpu_data .pgtable_cache_sz) ++;
}

extern __inline__ void free_pte_slow(pte_t *pte)
{
	free_pages(( (unsigned long)pte ),0) ;
}

 
extern __inline__ pmd_t *get_pmd_fast(void)
{
	return (pmd_t *)0;
}

extern __inline__ void free_pmd_fast(pmd_t *pmd)
{
}

extern __inline__ void free_pmd_slow(pmd_t *pmd)
{
}

extern void __bad_pte(pmd_t *pmd);
extern void __bad_pte_kernel(pmd_t *pmd);






extern inline pte_t * pte_alloc_kernel(pmd_t * pmd, unsigned long address)
{
	address = (address >> 12 ) & (1024  - 1);
	if ((! ((  *pmd  ).pmd) ) ) {
		pte_t * page = (pte_t *) get_pte_fast();
		
		if (!page)
			return get_pte_kernel_slow(pmd, address);
		(( *pmd ).pmd)  = (0x001  | 0x002  | 0x020  | 0x040 )  + ((unsigned long)( page )- ((unsigned long)(0xC0000000 ) ) ) ;   // AMBIGUOUS
		return page + address;
	}
	if (((((  *pmd  ).pmd)  & (~(~((1UL << 12 ) -1))  & ~0x004 )) != (0x001  | 0x002  | 0x020  | 0x040 ) ) ) {
		__bad_pte_kernel(pmd);
		return ((void *)0) ;
	}
	return (pte_t *) ((unsigned long) ((void *)((unsigned long)( ((  *pmd  ).pmd)  & (~((1UL << 12 ) -1))  )+ ((unsigned long)(0xC0000000 ) ) )) )  + address;
}

extern inline pte_t * pte_alloc(pmd_t * pmd, unsigned long address)
{
	address = (address >> (12 -2)) & 4*(1024  - 1);

	if ((! ((  *pmd  ).pmd) ) )
		goto getnew;
	if (((((  *pmd  ).pmd)  & (~(~((1UL << 12 ) -1))  & ~0x004 )) != (0x001  | 0x002  | 0x020  | 0x040 ) ) )
		goto fix;
	return (pte_t *) (((unsigned long) ((void *)((unsigned long)( ((  *pmd  ).pmd)  & (~((1UL << 12 ) -1))  )+ ((unsigned long)(0xC0000000 ) ) )) )  + address);
getnew:
{
	unsigned long page = (unsigned long) get_pte_fast();

	if (!page)
		return get_pte_slow(pmd, address);
	(( *pmd ).pmd)  = (0x001  | 0x002  | 0x004  | 0x020  | 0x040 )  + ((unsigned long)( page )- ((unsigned long)(0xC0000000 ) ) ) ;    // AMBIGUOUS
	return (pte_t *) (page + address);
}
fix:
	__bad_pte(pmd);
	return ((void *)0) ;
}





extern inline void pmd_free(pmd_t * pmd)
{
}

extern inline pmd_t * pmd_alloc(pgd_t * pgd, unsigned long address)
{
	return (pmd_t *) pgd;
}




extern int do_check_pgt_cache(int, int);

extern inline void set_pgdir(unsigned long address, pgd_t entry)
{
	struct task_struct * p;
	pgd_t *pgd;




	(void)( &tasklist_lock ) ;
	for ( p  = & (init_task_union.task)  ; ( p  =  p ->next_task) != & (init_task_union.task)  ; )  {
		if (!p->mm)
			continue;
		* (( p->mm )->pgd + (( address ) >> 22 ))  = entry;
	}
	do { } while(0) ;

	for (pgd = (pgd_t *)(boot_cpu_data .pgd_quick) ; pgd; pgd = (pgd_t *)*(unsigned long *)pgd)
		pgd[address >> 22 ] = entry;







}

extern pgd_t swapper_pg_dir[1024];

 



extern inline void update_mmu_cache(struct vm_area_struct * vma,
	unsigned long address, pte_t pte)
{
}










 




# 7 "/usr/src/linux/include/linux/vmalloc.h" 2


struct vm_struct {
	unsigned long flags;
	void * addr;
	unsigned long size;
	struct vm_struct * next;
};

struct vm_struct * get_vm_area(unsigned long size);
void vfree(void * addr);
void * vmalloc(unsigned long size);
long vread(char *buf, char *addr, unsigned long count);
void vmfree_area_pages(unsigned long address, unsigned long size);
int vmalloc_area_pages(unsigned long address, unsigned long size);



# 101 "/usr/src/linux/include/asm/io.h" 2





 



extern inline unsigned long virt_to_phys(volatile void * address)
{
	return ((unsigned long)( address ) & ~((unsigned long)(0xC0000000 ) ) ) ;   // AMBIGUOUS
}

extern inline void * phys_to_virt(unsigned long address)
{
	return ((void *)(((unsigned long)(0xC0000000 ) )  | (unsigned long)( address ))) ;
}

extern void * __ioremap(unsigned long offset, unsigned long size, unsigned long flags);

extern inline void * ioremap (unsigned long offset, unsigned long size)
{
	return __ioremap(offset, size, 0);
}

 




extern inline void * ioremap_nocache (unsigned long offset, unsigned long size)
{
        return __ioremap(offset, size, 0x010 );
}

extern void iounmap(void *addr);

 





 


















 





static inline int check_signature(unsigned long io_addr,
	const unsigned char *signature, int length)
{
	int retval = 0;
	do {
		if ((*(volatile unsigned char *) ((void *)(((unsigned long)(0xC0000000 ) )  | (unsigned long)(  io_addr  ))) )  != *signature)
			goto out;
		io_addr++;
		signature++;
		length--;
	} while (length);
	retval = 1;
out:
	return retval;
}




# 18 "/usr/src/linux/include/asm/keyboard.h" 2





extern int pckbd_setkeycode(unsigned int scancode, unsigned int keycode);
extern int pckbd_getkeycode(unsigned int scancode);
extern int pckbd_translate(unsigned char scancode, unsigned char *keycode,
			   char raw_mode);
extern char pckbd_unexpected_up(unsigned char keycode);
extern void pckbd_leds(unsigned char leds);
extern void pckbd_init_hw(void);
extern unsigned char pckbd_sysrq_xlate[128];











 




 





 


 












# 34 "pc_keyb.c" 2



# 1 "/usr/src/linux/include/asm/irq.h" 1



 










 










static __inline__ int irq_cannonicalize(int irq)
{
	return ((irq == 2) ? 9 : irq);
}

extern void disable_irq(unsigned int);
extern void disable_irq_nosync(unsigned int);
extern void enable_irq(unsigned int);


# 37 "pc_keyb.c" 2



 

# 1 "/usr/src/linux/include/linux/pc_keyb.h" 1
 







 















 



extern unsigned char pckbd_read_mask;
extern unsigned char aux_device_present;

 







 

















 









 







 














 












 



















struct aux_queue {
	unsigned long head;
	unsigned long tail;
	struct wait_queue *proc_list;
	struct fasync_struct *fasync;
	unsigned char buf[2048 ];
};
# 42 "pc_keyb.c" 2


 

# 55 "pc_keyb.c"


static void kbd_write_command_w(int data);
static void kbd_write_output_w(int data);

static void aux_write_ack(int val);


//spinlock_t kbd_controller_lock = (spinlock_t) { } ;   // INVALID
static unsigned char handle_kbd_event(void);

 
static volatile unsigned char reply_expected = 0;
static volatile unsigned char acknowledge = 0;
static volatile unsigned char resend = 0;



 



static int __attribute__ ((__section__ (".text.init")))  psaux_init(void);


 

static struct aux_queue *queue;	 
static int aux_count = 0;
 
static unsigned char mouse_reply_expected = 0;







 












static void kb_wait(void)
{
	unsigned long timeout = 250 ;

	do {
		 



		unsigned char status = handle_kbd_event();

		if (! (status & 0x02 ))
			return;
		(	(__builtin_constant_p( 1 ) && ( 1 )<= 5 ) ? (__builtin_constant_p( ( 1 )*1000 ) ? __const_udelay(( ( 1 )*1000 ) * 0x10c6ul) : __udelay( ( 1 )*1000 ))  : ({unsigned long msec=( 1 ); while (msec--) (__builtin_constant_p( 1000 ) ? __const_udelay(( 1000 ) * 0x10c6ul) : __udelay( 1000 )) ;})) ;
		timeout--;
	} while (timeout);

	printk("<4>"  "Keyboard timed out[1]\n");

}

 




























 






















 










static unsigned char high_keys[128 - 89 ] = {
  124 , 125 , 126 , 127 , 0, 0, 0,                    
  0, 0, 0, 0, 0, 0, 0, 0,                             
  0, 0, 0, 0, 0, 122 , 0, 123 ,           
  0, 0, 0, 89 , 120 , 0, 0, 90 ,     
  91 , 92 , 93 , 94 ,         
  95 , 124 , 121 , 0                    
};

 

 






 




 









static unsigned char e0_keys[128] = {
  0, 0, 0, 0, 0, 0, 0, 0,			       
  0, 0, 0, 0, 0, 0, 0, 0,			       
  0, 0, 0, 0, 0, 0, 0, 0,			       
  0, 0, 0, 0, 96 , 97 , 0, 0,	       
  0, 0, 0, 0, 0, 0, 0, 0,			       
  0, 0, 0, 0, 0, 0, 0, 0,			       
  0, 0, 0, 0, 0, 98 , 0, 99 ,	       
  100 , 0, 0, 0, 0, 113 , 114 , 115 ,	       
  116 , 117 , 0, 0, 0, 0, 101 , 102 ,	       
  103 , 104 , 0, 105 , 124 , 106 , 118 , 107 , 
  108 , 109 , 110 , 111 , 0, 0, 0, 0,	       
  0, 0, 0, 125 , 126 , 127 , 0, 0,	       
  0, 0, 0, 0, 0, 0, 0, 0,			       
  0, 0, 0, 0, 0, 0, 0, 112 ,		       
  0, 0, 0, 0, 0, 0, 0, 0,			       
  0, 0, 0, 0, 0, 0, 0, 0			       
};

int pckbd_setkeycode(unsigned int scancode, unsigned int keycode)
{
	if (scancode < 89  || scancode > 255 || keycode > 127)
	  return - 22 ;
	if (scancode < 128)
	  high_keys[scancode - 89 ] = keycode;
	else
	  e0_keys[scancode - 128] = keycode;
	return 0;
}

int pckbd_getkeycode(unsigned int scancode)
{
	return
	  (scancode < 89  || scancode > 255) ? - 22  :
	  (scancode < 128) ? high_keys[scancode - 89 ] :
	    e0_keys[scancode - 128];
}

static int do_acknowledge(unsigned char scancode)
{
	if (reply_expected) {
	   




		if (scancode == 0xFA ) {
			acknowledge = 1;
			reply_expected = 0;
			return 0;
		} else if (scancode == 0xFE ) {
			resend = 1;
			reply_expected = 0;
			return 0;
		}
		 




	}
	return 1;
}

int pckbd_translate(unsigned char scancode, unsigned char *keycode,
		    char raw_mode)
{
	static int prev_scancode = 0;

	 
	if (scancode == 0xe0 || scancode == 0xe1) {
		prev_scancode = scancode;
		return 0;
	}

	 
	if (scancode == 0x00 || scancode == 0xff) {
		prev_scancode = 0;
		return 0;
	}

	scancode &= 0x7f;

	if (prev_scancode) {
	   



	  if (prev_scancode != 0xe0) {
	      if (prev_scancode == 0xe1 && scancode == 0x1d) {
		  prev_scancode = 0x100;
		  return 0;
	      } else if (prev_scancode == 0x100 && scancode == 0x45) {
		  *keycode = 119 ;
		  prev_scancode = 0;
	      } else {

		  if (!raw_mode)
		    printk("<6>"  "keyboard: unknown e1 escape sequence\n");

		  prev_scancode = 0;
		  return 0;
	      }
	  } else {
	      prev_scancode = 0;
	       






	       





	      if (scancode == 0x2a || scancode == 0x36)
		return 0;

	      if (e0_keys[scancode])
		*keycode = e0_keys[scancode];
	      else {

		  if (!raw_mode)
		    printk("<6>"  "keyboard: unknown scancode e0 %02x\n",
			   scancode);

		  return 0;
	      }
	  }
	} else if (scancode >= 89 ) {
	     




	     

	     


	  *keycode = high_keys[scancode - 89 ];

	  if (!*keycode) {
	      if (!raw_mode) {

		  printk("<6>"  "keyboard: unrecognized scancode (%02x)"
			 " - ignored\n", scancode);

	      }
	      return 0;
	  }
 	} else
	  *keycode = scancode;
 	return 1;
}

char pckbd_unexpected_up(unsigned char keycode)
{
	 

	if (keycode >= 89  || keycode == 85)
	    return 0;
	else
	    return 0200;
}

static inline void handle_mouse_event(unsigned char scancode)
{

	if (mouse_reply_expected) {
		if (scancode == 0xFA ) {
			mouse_reply_expected--;
			return;
		}
		mouse_reply_expected = 0;
	}
    else if(scancode == 170 ){
        queue->head = queue->tail = 0;   
         
	kb_wait();
	outb( 0xD4  , 0x64 ) ;
	kb_wait();
	outb( 0xF4  , 0x60 ) ;
	 
	mouse_reply_expected++;
	kb_wait();
        return;
    }

	add_mouse_randomness(scancode);
	if (aux_count) {
		int head = queue->head;

		queue->buf[head] = scancode;
		head = (head + 1) & (2048 -1);
		if (head != queue->tail) {
			queue->head = head;
			if (queue->fasync)
				kill_fasync(queue->fasync, 29 );
			__wake_up(( &queue->proc_list ),1 ) ;
		}
	}

}

 






static unsigned char handle_kbd_event(void)
{
	unsigned char status = inb(0x64 ) ;
	unsigned int work = 10000;

	while (status & 0x01 ) {
		unsigned char scancode;

		scancode = inb(0x60 ) ;



		if (status & 0x20 ) {
			handle_mouse_event(scancode);
		} else {
			if (do_acknowledge(scancode))
				handle_scancode(scancode, !(scancode & 0x80));
			mark_bh(KEYBOARD_BH);
		}

		status = inb(0x64 ) ;
		
		if(!work--)
		{
			printk("<3>"  "pc_keyb: controller jammed (0x%02X).\n",
				status);
			break;
		}
	}

	return status;
}


static void keyboard_interrupt(int irq, void *dev_id, struct pt_regs *regs)
{
	unsigned long flags;

	kbd_pt_regs = regs;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	handle_kbd_event();
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
}

 






static int send_data(unsigned char data)
{
	int retries = 3;

	do {
		unsigned long timeout = 1000 ;

		acknowledge = 0;  
		resend = 0;
		reply_expected = 1;
		kbd_write_output_w(data);
		for (;;) {
			if (acknowledge)
				return 1;
			if (resend)
				break;
			(	(__builtin_constant_p( 1 ) && ( 1 )<= 5 ) ? (__builtin_constant_p( ( 1 )*1000 ) ? __const_udelay(( ( 1 )*1000 ) * 0x10c6ul) : __udelay( ( 1 )*1000 ))  : ({unsigned long msec=( 1 ); while (msec--) (__builtin_constant_p( 1000 ) ? __const_udelay(( 1000 ) * 0x10c6ul) : __udelay( 1000 )) ;})) ;
			if (!--timeout) {

				printk("<4>"  "Keyboard timeout[2]\n");

				return 0;
			}
		}
	} while (retries-- > 0);

	printk("<4>"  "keyboard: Too many NACKs -- noisy kbd cable?\n");

	return 0;
}

void pckbd_leds(unsigned char leds)
{
	if (!send_data(0xED ) || !send_data(leds))
	    send_data(0xF4 );	 
}

 









 int kbd_startup_reset __attribute__ ((__section__ (".data.init")))  = 0;




 
void __attribute__ ((__section__ (".text.init")))  kbd_reset_setup(char *str, int *ints)
{
	kbd_startup_reset = 1;
}




static int __attribute__ ((__section__ (".text.init")))  kbd_read_data(void)
{
	int retval = (-1) ;
	unsigned char status;

	status = inb(0x64 ) ;
	if (status & 0x01 ) {
		unsigned char data = inb(0x60 ) ;

		retval = data;
		if (status & (0x40  | 0x80 ))
			retval = (-2) ;
	}
	return retval;
}

static void __attribute__ ((__section__ (".text.init")))  kbd_clear_input(void)
{
	int maxread = 100;	 

	do {
		if (kbd_read_data() == (-1) )
			break;
	} while (--maxread);
}

static int __attribute__ ((__section__ (".text.init")))  kbd_wait_for_input(void)
{
	long timeout = 1000 ;

	do {
		int retval = kbd_read_data();
		if (retval >= 0)
			return retval;
		(	(__builtin_constant_p( 1 ) && ( 1 )<= 5 ) ? (__builtin_constant_p( ( 1 )*1000 ) ? __const_udelay(( ( 1 )*1000 ) * 0x10c6ul) : __udelay( ( 1 )*1000 ))  : ({unsigned long msec=( 1 ); while (msec--) (__builtin_constant_p( 1000 ) ? __const_udelay(( 1000 ) * 0x10c6ul) : __udelay( 1000 )) ;})) ;
	} while (--timeout);
	return -1;
}

static void kbd_write_command_w(int data)
{
	unsigned long flags;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	kb_wait();
	outb( data , 0x64 ) ;
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
}

static void kbd_write_output_w(int data)
{
	unsigned long flags;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	kb_wait();
	outb( data , 0x60 ) ;
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
}


static void kbd_write_cmd(int cmd)
{
	unsigned long flags;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	kb_wait();
	outb( 0x60  , 0x64 ) ;
	kb_wait();
	outb( cmd , 0x60 ) ;
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
}


static char * __attribute__ ((__section__ (".text.init")))  initialize_kbd(void)
{
	int status;

	 




	kbd_write_command_w(0xAA );
	if (kbd_wait_for_input() != 0x55)
		return "Keyboard failed self test";

	 




	kbd_write_command_w(0xAB );
	if (kbd_wait_for_input() != 0x00)
		return "Keyboard interface failed self test";

	 


	kbd_write_command_w(0xAE );

	 







	do {
		kbd_write_output_w(0xFF );
		status = kbd_wait_for_input();
		if (status == 0xFA )
			break;
		if (status != 0xFE )
			return "Keyboard reset failed, no ACK";
	} while (1);

	if (kbd_wait_for_input() != 0xAA )
		return "Keyboard reset failed, no POR";

	 





	do {
		kbd_write_output_w(0xF5 );
		status = kbd_wait_for_input();
		if (status == 0xFA )
			break;
		if (status != 0xFE )
			return "Disable keyboard: no ACK";
	} while (1);

	kbd_write_command_w(0x60 );
	kbd_write_output_w(0x01 
			      | 0x04 
			      | 0x20 
			      | 0x40 );

	 
	kbd_write_command_w(0x20 );
	if (!(kbd_wait_for_input() & 0x40 )) {
		 



		kbd_write_output_w(0xF0);
		kbd_wait_for_input();
		kbd_write_output_w(0x01);
		kbd_wait_for_input();
	}

	
	kbd_write_output_w(0xF4 );
	if (kbd_wait_for_input() != 0xFA )
		return "Enable keyboard: no ACK";

	 


	kbd_write_output_w(0xF3 );
	if (kbd_wait_for_input() != 0xFA )
		return "Set rate: no ACK";
	kbd_write_output_w(0x00);
	if (kbd_wait_for_input() != 0xFA )
		return "Set rate: no ACK";

	return ((void *)0) ;
}

void __attribute__ ((__section__ (".text.init")))  pckbd_init_hw(void)
{
	request_region(0x60, 16, "keyboard") ;

	 
	kbd_clear_input();

	if (kbd_startup_reset) {
		char *msg = initialize_kbd();
		if (msg)
			printk("<4>"  "initialize_kbd: %s\n", msg);
	}


	psaux_init();


	 
	request_irq(1 ,  keyboard_interrupt , 0, "keyboard", ((void *)0) ) ;
}



 


static int __attribute__ ((__section__ (".text.init")))  detect_auxiliary_port(void)
{
	unsigned long flags;
	int loops = 10;
	int retval = 0;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;

	 






	kb_wait();
	outb( 0xD3  , 0x64 ) ;

	kb_wait();
	outb( 0x5a , 0x60 ) ;  

	do {
		unsigned char status = inb(0x64 ) ;

		if (status & 0x01 ) {
			(void) inb(0x60 ) ;
			if (status & 0x20 ) {
				printk("<6>"  "Detected PS/2 Mouse Port.\n");
				retval = 1;
			}
			break;
		}
		(	(__builtin_constant_p( 1 ) && ( 1 )<= 5 ) ? (__builtin_constant_p( ( 1 )*1000 ) ? __const_udelay(( ( 1 )*1000 ) * 0x10c6ul) : __udelay( ( 1 )*1000 ))  : ({unsigned long msec=( 1 ); while (msec--) (__builtin_constant_p( 1000 ) ? __const_udelay(( 1000 ) * 0x10c6ul) : __udelay( 1000 )) ;})) ;
	} while (--loops);
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;

	return retval;
}

 


static void aux_write_dev(int val)
{
	unsigned long flags;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	kb_wait();
	outb( 0xD4  , 0x64 ) ;
	kb_wait();
	outb( val , 0x60 ) ;
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
}

 


static void aux_write_ack(int val)
{
	unsigned long flags;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	kb_wait();
	outb( 0xD4  , 0x64 ) ;
	kb_wait();
	outb( val , 0x60 ) ;
	 
	mouse_reply_expected++;
	kb_wait();
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
}

static unsigned char get_from_queue(void)
{
	unsigned char result;
	unsigned long flags;

	do { __asm__ __volatile__("pushfl ; popl %0":"=g" (    flags   ):   :"memory")  ; __asm__ __volatile__ ("cli": : :"memory")  ; } while (0) ;
	result = queue->buf[queue->tail];
	queue->tail = (queue->tail + 1) & (2048 -1);
	__asm__ __volatile__("pushl %0 ; popfl":   :"g" (    flags   ):"memory")   ;
	return result;
}


static inline int queue_empty(void)
{
	return queue->head == queue->tail;
}

static int fasync_aux(int fd, struct file *filp, int on)
{
	int retval;

	retval = fasync_helper(fd, filp, on, &queue->fasync);
	if (retval < 0)
		return retval;
	return 0;
}


 




static int release_aux(struct inode * inode, struct file * file)
{
	fasync_aux(-1, file, 0);
	if (--aux_count)
		return 0;
	kbd_write_cmd((0x40  | 0x20  | 0x04  | 0x01 ) );			     
	kbd_write_command_w(0xA7 );
	free_irq(12 ,  ((void *)queue)  ) ;
	return 0;
}

 




static int open_aux(struct inode * inode, struct file * file)
{
	if (aux_count++) {
		return 0;
	}
	queue->head = queue->tail = 0;		 
	if (request_irq(12 ,  keyboard_interrupt , 0x04000000 , "PS/2 Mouse",   ((void *)queue)  ) ) {
		aux_count--;
		return - 16 ;
	}
	kbd_write_command_w(0xA8 );	 


	aux_write_ack(0xF4 );  
	kbd_write_cmd((0x40  | 0x04  | 0x02  | 0x01 ) );  

	return 0;
}

 



static ssize_t read_aux(struct file * file, char * buffer,
			size_t count, loff_t *ppos)
{
	struct wait_queue wait = { get_current() , ((void *)0)  };
	ssize_t i = count;
	unsigned char c;

	if (queue_empty()) {
		if (file->f_flags & 04000 )
			return - 11 ;
		add_wait_queue(&queue->proc_list, &wait);
repeat:
		get_current() ->state = 1 ;
		if (queue_empty() && !signal_pending(get_current() )) {
			schedule();
			goto repeat;
		}
		get_current() ->state = 0 ;
		remove_wait_queue(&queue->proc_list, &wait);
	}
	while (i > 0 && !queue_empty()) {
		c = get_from_queue();
		({	int __ret_pu;	switch(sizeof (*(  buffer++ ))) {	case 1:  __asm__ __volatile__("call __put_user_" "1"	:"=a" ( __ret_pu )	:"0" (   buffer++  ),"d" ( (__typeof__(*(  buffer++ )))( c ) )	:"cx") ; break;	case 2:  __asm__ __volatile__("call __put_user_" "2"	:"=a" ( __ret_pu )	:"0" (   buffer++  ),"d" ( (__typeof__(*(  buffer++ )))( c ) )	:"cx") ; break;	case 4:  __asm__ __volatile__("call __put_user_" "4"	:"=a" ( __ret_pu )	:"0" (   buffer++  ),"d" ( (__typeof__(*(  buffer++ )))( c ) )	:"cx") ; break;	default: __asm__ __volatile__("call __put_user_" "X"	:"=a" ( __ret_pu )	:"0" (   buffer++  ),"d" (  c  )	:"cx") ; break;	}	__ret_pu;	}) ;
		i--;
	}
	if (count-i) {
		file->f_dentry->d_inode->i_atime = (xtime.tv_sec) ;
		return count-i;
	}
	if (signal_pending(get_current() ))
		return - 512 ;
	return 0;
}

 



static ssize_t write_aux(struct file * file, const char * buffer,
			 size_t count, loff_t *ppos)
{
	ssize_t retval = 0;

	if (count) {
		ssize_t written = 0;

		if (count > 32)
			count = 32;  
		do {
			char c;
//			({	int __ret_gu,__val_gu;	switch(sizeof (*(  buffer++ ))) {	case 1:  __asm__ __volatile__("call __get_user_" "1" :"=a" ( __ret_gu ),"=d" ( __val_gu ) :"0" (   buffer++  )) ; break;	case 2:  __asm__ __volatile__("call __get_user_" "2" :"=a" ( __ret_gu ),"=d" ( __val_gu ) :"0" (   buffer++  )) ; break;	case 4:  __asm__ __volatile__("call __get_user_" "4" :"=a" ( __ret_gu ),"=d" ( __val_gu ) :"0" (   buffer++  )) ; break;	default: __asm__ __volatile__("call __get_user_" "X" :"=a" ( __ret_gu ),"=d" ( __val_gu ) :"0" (   buffer++  )) ; break;	}	( c ) = (__typeof__(*(  buffer++ )))__val_gu;	__ret_gu;	}) ;    // TYPEOF
			aux_write_dev(c);
			written++;
		} while (--count);
		retval = - 5 ;
		if (written) {
			retval = written;
			file->f_dentry->d_inode->i_mtime = (xtime.tv_sec) ;
		}
	}

	return retval;
}

static unsigned int aux_poll(struct file *file, poll_table * wait)
{
	poll_wait(file, &queue->proc_list, wait);
	if (!queue_empty())
		return 0x0001  | 0x0040 ;
	return 0;
}

struct file_operations psaux_fops = {
	((void *)0) ,		 
	read_aux,
	write_aux,
	((void *)0) , 		 
	aux_poll,
	((void *)0) , 		 
	((void *)0) ,		 
	open_aux,
	((void *)0) ,		 
	release_aux,
	((void *)0) ,
	fasync_aux,
};

 


static struct miscdevice psaux_mouse = {
	1 , "psaux", &psaux_fops
};

static int __attribute__ ((__section__ (".text.init")))  psaux_init(void)
{
	if (!detect_auxiliary_port())
		return - 5 ;

	misc_register(&psaux_mouse);
	queue = (struct aux_queue *) kmalloc(sizeof(*queue), (0x04  | 0x01  | 0x10 ) );
	(__builtin_constant_p(  0 ) ? (__builtin_constant_p( (  sizeof(*queue) ) ) ? __constant_c_and_count_memset(( ( queue ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  sizeof(*queue) ) )) : __constant_c_memset(( ( queue ) ),( (0x01010101UL*(unsigned char)(  0 )) ),( (  sizeof(*queue) ) )))  : (__builtin_constant_p( (  sizeof(*queue) ) ) ? __memset_generic(( ( ( queue ) ) ),( ( (  0 ) ) ),( ( (  sizeof(*queue) ) ) ))  : __memset_generic(( ( queue ) ),( (  0 ) ),( (  sizeof(*queue) ) ))) ) ;
	queue->head = queue->tail = 0;
	queue->proc_list = ((void *)0) ;









	outb( 0xA7  , 0x64 ) ;  
	kbd_write_cmd((0x40  | 0x20  | 0x04  | 0x01 ) );  

	return 0;
}


