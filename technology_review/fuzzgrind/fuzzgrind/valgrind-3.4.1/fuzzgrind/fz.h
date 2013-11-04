/*  This file is part of Fuzzgrind.
 *  Copyright (C) 2009 Gabriel Campana
 *
 *  This work is licensed under the terms of the GNU GPL, version 3.
 *  See the LICENSE file in the top-level directory.
 */


#define FZ_(str)    VGAPPEND(vgFuzzGrind_, str)

extern Char*         FZ_(clo_file_filter);
extern Bool          FZ_(clo_taint_file);
extern Bool          FZ_(verbose);
extern Bool          FZ_(clo_taint_stdin);

typedef UInt Tmp;
typedef UInt Reg;
//typedef HWord Addr;

/*
 * Structures which represent the dependency to the input
 * For example, the first byte of a little endian temporary value may depend of
 * the 6th byte of the input
 */
 
#define INVALID_TMP       -1
#define INVALID_ADDR      -1
//#define IS_INVALID(i, n)  (i & (1 << n))
//#define SET_INVALID(i, n) do { i |= (1 << n); } while (0)
#define XXX_POS_MAX       100
#define MAX_DEP           4096 * 2
#define XXX_MAX_BUF       1024
typedef struct s_dependency {
    union {
        //Tmp tmp;
        //Reg reg;
        Addr addr;
    } value;
    unsigned int size;      /* dependency size, in bits */
    char *cons;             /* pointing to buf while cons_size <= XXX_MAX_BUF */
    char buf[XXX_MAX_BUF];
    unsigned int cons_size;
} Dep;

extern Dep deptmp[MAX_DEP];
extern Dep depreg[MAX_DEP];
extern Dep depaddr8[MAX_DEP];
extern Dep depaddr16[MAX_DEP];
extern Dep depaddr32[MAX_DEP];
extern UInt depaddr8_number;
extern UInt depaddr16_number;
extern UInt depaddr32_number;

#define SELECT_DEPADDR(size) \
    (size == 32) ? depaddr32 : ((size == 8) ? depaddr8 : depaddr16)
#define SELECT_DEPADDR_NUMBER(size) \
    (size == 32) ? &depaddr32_number : ((size == 8) ? &depaddr8_number : &depaddr16_number)


#define TO_STR(x) #x

#define add_dirty2(fun, a, b) do {                               \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_2((a), (b))               \
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)

#define add_dirty3(fun, a, b, c) do {                            \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_3((a), (b), (c))          \
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)

#define add_dirty4(fun, a, b, c, d) do {                         \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_4((a), (b), (c), (d))     \
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)

#define add_dirty5(fun, a, b, c, d, e) do {                      \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_5((a), (b), (c), (d), (e))\
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)

#define add_dirty6(fun, a, b, c, d, e, f) do {                   \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_6((a), (b), (c), (d), (e), (f))\
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)

#define add_dirty7(fun, a, b, c, d, e, f, g) do {                   \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_7((a), (b), (c), (d), (e), (f), (g))\
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)


/* prototypes */
extern UInt add_dependency_addr(Addr, UInt);
extern void del_dependency_addr(Addr, UInt);

extern void FZ_(setup_tainted_map)(void);

extern void FZ_(syscall_open)(ThreadId tid, SysRes res);
extern void FZ_(syscall_read)(ThreadId tid, SysRes res);
extern void FZ_(syscall_mmap2)(ThreadId tid, SysRes res);
extern void FZ_(syscall_munmap)(ThreadId tid, SysRes res);
extern void FZ_(syscall_close)(ThreadId tid, SysRes res);
extern void FZ_(syscall_lseek)(ThreadId tid, SysRes res);

extern void IROp_to_str(IROp op, Char *buffer);

extern IRSB* fz_instrument(VgCallbackClosure*, IRSB*, VexGuestLayout*, 
                           VexGuestExtents*, IRType, IRType);
