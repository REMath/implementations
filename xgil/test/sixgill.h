
#ifndef SIXGILL_H
#define SIXGILL_H 

/******************************************************************************
 * Macros for static assertion annotations. These are used by the sixgill tool;
 * see sixgill.org for descriptions of these macros.
 * When the tool is not running these macros are no-ops.
 *****************************************************************************/

#ifdef XGILL_PLUGIN

#define precondition(COND)         __attribute__((precondition(#COND)))
#define precondition_assume(COND)  __attribute__((precondition_assume(#COND)))
#define postcondition(COND)        __attribute__((postcondition(#COND)))
#define postcondition_assume(COND) __attribute__((postcondition_assume(#COND)))
#define invariant(COND)            __attribute__((invariant(#COND)))
#define invariant_assume(COND)     __attribute__((invariant_assume(#COND)))

/* Used to make identifiers for assert/assume annotations in a function. */
#define static_paste2(X,Y) X ## Y
#define static_paste1(X,Y) static_paste2(X,Y)

#define assert_static(COND)                          \
  do {                                               \
    __attribute__((assert_static(#COND), unused))    \
    int static_paste1(assert_static_, __COUNTER__);  \
  } while (0)

#define assume_static(COND)                          \
  do {                                               \
    __attribute__((assume_static(#COND), unused))    \
    int static_paste1(assume_static_, __COUNTER__);  \
  } while (0)

#define assert_static_runtime(COND)                         \
  do {                                                      \
    __attribute__((assert_static_runtime(#COND), unused))   \
    int static_paste1(assert_static_runtime_, __COUNTER__); \
  } while (0)

#else /* XGILL_PLUGIN */

#define precondition(COND)          /* nothing */
#define precondition_assume(COND)   /* nothing */
#define postcondition(COND)         /* nothing */
#define postcondition_assume(COND)  /* nothing */
#define invariant(COND)             /* nothing */
#define invariant_assume(COND)      /* nothing */

#define assert_static(COND)          do { /* nothing */ } while (0)
#define assume_static(COND)          do { /* nothing */ } while (0)
#define assert_static_runtime(COND)  do { /* nothing */ } while (0)

#endif /* XGILL_PLUGIN */

#endif /* SIXGILL_H */
