// stdarg.h
// variable-argument function support macros

#ifndef __STDARG_H
#define __STDARG_H

typedef void *va_list;

// sm: this is for compatibility with glibc, which seems to assume
// it is using gcc's names
typedef va_list __gnuc_va_list;

void __va_start(va_list, ...);
#define va_start(__AP, __ARG) __va_start(__AP, __ARG)

void *__va_arg(va_list, int);
#define va_arg(__AP, __TYPE) *((__TYPE*)__va_arg((__AP), sizeof (__TYPE)))

void va_end(va_list);

#endif /* __STDARG_H */
