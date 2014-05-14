AC_INIT(stp, 0.1)
AM_INIT_AUTOMAKE
AC_PROG_CXX
AC_PROG_RANLIB
AC_CONFIG_MACRO_DIR([m4])
AC_CHECK_PROG(PERL, perl, perl)
AC_CHECK_PROGS(YACC,yacc bison byacc,[no],[path = $PATH])
[if test "$YACC" = "no"]
[then]
    [echo "You will need to install yacc to build STP"]
    [exit 1]
[fi]
AC_PROG_YACC
AC_CHECK_PROGS(LEX,lex flex ,[no],[path = $PATH])
[if test "$LEX" = "no"]
[then]
    [echo "You will need to install lex to build STP"]
    [exit 1]
[fi]
AC_PROG_LEX
AC_LANG(C++)
AC_CHECK_HEADERS([ext/hash_map ext/hash_set hash_map hash_set])
AC_CONFIG_HEADER(config.h)
AC_CONFIG_FILES([Makefile AST/Makefile sat/Makefile sat/core/Makefile
                 sat/mtl/Makefile simplifier/Makefile bitvec/Makefile
                 c_interface/Makefile constantbv/Makefile parser/Makefile])
#----------------------------------------------------------------------------
# Check is bionic
#----------------------------------------------------------------------------
# This variable will collect the suppression files to be used.
AC_SUBST(DEFAULT_SUPP)

AC_CHECK_HEADER([features.h])

# not really a version check
AC_EGREP_CPP([BIONIC_LIBC], [
#if defined(__ANDROID__)
  BIONIC_LIBC
#endif
],
GLIBC_VERSION="bionic")

AM_CONDITIONAL(BIONIC, test "$GLIBC_VERSION" = bionic)

case "${GLIBC_VERSION}" in
     bionic)
	AC_DEFINE([BIONIC_LIBC], 1, [Define to 1 if you're using Bionic])
	;;
	
esac

AC_SUBST(GLIBC_VERSION)

AC_OUTPUT
