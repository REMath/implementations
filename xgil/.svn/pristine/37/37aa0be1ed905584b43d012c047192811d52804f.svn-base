AC_PREREQ(2.57)
AC_INIT(sixgill, 0.91, [sg-discuss@sixgill.org])
AC_CONFIG_HEADER([config.h])

AC_PROG_CC
AC_PROG_CXX

AC_CANONICAL_HOST

case "$host_os" in
  darwin*)
    CPPFLAGS="$CPPFLAGS -I/opt/local/include";
    HOST_CFLAGS="-I/opt/local/include -DHOST_DARWIN";
    HOST_LDFLAGS="-L/opt/local/lib";
    ;;
    
  cygwin*)
    HOST_CFLAGS="-DHOST_CYGWIN";
    ;;
esac

AC_SUBST(HOST_CFLAGS)
AC_SUBST(HOST_LDFLAGS)

dnl *** check for gmp/zlib ***
AC_CHECK_HEADERS( gmp.h, [], [AC_MSG_ERROR(GMP must be installed)] )
AC_CHECK_HEADERS( zlib.h, [], [AC_MSG_ERROR(Zlib must be installed)] )
AC_LANG(C++)

dnl *** debug build
AC_ARG_ENABLE([debug],
              [AS_HELP_STRING([--enable-debug],
                [Build debugging binaries])],
              [DEBUG=1])
AC_SUBST(DEBUG)

dnl ***********************
dnl CVC3 support
dnl ***********************
AC_CHECK_HEADERS( cvc3/vc.h )
LIBS_SAVED=$LIBS
LIBS="$LIBS -lcvc3 -lgmp"
AC_LINK_IFELSE(
    [AC_LANG_PROGRAM([#include <cvc3/vc.h>], 
      [CVC3::Expr expr])],
    [AC_DEFINE(HAVE_CVC3, 1, [Define if you want to use CVC3])]
    [CVC3_LIBS="-lcvc3"]
    [USE_CVC3="yes"],
    [AC_MSG_WARN([cannot find CVC3 libraries])]
    [USE_CVC3="no"])
LIBS=$LIBS_SAVED
AC_SUBST(CVC3_LIBS)
AC_SUBST(USE_CVC3)

dnl ***********************
dnl Yices support
dnl ***********************
AC_ARG_WITH([yices],
            [AS_HELP_STRING([--with-yices=DIR],
              [Enable support for Yices from directory DIR])],
            [YICES_DIR=$withval])
if test "x$YICES_DIR" != "x" ; then
     AC_CHECK_FILE( ${YICES_DIR}/lib/libyices.a, [USE_YICES="yes"], [USE_YICES="no"] )
else
     [ USE_YICES="no" ] 
fi
AC_SUBST(USE_YICES)
AC_SUBST(YICES_DIR)

dnl ***********************
dnl GCC plugin support
dnl ***********************
GCC_PLUGIN_SUPPORT=no
GCC_PLUGIN_HEADERS=`$CC -print-file-name=plugin/include | awk '{print $NF}'`
# if we can't find the plugin/include path, we just get back "plugin/include"
if test "x$GCC_PLUGIN_HEADERS" != "xplugin/include" ; then
   GCC_PLUGIN_SUPPORT=yes
else
   AC_MSG_WARN([GCC plugin support not available, consider modifying your path to include gcc 4.5 or later])
fi
AC_SUBST(GCC_PLUGIN_SUPPORT)
AC_SUBST(GCC_PLUGIN_HEADERS)

dnl **********************
dnl Sometimes symbols in cc1/cc1plus are extern "C", sometimes mangled C++
dnl **********************
AC_MSG_CHECKING([symbol linkage in cc1])
CC1_BINARY=`$CC --print-prog-name=cc1`
CC1_LINKAGE=`nm -D $CC1_BINARY | egrep -q 'T print_node$' && echo C || echo mangled`
AC_MSG_RESULT($CC1_LINKAGE)
AC_MSG_CHECKING([symbol linkage in cc1plus])
CC1PLUS_BINARY=`$CC --print-prog-name=cc1plus`
CC1PLUS_LINKAGE=`nm -D $CC1PLUS_BINARY | egrep -q 'T print_node$' && echo C || echo mangled`
AC_MSG_RESULT($CC1PLUS_LINKAGE)
if test "$CC1_LINKAGE" = "$CC1PLUS_LINKAGE"; then
  if test "$CC1_LINKAGE" = "mangled"; then
    PLUGIN_CC=$CXX
  else
    PLUGIN_CC=$CC
  fi
else
  AC_MSG_ERROR([cc1 and cc1plus use different linkage])
fi
AC_SUBST(PLUGIN_CC)

dnl ***********************
dnl Results
dnl ***********************
AC_CONFIG_FILES([config.mk])

AC_OUTPUT

AC_MSG_RESULT([

===============================================================
sixgill configuration (Please review)

           * Install:
             - prefix:                  $prefix

           * Solvers:
             - CVC3:                    $USE_CVC3
             - Yices:                   $USE_YICES

           * GCC Plugin:                $GCC_PLUGIN_SUPPORT

===============================================================

])

