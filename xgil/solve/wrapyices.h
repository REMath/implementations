
// Sixgill: Static assertion checker for C/C++ programs.
// Copyright (C) 2009-2010  Stanford University
// Author: Brian Hackett
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

// needed for yices_get_mpz_value
#include <gmp.h>

#include <util/assert.h>
#include <util/ostream.h>
#include <yices_c.h>

// #define YICES_DEBUG_CALLS

#ifdef YICES_DEBUG_CALLS

extern FileOutStream yices_out;

inline const char* string_expr(yices_expr e) {
  char *buf = new char[200];
  sprintf(buf, "expr_%lx", (unsigned long) e);
  return buf;
}

inline const char* string_decl(yices_var_decl d) {
  char *buf = new char[200];
  sprintf(buf, "decl_%lx", (unsigned long) d);
  return buf;
}

inline const char* string_type(yices_type t) {
  char *buf = new char[200];
  sprintf(buf, "type_%lx", (unsigned long) t);
  return buf;
}

#define YICES_VOID_CALL(STREAM_DATA)                \
  yices_out << STREAM_DATA << ";" << endl << flush

#define YICES_EXPR_CALL(EXPR, STREAM_DATA)          \
  yices_out << string_expr(EXPR) << " = "           \
            << STREAM_DATA << ";" << endl << flush

#define YICES_DECL_CALL(DECL, STREAM_DATA)          \
  yices_out << string_decl(DECL) << " = "           \
            << STREAM_DATA << ";" << endl << flush

#define YICES_TYPE_CALL(TYPE, STREAM_DATA)          \
  yices_out << string_type(TYPE) << " = "           \
            << STREAM_DATA << ";" << endl << flush

#define YICES_EXPR_FILL_ARGS(ARGS, COUNT)                               \
  for (int ind = 0; ind < COUNT; ind++) {                               \
    yices_out << "expr_args[" << ind << "] = "                          \
              << string_expr(ARGS[ind]) << ";" << endl << flush;        \
  }

#define YICES_TYPE_FILL_ARGS(ARGS, COUNT)                               \
  for (int ind = 0; ind < COUNT; ind++) {                               \
    yices_out << "type_args[" << ind << "] = "                          \
              << string_type(ARGS[ind]) << ";" << endl << flush;        \
  }

#define YICES_FAILURE  Assert(false)

#else // YICES_DEBUG_CALLS

#define YICES_VOID_CALL(STREAM_DATA)
#define YICES_EXPR_CALL(EXPR, STREAM_DATA)
#define YICES_DECL_CALL(DECL, STREAM_DATA)
#define YICES_TYPE_CALL(TYPE, STREAM_DATA)

#define YICES_EXPR_FILL_ARGS(ARGS, COUNT)
#define YICES_TYPE_FILL_ARGS(ARGS, COUNT)

#define YICES_FAILURE

#endif // YICES_DEBUG_CALLS

inline yices_context wrap_yices_mk_context()
{
  YICES_VOID_CALL("cxt = yices_mk_context()");
  return yices_mk_context();
}

inline void wrap_yices_del_context(yices_context cxt)
{
  YICES_VOID_CALL("yices_del_context(cxt)");
  yices_del_context(cxt);
}

inline void wrap_yices_dump_context(yices_context cxt)
{
  YICES_VOID_CALL("yices_dump_context(cxt)");
  yices_dump_context(cxt);
}

inline void wrap_yices_push(yices_context cxt)
{
  YICES_VOID_CALL("yices_push(cxt)");
  yices_push(cxt);
}

inline void wrap_yices_pop(yices_context cxt)
{
  YICES_VOID_CALL("yices_pop(cxt)");
  yices_pop(cxt);
}

inline void wrap_yices_assert(yices_context cxt, yices_expr e)
{
  YICES_VOID_CALL("yices_assert(cxt, " << string_expr(e) << ")");
  yices_assert(cxt, e);
}

inline assertion_id wrap_yices_assert_retractable(yices_context cxt, yices_expr e)
{
  YICES_FAILURE;
  return yices_assert_retractable(cxt, e);
}

inline void wrap_yices_retract(yices_context cxt, assertion_id id)
{
  YICES_FAILURE;
  yices_retract(cxt, id);
}

inline lbool wrap_yices_check(yices_context cxt)
{
  YICES_VOID_CALL("yices_check(cxt)");
  return yices_check(cxt);
}

inline void wrap_yices_pp_expr(yices_expr e)
{
  YICES_VOID_CALL("yices_pp_expr(" << string_expr(e) << ")");
  yices_pp_expr(e);
}

inline yices_model wrap_yices_get_model(yices_context cxt)
{
  YICES_VOID_CALL("model = yices_get_model(cxt)");
  return yices_get_model(cxt);
}

inline void wrap_yices_display_model(yices_model model)
{
  YICES_VOID_CALL("yices_display_model(model)");
  yices_display_model(model);
}

inline yices_type wrap_yices_mk_type(yices_context cxt, const char *name)
{
  yices_type t = yices_mk_type(cxt, const_cast<char*>(name));
  YICES_TYPE_CALL(t, "yices_mk_type(cxt, \"" << name << "\")");
  return t;
}

inline yices_type wrap_yices_mk_function_type(yices_context cxt,
                                              yices_type args[], int num,
                                              yices_type ret)
{
  yices_type t = yices_mk_function_type(cxt, args, num, ret);
  YICES_TYPE_FILL_ARGS(args, num);
  YICES_TYPE_CALL(t, "yices_mk_function_type(cxt, type_args, "
                  << num << ", " << string_type(ret) << ")");
  return t;
}

inline yices_expr wrap_yices_mk_num_from_mpz(yices_context cxt, const mpz_t val)
{
  yices_expr e = yices_mk_num_from_mpz(cxt, val);

#ifdef YICES_DEBUG_CALLS
  static char buf[1000];
#endif

  // change this to yices_mk_num_from_string in the output.
  YICES_EXPR_CALL(e, "yices_mk_num_from_string(cxt, \"" << mpz_get_str(buf, 10, val) << "\")");
  return e;
}

inline yices_expr wrap_yices_mk_num_from_string(yices_context cxt, char *str)
{
  yices_expr e = yices_mk_num_from_string(cxt, str);
  YICES_EXPR_CALL(e, "yices_mk_num_from_string(cxt, \"" << str << "\")");
  return e;
}

inline yices_expr wrap_yices_mk_num(yices_context cxt, int n)
{
  yices_expr e = yices_mk_num(cxt, n);
  YICES_EXPR_CALL(e, "yices_mk_num(cxt, " << n << ")");
  return e;
}

inline yices_expr wrap_yices_mk_true(yices_context cxt)
{
  yices_expr e = yices_mk_true(cxt);
  YICES_EXPR_CALL(e, "yices_mk_true(cxt)");
  return e;
}

inline yices_expr wrap_yices_mk_false(yices_context cxt)
{
  yices_expr e = yices_mk_false(cxt);
  YICES_EXPR_CALL(e, "yices_mk_false(cxt)");
  return e;
}

inline yices_var_decl wrap_yices_mk_var_decl(yices_context cxt, char *name, yices_type type)
{
  yices_var_decl d = yices_mk_var_decl(cxt, name, type);
  YICES_DECL_CALL(d,
    "yices_mk_var_decl(cxt, \"" << name << "\", " << string_type(type) << ")");
  return d;
}

inline yices_expr wrap_yices_mk_var_from_decl(yices_context cxt, yices_var_decl d)
{
  yices_expr e = yices_mk_var_from_decl(cxt, d);
  YICES_EXPR_CALL(e, "yices_mk_var_from_decl(cxt, " << string_decl(d) << ")");
  return e;
}

#define YICES_EXPR_UNARY(NAME)                                          \
  inline yices_expr wrap_yices_mk_##NAME (yices_context cxt,            \
                                          yices_expr be)                \
  {                                                                     \
    yices_expr e = yices_mk_##NAME (cxt, be);                           \
    YICES_EXPR_CALL(e, "yices_mk_" #NAME "(cxt, "                       \
                    << string_expr(be) << ")");                         \
    return e;                                                           \
  }

YICES_EXPR_UNARY(not)

#define YICES_EXPR_BINARY(NAME)                                         \
  inline yices_expr wrap_yices_mk_##NAME (yices_context cxt,            \
                                          yices_expr le, yices_expr re) \
  {                                                                     \
    yices_expr e = yices_mk_##NAME (cxt, le, re);                       \
    YICES_EXPR_CALL(e, "yices_mk_" #NAME "(cxt, "                       \
                    << string_expr(le) << ", "                          \
                    << string_expr(re) << ")");                         \
    return e;                                                           \
  }

YICES_EXPR_BINARY(lt)
YICES_EXPR_BINARY(gt)
YICES_EXPR_BINARY(le)
YICES_EXPR_BINARY(ge)
YICES_EXPR_BINARY(eq)
YICES_EXPR_BINARY(diseq)

#define YICES_EXPR_TERNARY(NAME)                                        \
  inline yices_expr wrap_yices_mk_##NAME (yices_context cxt,            \
                                          yices_expr fe, yices_expr le, \
                                          yices_expr re)                \
  {                                                                     \
    yices_expr e = yices_mk_##NAME (cxt, fe, le, re);                   \
    YICES_EXPR_CALL(e, "yices_mk_" #NAME "(cxt, "                       \
                    << string_expr(fe) << ", "                          \
                    << string_expr(le) << ", "                          \
                    << string_expr(re) << ")");                         \
    return e;                                                           \
  }

YICES_EXPR_TERNARY(ite)

#define YICES_EXPR_NARY(NAME)                                           \
  inline yices_expr wrap_yices_mk_##NAME (yices_context cxt,            \
                                          yices_expr args[], int num)   \
  {                                                                     \
    yices_expr e = yices_mk_##NAME (cxt, args, num);                    \
    YICES_EXPR_FILL_ARGS(args, num);                                    \
    YICES_EXPR_CALL(e, "yices_mk_" #NAME "(cxt, expr_args, "            \
                    << num << ")");                                     \
    return e;                                                           \
  }

YICES_EXPR_NARY(and)
YICES_EXPR_NARY(or)
YICES_EXPR_NARY(sum)
YICES_EXPR_NARY(sub)
YICES_EXPR_NARY(mul)

inline yices_expr wrap_yices_mk_app(yices_context cxt, yices_expr func,
                                    yices_expr args[], int num)
{
  yices_expr e = yices_mk_app(cxt, func, args, num);
  YICES_EXPR_FILL_ARGS(args, num);
  YICES_EXPR_CALL(e, "yices_mk_app(cxt, " << string_expr(func)
                  << ", expr_args, " << num << ")");
  return e;
}

inline lbool wrap_yices_get_value(yices_model model, yices_var_decl d)
{
  YICES_VOID_CALL("yices_get_value(model, " << string_decl(d) << ")");
  return yices_get_value(model, d);
}

inline int wrap_yices_get_int_value(yices_model model, yices_var_decl d, long *pv)
{
  YICES_VOID_CALL("yices_get_int_Value(model, " << string_decl(d) << ", &long_val)");
  return yices_get_int_value(model, d, pv);
}

inline int wrap_yices_get_mpz_value(yices_model model, yices_var_decl d, mpz_t v)
{
  YICES_VOID_CALL("yices_get_mpz_value(model, " << string_decl(d) << ", mpz_val)");
  return yices_get_mpz_value(model, d, v);
}

inline lbool wrap_yices_evaluate_in_model(yices_model model, yices_expr e)
{
  YICES_VOID_CALL("yices_evaluate_in_model(model, " << string_expr(e) << ")");
  return yices_evaluate_in_model(model, e);
}
