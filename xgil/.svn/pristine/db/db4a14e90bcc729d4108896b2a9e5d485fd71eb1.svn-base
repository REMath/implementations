
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

// C interface for constructing IL structures and writing them
// to output databases. for frontends which can call into C but
// are not written in C++ or can't use the Xgill headers directly.

#ifndef XIL_INTERFACE
#define XIL_INTERFACE

#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct _struct_XIL_Location* XIL_Location;
typedef struct _struct_XIL_Type* XIL_Type;
typedef struct _struct_XIL_Field* XIL_Field;
typedef struct _struct_XIL_Var* XIL_Var;
typedef struct _struct_XIL_Exp* XIL_Exp;
typedef int XIL_PPoint;

/////////////////////////////////////////////////////////////////////
// Utility
/////////////////////////////////////////////////////////////////////

// sets a file to use for printing log data. all output will be directed here,
// except from XIL_Print and XIL_PrintGenerated.
void XIL_SetLogFile(FILE *file);

// gets file where log data is being printed. this is stdout if SetLogFile
// has not been called.
FILE* XIL_GetLogFile();

// print any of the various xgill objects to the log.
void XIL_Print(void *object);

// set the path to use as the base of generated locations.
void XIL_SetNormalizeDirectory(const char *path);

// make a location for file/line. file may be relative to the current
// working directory, and the result location will be normalized per
// the normalize directory.
XIL_Location XIL_MakeLocation(const char *file, int line);

// levels at which we can associate pointers. these differ over the points
// at which they are cleared.
typedef enum {
  // associations cleared after each annotation.
  XIL_AscAnnotate,

  // associations cleared after each block.
  XIL_AscBlock,

  // associations which are never cleared.
  XIL_AscGlobal

} XIL_AssociateKind;

// association hashtable interface between two pointers. the pointer initially
// associated with a value is zero.
void** XIL_Associate(XIL_AssociateKind table, const char *kind, void *value);
void XIL_ClearAssociate(XIL_AssociateKind table);

/////////////////////////////////////////////////////////////////////
// Annotations
/////////////////////////////////////////////////////////////////////

#define XIL_ITERATE_ANNOT(MACRO)                                \
    /* preconditions holding at entry to a function. */         \
  MACRO(Precondition, "precondition", 1)                        \
  MACRO(PreconditionAssume, "precondition_assume", 2)           \
    /* postconditions holding at exit from a function. */       \
  MACRO(Postcondition, "postcondition", 3)                      \
  MACRO(PostconditionAssume, "postcondition_assume", 4)         \
    /* invariants holding for a type or global. */              \
  MACRO(Invariant, "invariant", 5)                              \
  MACRO(InvariantAssume, "invariant_assume", 6)                 \
    /* conditions holding at specific points in a function. */  \
  MACRO(Assert, "assert_static", 7)                             \
  MACRO(Assume, "assume_static", 8)                             \
  MACRO(AssertRuntime, "assert_static_runtime", 9)

enum _enum_XIL_AnnotationKind {
#define XIL_FILL_ANNOT(NAME, _, VALUE)  XIL_AK_ ## NAME = VALUE,
  XIL_ITERATE_ANNOT(XIL_FILL_ANNOT)
#undef XIL_FILL_ANNOT
};
typedef enum _enum_XIL_AnnotationKind XIL_AnnotationKind;

// read a file of annotations generated from the web interface.
void XIL_ReadAnnotationFile(const char *file);

// get the number of read annotations associated with a func/global/type.
int XIL_GetAnnotationCount(const char *name, bool global, bool type);

// get one of the read annotations associated with var.
void XIL_GetAnnotation(const char *name, bool global, bool type, int index,
                       const char **pwhere,
                       const char **ppoint_text, const char **pannot_text,
                       int *ptrusted);

// ensure that any generated annotations are forced to disk after processing
// is done. only write out CFGs affected by read annotations (annotations
// which indicate loop invariant or other assertions within the CFG).
void XIL_ForceAnnotationWrites();

/////////////////////////////////////////////////////////////////////
// Active block
/////////////////////////////////////////////////////////////////////

// set/clear the global variable or function we are generating a CFG for.
// if annot is specified then we are making an annotation CFG for var.
// annot_type indicates this is a type invariant (var is a global variable
// with the name of the type).
void XIL_SetActiveBlock(XIL_Var var, const char *annot_name,
                        XIL_AnnotationKind annot_kind, int annot_type);
void XIL_ClearActiveBlock(int drop);

/////////////////////////////////////////////////////////////////////
// Types
/////////////////////////////////////////////////////////////////////

XIL_Type XIL_TypeError();
XIL_Type XIL_TypeVoid();
XIL_Type XIL_TypeInt(int width, int sign);
XIL_Type XIL_TypeFloat(int width);
XIL_Type XIL_TypePointer(XIL_Type target_type, int width);
XIL_Type XIL_TypeArray(XIL_Type element_type, int count);
XIL_Type XIL_TypeCSU(const char *csu_name, int *generate);
XIL_Type XIL_TypeFunction(XIL_Type return_type, const char *this_csu,
                          int varargs, XIL_Type *arg_types, int arg_count);

// get the name associated with a CSU type, or NULL for non-CSU types.
const char* XIL_GetTypeCSUName(XIL_Type csu_type);

XIL_Field XIL_MakeField(const char *name, const char *source_name,
                        const char *csu_name, XIL_Type type, int is_func);

// push/pop the CSU type we are adding information about. adds are to the
// CSU at the top of the stack.
void XIL_PushActiveCSU(const char *name);
void XIL_PopActiveCSU(int drop);

// kinds that can be passed to CSUSetKind.
#define XIL_CSU_Class  1
#define XIL_CSU_Struct 2
#define XIL_CSU_Union  3

void XIL_CSUSetKind(int kind);
void XIL_CSUSetWidth(int width);
void XIL_CSUSetCommand(const char *command);
void XIL_CSUSetBeginLocation(XIL_Location begin_loc);
void XIL_CSUSetEndLocation(XIL_Location end_loc);
void XIL_CSUAddDataField(XIL_Field field, int offset);
void XIL_CSUAddFunctionField(XIL_Field field, XIL_Field base, XIL_Var func);

const char * XIL_MaybeDecorateFunction(const char *name, XIL_Type type);

/////////////////////////////////////////////////////////////////////
// Variables
/////////////////////////////////////////////////////////////////////

// make global variables or functions.
XIL_Var XIL_VarGlob(const char *name, const char *source_name);
XIL_Var XIL_VarFunc(const char *name, const char *source_name);

// make local variables whose context is either the active block or the
// function being annotated.
XIL_Var XIL_VarArg(int index, const char *name, int annot);
XIL_Var XIL_VarLocal(const char *name, const char *source_name, int annot);
XIL_Var XIL_VarReturn(int annot);
XIL_Var XIL_VarThis(int annot);

// make temporaries for the active block.
XIL_Var XIL_VarTemp(const char *name);

// get the name associated with a variable if there is one. for globals this
// will be the full name rather than the source name.
const char* XIL_GetVarName(XIL_Var var);

/////////////////////////////////////////////////////////////////////
// Opcodes
/////////////////////////////////////////////////////////////////////

#define XIL_ITERATE_UNOP(MACRO)                 \
    /* arith -> arith */                        \
  MACRO(Coerce, 1)                              \
  MACRO(Neg, 2)                                 \
  MACRO(BitwiseNot, 3)                          \
    /* bool -> bool */                          \
  MACRO(LogicalNot, 4)

#define XIL_UNOP_COUNT  5

enum _enum_XIL_UnopKind {
#define XIL_FILL_UNOP(NAME, VALUE)  XIL_U_ ## NAME = VALUE,
  XIL_ITERATE_UNOP(XIL_FILL_UNOP)
#undef XIL_FILL_UNOP
};
typedef enum _enum_XIL_UnopKind XIL_UnopKind;

#define XIL_ITERATE_BINOP(MACRO)                \
    /* arith x arith -> arith */                \
  MACRO(Plus, 1)                                \
  MACRO(Minus, 2)                               \
  MACRO(Mult, 3)                                \
  MACRO(Div, 4)                                 \
  MACRO(Mod, 5)                                 \
  MACRO(ShiftLeft, 6)                           \
  MACRO(ShiftRight, 7)                          \
  MACRO(BitwiseAnd, 8)                          \
  MACRO(BitwiseOr, 9)                           \
  MACRO(BitwiseXOr, 10)                         \
  MACRO(Min, 11)                                \
  MACRO(Max, 12)                                \
  MACRO(DivExact, 13)                           \
    /* pointer x arith -> pointer */            \
  MACRO(PlusPI, 20)                             \
  MACRO(MinusPI, 21)                            \
    /* pointer x pointer -> arith */            \
  MACRO(MinusPP, 22)                            \
    /* arith x arith -> bool */                 \
  MACRO(LessThan, 30)                           \
  MACRO(GreaterThan, 31)                        \
  MACRO(LessEqual, 32)                          \
  MACRO(GreaterEqual, 33)                       \
  MACRO(Equal, 34)                              \
  MACRO(NotEqual, 35)                           \
    /* pointer x pointer -> bool */             \
  MACRO(LessThanP, 40)                          \
  MACRO(GreaterThanP, 41)                       \
  MACRO(LessEqualP, 42)                         \
  MACRO(GreaterEqualP, 43)                      \
  MACRO(EqualP, 44)                             \
  MACRO(NotEqualP, 45)                          \
    /* bool x bool -> bool */                   \
  MACRO(LogicalAnd, 50)                         \
  MACRO(LogicalOr, 51)

#define XIL_BINOP_COUNT  60

enum _enum_XIL_BinopKind {
#define XIL_FILL_BINOP(NAME, VALUE)  XIL_B_ ## NAME = VALUE,
  XIL_ITERATE_BINOP(XIL_FILL_BINOP)
#undef XIL_FILL_BINOP
};
typedef enum _enum_XIL_BinopKind XIL_BinopKind;

/////////////////////////////////////////////////////////////////////
// Expressions
/////////////////////////////////////////////////////////////////////

XIL_Exp XIL_ExpEmpty();
XIL_Exp XIL_ExpVar(XIL_Var var);
XIL_Exp XIL_ExpDrf(XIL_Exp target);
XIL_Exp XIL_ExpFld(XIL_Exp target, XIL_Field field);
XIL_Exp XIL_ExpRfld(XIL_Exp target, XIL_Field field);
XIL_Exp XIL_ExpIndex(XIL_Exp target, XIL_Type element_type, XIL_Exp index);
XIL_Exp XIL_ExpString(XIL_Type type, void *data, int data_length);
XIL_Exp XIL_ExpInt(long value);
XIL_Exp XIL_ExpIntStr(const char *value);
XIL_Exp XIL_ExpFloat(const char *value);
XIL_Exp XIL_ExpUnop(XIL_UnopKind unop, XIL_Exp op,
                    int bits, int sign);
XIL_Exp XIL_ExpBinop(XIL_BinopKind binop, XIL_Exp left_op, XIL_Exp right_op,
                     XIL_Type stride_type, int bits, int sign);

XIL_Exp XIL_ExpInitial(XIL_Exp target);
XIL_Exp XIL_ExpLBound(XIL_Exp target, XIL_Type stride_type);
XIL_Exp XIL_ExpUBound(XIL_Exp target, XIL_Type stride_type);
XIL_Exp XIL_ExpZTerm(XIL_Exp target, XIL_Type stride_type);
XIL_Exp XIL_ExpGCSafe(XIL_Exp target);
XIL_Exp XIL_ExpSkipInference();

// get the value of an integer expression and store it in value,
// otherwise return 0.
int XIL_GetExpInt(XIL_Exp exp, long *value);

// for an integer expression with its high bit set, transform it into the
// equivalent signed or unsigned integer, otherwise return the expression.
// XIL_ExpSign(4294967295, 32, true) == -1
// XIL_ExpSign(-1, 32, false) == 4294967295
XIL_Exp XIL_ExpSign(XIL_Exp exp, int bits, bool sign);

// take the address of target, if possible. NULL otherwise.
XIL_Exp XIL_ExpAddress(XIL_Exp target);

/////////////////////////////////////////////////////////////////////
// Blocks
/////////////////////////////////////////////////////////////////////

void XIL_CFGSetCommand(const char *command);
void XIL_CFGSetBeginLocation(XIL_Location begin_loc);
void XIL_CFGSetEndLocation(XIL_Location end_loc);
void XIL_CFGAddVar(XIL_Var var, XIL_Type type, int override);
XIL_PPoint XIL_CFGAddPoint(XIL_Location loc);
XIL_Location XIL_CFGGetPointLocation(XIL_PPoint point);
void XIL_CFGSetPointLocation(XIL_PPoint point, XIL_Location loc);
void XIL_CFGSetEntryPoint(XIL_PPoint point);
void XIL_CFGSetExitPoint(XIL_PPoint point);
void XIL_CFGAddLoopHead(XIL_PPoint point, XIL_Location end_loc);

void XIL_CFGEdgeSkip(XIL_PPoint source, XIL_PPoint target);
void XIL_CFGEdgeAssume(XIL_PPoint source, XIL_PPoint target,
                       XIL_Exp condition, int nonzero);
void XIL_CFGEdgeAssign(XIL_PPoint source, XIL_PPoint target,
                       XIL_Type type, XIL_Exp left_side, XIL_Exp right_side);
void XIL_CFGEdgeCall(XIL_PPoint source, XIL_PPoint target, XIL_Type func_type,
                     XIL_Exp return_assign, XIL_Exp instance, XIL_Exp func,
                     XIL_Exp *args, int arg_count);
void XIL_CFGEdgeAssembly(XIL_PPoint source, XIL_PPoint target);
void XIL_CFGEdgeAnnotation(XIL_PPoint source, XIL_PPoint target,
                           const char *annot_name);

/////////////////////////////////////////////////////////////////////
// Databases
/////////////////////////////////////////////////////////////////////

// do any necessary setup for generating CSUs and CFGs.
void XIL_SetupGenerate(const char *remote_address);

// print to the log all CSUs and CFGs that have been generated.
void XIL_PrintGenerated();

// write to the databases all CSUs and CFGs that have been generated.
void XIL_WriteGenerated();

// whether an annotation with the specified name has already been processed.
int XIL_HasAnnotation(XIL_Var var, const char *annot_name, int annot_type);

// write an annotation CFG indicating a processing error.
void XIL_AddAnnotationMsg(XIL_Var var, const char *annot_name,
                          XIL_AnnotationKind annot_kind, int annot_type,
                          XIL_Location loc, const char *annot_message);

#ifdef __cplusplus
} // extern "C"
#endif

#endif // XIL_INTERFACE
