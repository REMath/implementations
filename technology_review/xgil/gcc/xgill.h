
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

// all includes and functions needed to convert GCC trees into XIL structures.

#ifndef XIL_MAIN
#define XIL_MAIN

#include <gcc-plugin.h>
#include <config.h>
#include <system.h>
#include <coretypes.h>
#include <tm.h>
#include <tree.h>

#include "../imlang/interface.h"

// suppress weird error with CUMULATIVE_ARGS not defined in target.h
#ifndef CUMULATIVE_ARGS
#define CUMULATIVE_ARGS int
#endif

// stream used to print all log data (warnings, errors, diagnostics).
extern FILE *xil_log;

// directory containing the log file, NULL for no log file.
extern const char *xil_log_directory;

// IP address of database manager, NULL for no manager.
extern const char *xil_remote_address;

// path which can be used to invoke gcc, for annotation processing.
extern const char *xil_gcc_path;

// path to this plugin passed via -fplugin.
extern const char *xil_plugin_path;

// gcc binary and command line arguments used to invoke the plugin.
extern const char *xil_command;

// if an error is encountered during annotation processing, name of the
// file to write information about that error.
extern const char *xil_annotation_single;

// whether our input file is generating an annotation CFG.
extern bool xil_has_annotation;

// if the annotation CFG is a type invariant, the 'this' type.
extern tree xil_annotation_this;

// common width used by all constructed pointer types. we check this against
// the pointer types we get from GCC.
extern int xil_pointer_width;

// set to zero to disable generation of record types.
extern int xil_generate_record_types;

// information about post side effects (postincr, postdecr) that were added
// to the CFG at some tree node.
struct XIL_PostEdges
{
  // start/end points of the post side effects. these are zero if no post
  // side effects have been generated for this point.
  XIL_PPoint start_point;
  XIL_PPoint end_point;
};

#define MAKE_POST_EDGES(NAME)                           \
  struct XIL_PostEdges NAME;                            \
  memset(&NAME, 0, sizeof(struct XIL_PostEdges));

// translation environment for a tree with side effects.
struct XIL_TreeEnv
{
  // point to receive side effects of the tree. this is mutable and will be
  // updated as new side effects are generated.
  XIL_PPoint *point;

  // information about where to store post side effects of the tree.
  // this may be NULL, in which case temporaries will be generated to model
  // the behavior of post operations.
  struct XIL_PostEdges *post_edges;

  // whether the result fields below have been processed and used/filled with
  // the appropriate values. this is mutable.
  bool processed;

  // whether the result of this expression should branch to true_point
  // or false_point below. after the TranslateTree, there will be paths
  // from the original value of point to true_point and false_point.
  bool result_branch;

  // point to jump to if this tree evaluates to true/false.
  // only used if result_branch is true.
  XIL_PPoint true_point;
  XIL_PPoint false_point;

  // lvalue to assign the value of this tree to, NULL if there is none.
  XIL_Exp result_assign;

  // type of the assignment, only used if result_assign != NULL.
  XIL_Type result_assign_type;

  // pointer to receive the lvalue result of the tree. NULL if the
  // expression will not be used as an lvalue.
  XIL_Exp *result_lval;

  // pointer to receive the rvalue result of the tree. NULL if the
  // expression will not be used as an rvalue.
  XIL_Exp *result_rval;

  // at most one use of the result (branch/assign/lval/rval) can be set.
  // if none are set the result is discarded.
};

// define a local tree environment and initialize it. this should be
// used for all calls to TranslateTree.
#define MAKE_ENV(NAME, POINT, POST)             \
  struct XIL_TreeEnv NAME;                      \
  memset(&NAME, 0, sizeof(struct XIL_TreeEnv)); \
  NAME.point = POINT;                           \
  NAME.post_edges = POST;

static inline bool XIL_TreeResultUsed(struct XIL_TreeEnv *env)
{
  return env->result_branch || env->result_assign != NULL
      || env->result_lval != NULL || env->result_rval != NULL;
}

// information about a virtual function for a CSU.
struct XIL_VirtualFunction
{
  // if the function was inherited from a base, indicates the direct base
  // which was inherited from.
  XIL_Field base;

  // field added for the function. if the function was inherited from a base
  // class then this indicates the original base the function was declared for.
  XIL_Field field;

  // declaration of the function. if the function is overridden this indicates
  // the active declaration, not the original declaration.
  tree decl;

  // index into the vtable for this function. -1 for functions not in the
  // vtable, i.e. those inherited from the second or later base and which
  // were not overridden by this class.
  int index;

  // link in the list of virtual functions on the CSU.
  struct XIL_VirtualFunction *next;
};

// get the list of function fields for the specified type, making it if needed.
struct XIL_VirtualFunction* XIL_GetFunctionFields(tree type);

// information about a local variable within a function. we need to keep around
// all the local variables in a function to watch for duplicate names.
struct XIL_LocalData
{
  // declaration for the variable.
  tree decl;

  // XIL representation of this variable.
  XIL_Var var;

  // next local variable in the function.
  struct XIL_LocalData *block_next;

  // next local variable in the defining scope.
  struct XIL_LocalData *scope_next;
};

// translation environment for a scope. scopes are introduced when we want to
// attach some property to an entire subtree we are traversing.
struct XIL_ScopeEnv
{
  // scope to restore when this one finishes.
  struct XIL_ScopeEnv *parent;

  // local variables declared in this scope. needed for annotation processing.
  struct XIL_LocalData *locals;

  // points to jump to on a break or continue tree.
  XIL_PPoint break_point;
  XIL_PPoint continue_point;

  // for switch statements, the expression switched on and mutable
  // points for the frontier of generated branches and default point.
  XIL_Exp switch_test;
  XIL_PPoint switch_point;
  XIL_PPoint default_point;

  // edges that have been introduced for cleanup points at the end
  // of this scope.
  struct XIL_PostEdges *cleanup_edges;

  // for a cleanup statement (C++ structures with destructors),
  // the cleanup to perform when exiting this scope.
  tree cleanup;

  // exit point for a loop expr.
  XIL_PPoint exit_point;
};

// active scope for the currently active block.
extern struct XIL_ScopeEnv *xil_active_scope;

void XIL_ActivePushScope();
void XIL_ActivePopScope();

// information about a goto a label which has not been encountered yet.
// for cp we don't know what cleanup to perform before jumping so we'll delay
// generation of the goto edge until we see the label and its scope.
struct XIL_GotoData
{
  // source of the goto. before the label is encountered this does not have
  // any outgoing edges in the CFG.
  XIL_PPoint point;

  // scope which contains the goto.
  struct XIL_ScopeEnv *scope;

  // next link in the list of gotos.
  struct XIL_GotoData *next;
};

// information about a label within a function. one of these is associated
// with every LABEL_DECL. parts of this structure are filled in at various
// times because we might see either the gotos for the label or the label
// itself first during our traversal, and we don't want to do a prepass to
// identify all the labels.
struct XIL_LabelData
{
  // point which the label corresponds to. filled in once the label
  // has been encountered.
  XIL_PPoint point;

  // scope which contains the label. filled in once the label has been
  // encountered.
  struct XIL_ScopeEnv *scope;

  // list of information about gotos for this label which were encountered
  // before the label itself was.
  struct XIL_GotoData *gotos;
};

// add a path between source and target which incorporates any necessary
// cleanup due to the scopes of the points. not used just for goto,
// but also return, break, continue. target_scope may be NULL for the
// function's entire scope.
void XIL_ResolveGoto(XIL_PPoint source, XIL_PPoint target,
                     struct XIL_ScopeEnv *source_scope,
                     struct XIL_ScopeEnv *target_scope);

struct XIL_PendingAnnotation
{
  tree type;
  tree attr;
  struct XIL_PendingAnnotation *next;
};

// global translation environment.
struct XIL_BlockEnv
{
  // declaration for the global or function variable we are processing.
  // if this is non-NULL then the active block has been set.
  tree decl;

  // name of the variable we are processing.
  const char *decl_name;

  // whether we have dropped this CFG due to encountering an unexpected tree.
  int dropped;

  // number of temporaries generated for the CFG.
  int temp_count;

  // number of annotations generated for the CFG.
  int annot_count;

  // entry/exit points of the CFG.
  XIL_PPoint entry_point;
  XIL_PPoint exit_point;

  // most recent point in the CFG, for handling AST nodes without location info.
  XIL_PPoint last_point;

  // all local variables in the CFG.
  struct XIL_LocalData *locals;

  // pending annotations discovered in the CFG.
  struct XIL_PendingAnnotation *annots;
};

// the active block environment.
extern struct XIL_BlockEnv xil_active_env;

// information about parameter declarations we have seen for the upcoming
// function declaration. this is needed for the C frontend, where function
// declarations do not have their parameter declarations as children.
struct XIL_ParamDecl
{
  tree decl;
  struct XIL_ParamDecl *next;
};
extern struct XIL_ParamDecl *xil_pending_param_decls;

// get the unique name to use for a global symbol. this may be a global
// variable/function, static unit scope variable, or static function
// scope variable.
const char* XIL_GlobalName(tree decl);

// get the non-unique name from the source to use for a global/local symbol.
const char* XIL_SourceName(tree decl);

// get the fully qualified name of a type or namespace declaration.
const char* XIL_QualifiedName(tree decl);

// gets a new temporary variable of the specified type.
XIL_Var XIL_NewTemporary(XIL_Type type);

// return whether type is a CSU or pointer/array of CSUs which does not
// have an explicit name. for C this is any CSU declared with 'struct { ... }',
// for C++ this is all CSUs.
bool XIL_IsAnonymous(tree type);

// return whether decl is a CSU with a fake name introduced by the C++ FE.
bool XIL_IsAnonymousCxx(tree decl);

// return whether type is declaring the same type as its own context.
// these appear in the fields for C++ structures.
bool XIL_IsSelfTypeDecl(tree decl);

// return whether field is a potential base class field of its container type:
// it does not have a name, but is not an anonymous structure. offset_zero
// will be set to indicate whether the field is at offset zero.
bool XIL_IsBaseField(tree field, bool *offset_zero);

// return whether decl is a destructor function decl. we need to fixup the
// names for these.
bool XIL_IsDestructor(tree decl);

// if type is a struct or union, assign it the specified name if it
// is anonymous. returns whichever name is assigned. name may be NULL,
// in which case no assign will be performed.
const char* XIL_CSUName(tree type, const char *name);

// node in the translation stack used to keep track of the context a node is
// translated in, for debugging.
struct XIL_StackNode
{
  // translation function at this point in the stack.
  const char *name;

  // file/line of the call to this function.
  const char *file;
  int line;

  // tree node being translated.
  tree node;

  // next node in the stack.
  struct XIL_StackNode *next;
};

// top of the translation stack.
extern struct XIL_StackNode *xil_stack;

#define XIL_PUSH_STACK(NAME, TREE)                    \
  struct XIL_StackNode stack_node;                    \
  stack_node.name = NAME;                             \
  stack_node.file = __FILE__;                         \
  stack_node.line = __LINE__;                         \
  stack_node.node = TREE;                             \
  stack_node.next = xil_stack;                        \
  xil_stack = &stack_node

#define XIL_POP_STACK()                         \
  gcc_assert(xil_stack == &stack_node);         \
  xil_stack = xil_stack->next

void XIL_PrintStack();

// Translation interface. these are macros to maintain the translation
// stack in the active environment.

// get the XIL type from a type tree.
XIL_Type generate_TranslateType(tree type);
#define XIL_TranslateType(TYPE)                 \
  ({                                            \
  XIL_PUSH_STACK("TranslateType", TYPE);        \
  XIL_Type res = generate_TranslateType(TYPE);  \
  XIL_POP_STACK();                              \
  res;                                          \
  })

// get the XIL field from a field declaration tree.
XIL_Field generate_TranslateField(tree decl);
#define XIL_TranslateField(DECL)                        \
  ({                                                    \
  XIL_PUSH_STACK("TranslateField", DECL);               \
  XIL_Field res = generate_TranslateField(DECL);        \
  XIL_POP_STACK();                                      \
  res;                                                  \
  })

// get the XIL variable from a declaration tree.
XIL_Var generate_TranslateVar(tree decl);
#define XIL_TranslateVar(DECL)                  \
  ({                                            \
  XIL_PUSH_STACK("TranslateVar", DECL);         \
  XIL_Var res = generate_TranslateVar(DECL);    \
  XIL_POP_STACK();                              \
  res;                                          \
  })

// get the value of a tree in the body of a function, adding any
// side effects according to env and the active block env.
void generate_TranslateTree(struct XIL_TreeEnv *env, tree node);
#define XIL_TranslateTree(ENV, NODE)            \
  ({                                            \
  XIL_PUSH_STACK("TranslateTree", NODE);        \
  generate_TranslateTree(ENV, NODE);            \
  XIL_POP_STACK();                              \
  })

// signal an unexpected tree encountered during translation. prints the
// file/line of the signal and the contents of the tree, then bail out.
#define TREE_UNEXPECTED(TREE)                                           \
  do {                                                                  \
    if (!xil_active_env.dropped) {                                      \
      fprintf(xil_log, "\nXIL: Unexpected tree (%s:%d):\n",             \
              __FILE__, __LINE__);                                      \
      print_node(xil_log, "", (TREE), 0);                               \
      fprintf(xil_log,"\n\n");                                          \
      XIL_PrintStack();                                                 \
      fflush(xil_log);                                                  \
      xil_active_env.dropped = 1;                                       \
    }                                                                   \
  } while (0)

// report an unexpected tree and fill in the tree result with an error var.
#define TREE_UNEXPECTED_RESULT(ENV, TREE)               \
  do {                                                  \
    TREE_UNEXPECTED(TREE);                              \
    XIL_Var error_var = XIL_VarGlob("error", "error");  \
    XIL_Exp error_exp = XIL_ExpVar(error_var);          \
    XIL_Exp error_drf = XIL_ExpDrf(error_exp);          \
    XIL_ProcessResult(ENV, error_drf);                  \
    return;                                             \
  } while (0)

void XIL_DebugPrint(tree node);

// as with TREE_UNEXPECTED, but less log information. these are cases where
// our translation is incomplete but the issue is known.
#define TREE_UNHANDLED()                                                \
  do {                                                                  \
    if (!xil_active_env.dropped) {                                      \
      fprintf(xil_log, "\nXIL: Unhandled tree (%s:%d)\n\n",             \
              __FILE__, __LINE__);                                      \
      fflush(xil_log);                                                  \
      xil_active_env.dropped = 1;                                       \
    }                                                                   \
  } while (0)
#define TREE_UNHANDLED_RESULT(ENV)                      \
  do {                                                  \
    TREE_UNHANDLED();                                   \
    XIL_Var error_var = XIL_VarGlob("error", "error");  \
    XIL_Exp error_exp = XIL_ExpVar(error_var);          \
    XIL_Exp error_drf = XIL_ExpDrf(error_exp);          \
    XIL_ProcessResult(ENV, error_drf);                  \
    return;                                             \
  } while (0)

// as with TREE_UNHANDLED, but no log information and does not cause compilation
// to abort. Use for expressions with no reasonable translation but for which
// an approximate CFG is still desired.
#define TREE_BOGUS()
#define TREE_BOGUS_RESULT(ENV)                          \
  do {                                                  \
    TREE_BOGUS();                                       \
    XIL_Var error_var = XIL_VarGlob("error", "error");  \
    XIL_Exp error_exp = XIL_ExpVar(error_var);          \
    XIL_Exp error_drf = XIL_ExpDrf(error_exp);          \
    XIL_ProcessResult(ENV, error_drf);                  \
    return;                                             \
  } while (0)

// get a small unsigned integer constant from a tree.
#define TREE_UINT(TREE)                                 \
  ({ gcc_assert(TREE);                                  \
     TREE_CHECK(TREE, INTEGER_CST);                     \
     gcc_assert(TREE_INT_CST_HIGH(TREE) == 0);          \
     TREE_INT_CST_LOW(TREE); })

// get an integer constant from a tree as a string.
const char* XIL_TreeIntString(tree node);

// get the name of an attribute and any text or integer value it has.
const char* XIL_DecodeAttribute(tree attr,
                                const char **text_value, int *int_value);

// if attribute indicates an annotation, consume it and add it to the backend
// databases. attribute is attached to node (either the active function
// or the active type). return value indicates whether this is actually
// an annotation attribute.
bool XIL_ProcessAnnotationAttr(tree node, tree attr, XIL_PPoint *point,
                               XIL_Location loc);

// consume an annotation read from an annotation file.
void XIL_ProcessAnnotationRead(tree node, const char *where,
                               const char *point_text, const char *annot_text,
                               bool trusted);

#endif // XIL_MAIN
