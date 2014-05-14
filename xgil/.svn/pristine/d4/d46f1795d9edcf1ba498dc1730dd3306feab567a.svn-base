
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

#include "xgill.h"

#include <plugin.h>
#include <target.h>
#include <cp/cp-tree.h>

// for annotation processing
#include <cpplib.h>

// environment utility functions

FILE *xil_log = NULL;
const char *xil_log_directory = NULL;
const char *xil_remote_address = NULL;

const char *xil_gcc_path = NULL;
const char *xil_plugin_path = NULL;
const char *xil_command = NULL;
bool xil_has_annotation = false;
tree xil_annotation_this = NULL;

const char *xil_annotation_single = NULL;

// if our input file is generating an annotation CFG, the class ("func", "init"
// or "comp"), kind and name of annotation. the name of the variable/type
// being annotated comes from the annotation function.
static const char *annotation_class;
static const char *annotation_kind;
static const char *annotation_name;

int xil_pointer_width = 0;
struct XIL_ScopeEnv *xil_active_scope = NULL;
struct XIL_BlockEnv xil_active_env;

struct XIL_ParamDecl *xil_pending_param_decls = NULL;

void XIL_DebugPrint(tree node)
{
  fflush(stdout);
  print_node(stdout, "", node, 0);
  printf("\n\n");
  fflush(stdout);
}

void XIL_ActivePushScope()
{
  struct XIL_ScopeEnv *scope = xmalloc(sizeof(struct XIL_ScopeEnv));
  memset(scope, 0, sizeof(struct XIL_ScopeEnv));

  scope->parent = xil_active_scope;
  xil_active_scope = scope;
}

void XIL_ActivePopScope()
{
  struct XIL_ScopeEnv *scope = xil_active_scope;
  gcc_assert(scope);

  xil_active_scope = scope->parent;
}

void XIL_ResolveGoto(XIL_PPoint source, XIL_PPoint target,
                     struct XIL_ScopeEnv *source_scope,
                     struct XIL_ScopeEnv *target_scope)
{
  XIL_PPoint cur_point = source;

  while (source_scope) {
    // skip scopes which don't have any cleanup.
    if (!source_scope->cleanup) {
      source_scope = source_scope->parent;
      continue;
    }

    // don't need to do the cleanup if the target is also in this scope.
    bool needed = true;
    struct XIL_ScopeEnv *scope = target_scope;
    while (scope) {
      if (scope == source_scope) {
	needed = false;
        break;
      }
      scope = scope->parent;
    }
    if (!needed)
      break;

    MAKE_ENV(cleanup_env, &cur_point, NULL);
    XIL_TranslateTree(&cleanup_env, source_scope->cleanup);

    source_scope = source_scope->parent;
  }

  // do the final goto.
  XIL_CFGEdgeSkip(cur_point, target);
}

XIL_Var XIL_NewTemporary(XIL_Type type)
{
  xil_active_env.temp_count++;

  char name[100];
  sprintf(name, "__temp_%d", xil_active_env.temp_count);

  XIL_Var var = XIL_VarTemp(name);
  XIL_CFGAddVar(var, type, 0);

  return var;
}

struct XIL_StackNode *xil_stack = NULL;

void XIL_PrintStack()
{
  fprintf(xil_log, "XIL Stack:\n");

  struct XIL_StackNode *stack_node = xil_stack;
  while (stack_node) {
    fprintf(xil_log, "%s [%s:%d]: ", stack_node->name,
            stack_node->file, stack_node->line);
    print_node_brief(xil_log, "", stack_node->node, 0);
    fprintf(xil_log, "\n");

    stack_node = stack_node->next;
  }
}

const char* XIL_DecodeAttribute(tree attr,
                                const char **text_value, int *int_value)
{
  tree purpose = TREE_PURPOSE(attr);
  if (!purpose || TREE_CODE(purpose) != IDENTIFIER_NODE) {
    TREE_UNEXPECTED(attr);
    return NULL;
  }
  const char *name = IDENTIFIER_POINTER(purpose);

  tree value = TREE_VALUE(attr);
  if (!value)
    return name;

  if (TREE_CODE(value) != TREE_LIST) {
    TREE_UNEXPECTED(attr);
    return name;
  }
  value = TREE_VALUE(value);

  if (TREE_CODE(value) == STRING_CST) {
    if (text_value)
      *text_value = TREE_STRING_POINTER(value);
  }
  else if (TREE_CODE(value) == INTEGER_CST) {
    if (int_value)
      *int_value = TREE_INT_CST_LOW(value);
  }

  return name;
}

// generate a block for a declaration, which is either a function or global.
void XIL_GenerateBlock(tree decl)
{
  memset(&xil_active_env, 0, sizeof(struct XIL_BlockEnv));

  XIL_Var xil_var = NULL;
  int annot_type = 0;

  if (xil_has_annotation) {
    gcc_assert(annotation_name);
    gcc_assert(TREE_CODE(decl) == FUNCTION_DECL);

    // get the name of the function/global/type being annotated; this looks at
    // any annot_global / annot_source attributes on the decl.
    const char *full_name = XIL_GlobalName(decl);
    const char *name = XIL_SourceName(decl);

    if (!strcmp(annotation_class, "func"))
      xil_var = XIL_VarFunc(full_name, name);
    else if (!strcmp(annotation_class, "init"))
      xil_var = XIL_VarGlob(full_name, name);
    else if (!strcmp(annotation_class, "comp")) {
      xil_var = XIL_VarGlob(full_name, name);
      annot_type = 1;
    }

    gcc_assert(xil_var);
  }
  else {
    xil_var = XIL_TranslateVar(decl);
  }

  tree type = TREE_TYPE(decl);
  XIL_Type xil_type = XIL_TranslateType(type);

  // fixup the type for destructors. these have an __in_chrg argument that
  // doesn't show up when the functions are called.
  if (XIL_IsDestructor(decl)) {
    if (TREE_CODE(type) == METHOD_TYPE) {
      tree base_type = TYPE_METHOD_BASETYPE(type);
      XIL_Type xil_base_type = XIL_TranslateType(base_type);
      const char *this_csu = XIL_GetTypeCSUName(xil_base_type);
      xil_type = XIL_TypeFunction(XIL_TypeVoid(), this_csu, false, NULL, 0);
    }
    else {
      TREE_UNEXPECTED(decl);
    }
  }

  // don't deal with extern functions/globals. we will see the definition later
  // (hopefully!), including the complete type for arrays and any initializer.
  // we still want to process the type for these in case anonymous types are
  // being used.
  if (DECL_EXTERNAL(decl))
    return;

  // parse the annotation kind.
  XIL_AnnotationKind use_kind = 0;
  if (annotation_kind) {
#define XIL_TEST_ANNOT(_, STR, VALUE)                           \
    if (!strcmp(annotation_kind, STR)) use_kind = VALUE;
  XIL_ITERATE_ANNOT(XIL_TEST_ANNOT)
#undef XIL_TEST_ANNOT
    gcc_assert(use_kind);
  }

  const char *name = XIL_GetVarName(xil_var);

  xil_active_env.decl = decl;
  xil_active_env.decl_name = name;
  XIL_SetActiveBlock(xil_var, annotation_name, use_kind, annot_type);

  const char *decl_file = DECL_SOURCE_FILE(decl);
  int decl_line = DECL_SOURCE_LINE(decl);

  // get the begin file/line for a function definition. this is somewhat
  // trickier than might be expected. the decl's location sometimes comes from
  // a header file and not the definition we are interested in, while the
  // result variable's location corresponds to the ')' for the function,
  // not the function symbol which we want. solution: use the decl's location
  // unless it looks like it came from a declaration (in a different file
  // than the result, or many lines earlier).

  if (TREE_CODE(decl) == FUNCTION_DECL) {
    tree result = DECL_RESULT(decl);
    if (result) {
      const char *res_decl_file = DECL_SOURCE_FILE(result);
      int res_decl_line = DECL_SOURCE_LINE(result);

      if (strcmp(decl_file, res_decl_file) ||
          res_decl_line > decl_line + 10) {
        decl_file = res_decl_file;
        decl_line = res_decl_line;
      }
    }
  }

  XIL_Location begin_loc = XIL_MakeLocation(decl_file, decl_line);

  // get the end file/line from the parser's current position, unless the
  // parser has no current position.
  const char *end_file = input_filename;
  int end_line = input_line;
  if (!input_filename) {
    end_file = decl_file;
    end_line = decl_line;
  }

  // the begin/end points of the declaration should be in the same file.
  if (strcmp(decl_file, end_file))
    TREE_UNEXPECTED(decl);

  XIL_Location end_loc = XIL_MakeLocation(end_file, end_line);

  XIL_CFGSetCommand(xil_command);

  XIL_CFGSetBeginLocation(begin_loc);
  XIL_CFGSetEndLocation(end_loc);

  xil_active_env.entry_point = xil_active_env.last_point = XIL_CFGAddPoint(begin_loc);
  xil_active_env.exit_point = XIL_CFGAddPoint(end_loc);
  XIL_CFGSetEntryPoint(xil_active_env.entry_point);
  XIL_CFGSetExitPoint(xil_active_env.exit_point);

  // add the decl variable to the active CFG. override any previous type we
  // had for the variable, to account for seeing multiple definitions of
  // a variable, which gcc allows, e.g. int buf[]; int buf[10];
  if (!xil_has_annotation)
    XIL_CFGAddVar(xil_var, xil_type, 1);

  // current point for traversal of the function/initializer.
  XIL_PPoint point = xil_active_env.entry_point;

  bool is_function = (TREE_CODE(decl) == FUNCTION_DECL);

  if (is_function) {
    // handling for function definitions.
    tree defn = DECL_SAVED_TREE(decl);

    // add the parameters to the active CFG. skip this for destructors
    // to avoid the __in_chrg argument.
    if (!XIL_IsDestructor(decl)) {
      tree param = DECL_ARGUMENTS(decl);
      while (param) {
        gcc_assert(TREE_CODE(param) == PARM_DECL);
        XIL_TranslateVar(param);  // forces insertion of the parameter.
        param = TREE_CHAIN(param);
      }
    }

    // generate edges for the function body.
    XIL_ActivePushScope();
    MAKE_ENV(body_env, &point, NULL);
    XIL_TranslateTree(&body_env, defn);
    XIL_ActivePopScope();
  }
  else {
    // handling for global variables.
    tree initial = DECL_INITIAL(decl);

    // make an assignment for any initializer. for compound initializers
    // this may get fairly involved.
    if (initial) {
      MAKE_ENV(initial_env, &point, NULL);
      initial_env.result_assign = XIL_ExpVar(xil_var);
      initial_env.result_assign_type = xil_type;
      XIL_TranslateTree(&initial_env, initial);
    }
  }

  // connect any fall through to the exit point.
  XIL_CFGEdgeSkip(point, xil_active_env.exit_point);

  // for debugging, bail out of compilation at the first error.
  //if (xil_active_env.dropped) {
  //  printf("XIL: Bailing out\n");
  //  exit(1);
  //}

  // process any annotations read in from file for the function,
  // now that we know all locals.
  int count = XIL_GetAnnotationCount(name, !is_function, false);
  int ind = 0;
  for (; ind < count; ind++) {
    const char *where;
    const char *point_text, *annot_text;
    int trusted;
    XIL_GetAnnotation(name, !is_function, false, ind, &where,
                      &point_text, &annot_text, &trusted);
    XIL_ProcessAnnotationRead(decl, where, point_text, annot_text, trusted);
  }

  // process annotations discovered for CSU types.
  while (xil_active_env.annots) {
    struct XIL_PendingAnnotation *annot = xil_active_env.annots;
    xil_active_env.annots = annot->next;
    XIL_ProcessAnnotationAttr(annot->type, annot->attr, NULL, NULL);
  }

  XIL_ClearActiveBlock(xil_active_env.dropped);
  XIL_ClearAssociate(XIL_AscBlock);

  memset(&xil_active_env, 0, sizeof(struct XIL_BlockEnv));
}

// gcc plugin functions

// additional settings we get from plugin arguments.
static const char *normalize_directory = NULL;
static const char *log_file = NULL;
static const char *annotation_file = NULL;

void gcc_plugin_start_unit(void *gcc_data, void *user_data)
{
  if (log_file) {
    xil_log = fopen(log_file, "a");
    gcc_assert(xil_log);

    XIL_SetLogFile(xil_log);

    // figure out the directory containing the log. this will be used for
    // making temporary files (i.e. annotation files).
    char *log_dir = xstrdup(log_file);
    char *pos = log_dir;
    while (true) {
      char *slash_pos = strchr(pos + 1, '/');
      if (!slash_pos) {
        *pos = 0;
        break;
      }
      pos = slash_pos;
    }
    if (pos != log_dir)
      xil_log_directory = log_dir;
  }
  else {
    xil_log = stdout;
  }

  XIL_SetupGenerate(xil_remote_address);
  XIL_SetNormalizeDirectory(normalize_directory);

  if (annotation_file)
    XIL_ReadAnnotationFile(annotation_file);

  // compute the width of pointers on this target.
  addr_space_t as = ADDR_SPACE_GENERIC;
  enum machine_mode mode = targetm.addr_space.pointer_mode (as);
  tree size = size_int (GET_MODE_SIZE (mode));
  xil_pointer_width = TREE_UINT(size);
}

// handler to pick up the attribute indicating the name of the annotation
// whose CFG is being generated. we can't pass this at the command line as
// the name may include characters the gcc argument parser doesn't like.
tree annotation_name_handler(tree *node, tree name, tree args,
                             int flags, bool *no_add_attrs)
{
  gcc_assert(TREE_CODE(args) == TREE_LIST);
  tree value = TREE_VALUE(args);
  gcc_assert(TREE_CODE(value) == STRING_CST);

  annotation_name = TREE_STRING_POINTER(value);
  return NULL;
}

// XXX disabled for plugin compilation with CXX
#if 0

static struct attribute_spec annotation_name_attribute = {
  .name = "annot_name",
  .min_length = 1,
  .max_length = 1,
  .handler = annotation_name_handler
};

// handler to pick up the tree for the 'this' CSU type.
tree annotation_this_handler(tree *node, tree name, tree args,
                             int flags, bool *no_add_attrs)
{
  gcc_assert(!xil_annotation_this);
  xil_annotation_this = *node;
  return NULL;
}

static struct attribute_spec annotation_this_attribute = {
  .name = "annot_this",
  .min_length = 0,
  .max_length = 0,
  .handler = annotation_this_handler
};

static struct attribute_spec annotation_this_var_attribute = {
  .name = "annot_this_var",
  .min_length = 1,
  .max_length = 1
};

// attribute attached to global functions/variables, indicating the full name.
static struct attribute_spec annotation_global_attribute = {
  .name = "annot_global",
  .min_length = 1,
  .max_length = 1
};

// attribute attached to parameters, indicating the parameter index.
static struct attribute_spec annotation_param_attribute = {
  .name = "annot_param",
  .min_length = 1,
  .max_length = 1
};

// attribute attached to return variables.
static struct attribute_spec annotation_return_attribute = {
  .name = "annot_return",
  .min_length = 0,
  .max_length = 0
};

// attribute attached to local variables, indicating the actual name
// (which is the same as the declared name except in case of duplicates).
static struct attribute_spec annotation_local_attribute = {
  .name = "annot_local",
  .min_length = 1,
  .max_length = 1
};

// optional attribute attached to any of the above variables,
// indicating the source name of the variable.
static struct attribute_spec annotation_source_attribute = {
  .name = "annot_source",
  .min_length = 1,
  .max_length = 1
};

void gcc_plugin_attributes(void *gcc_data, void *user_data)
{
#define XIL_MAKE_ATTR(NAME, STR, _)                     \
  static struct attribute_spec NAME ## _attribute = {   \
    .name = STR,                                        \
    .min_length = 1,                                    \
    .max_length = 1                                     \
  };                                                    \
  register_attribute(&(NAME ## _attribute));

  XIL_ITERATE_ANNOT(XIL_MAKE_ATTR)
#undef XIL_MAKE_ATTR

  // attributes used in the files emitted during annotation processing.
  register_attribute(&annotation_name_attribute);
  register_attribute(&annotation_this_attribute);
  register_attribute(&annotation_this_var_attribute);
  register_attribute(&annotation_global_attribute);
  register_attribute(&annotation_param_attribute);
  register_attribute(&annotation_return_attribute);
  register_attribute(&annotation_local_attribute);
  register_attribute(&annotation_source_attribute);
}

#else

void gcc_plugin_attributes(void *gcc_data, void *user_data)
{}

#endif

void gcc_plugin_pre_genericize(void *gcc_data, void *user_data)
{
  tree decl = (tree) gcc_data;

  // check for __base_ctor/__comp_ctor fake constructors. these correspond
  // directly to another constructor for the type, and we will replace
  // references to these with references to that other constructor.
  // we will see the other constructor first, and its TREE_CHAINs will
  // have the __base_ctor and __comp_ctor.
  tree chain = TREE_CHAIN(decl);
  if (chain && TREE_CODE(chain) == FUNCTION_DECL) {
    const char *chain_name = IDENTIFIER_POINTER(DECL_NAME(chain));
    if (!strncmp(chain_name,"__base_ctor",11) ||
        !strncmp(chain_name,"__base_dtor",11)) {
      bool *skip_info = (bool*) XIL_Associate(XIL_AscGlobal, "func_skip",chain);
      *skip_info = true;

      chain = TREE_CHAIN(chain);
      if (chain && TREE_CODE(chain) == FUNCTION_DECL) {
        const char *chain_name = IDENTIFIER_POINTER(DECL_NAME(chain));
        if (!strncmp(chain_name,"__comp_ctor",11) ||
            !strncmp(chain_name,"__comp_dtor",11)) {
          skip_info = (bool*) XIL_Associate(XIL_AscGlobal, "func_skip",chain);
          *skip_info = true;
        }
      }
    }
  }

  // if this is the __base_ctor or __comp_ctor, skip it.
  bool *skip_info = (bool*) XIL_Associate(XIL_AscGlobal, "func_skip",decl);
  if (*skip_info)
    return;

  // check for annotations on this function.
  tree attr = DECL_ATTRIBUTES(decl);
  while (attr) {
    XIL_ProcessAnnotationAttr(decl, attr, NULL, NULL);
    attr = TREE_CHAIN(attr);
  }

  XIL_GenerateBlock(decl);

  // future parameter declarations will be for a different function.
  xil_pending_param_decls = NULL;
}

void gcc_plugin_finish_decl(void *gcc_data, void *user_data)
{
  tree decl = (tree) gcc_data;
  tree type = TREE_TYPE(decl);

  // push this onto the pending parameters if necessary.
  if (TREE_CODE(decl) == PARM_DECL) {
    // we should only see parameter declarations for C.
    gcc_assert(!c_dialect_cxx());

    struct XIL_ParamDecl *last = xil_pending_param_decls;
    while (last && last->next) last = last->next;

    struct XIL_ParamDecl *param_decl = xcalloc(1, sizeof(struct XIL_ParamDecl));
    param_decl->decl = decl;
    if (last) last->next = param_decl;
    else xil_pending_param_decls = param_decl;

    return;
  }

  // check for typedefs on structures, and assign the structure a name
  // if one is found.
  if (TREE_CODE(decl) == TYPE_DECL &&
      (TREE_CODE(type) == RECORD_TYPE || TREE_CODE(type) == UNION_TYPE)) {
    if (XIL_IsAnonymous(type)) {
      const char *name = IDENTIFIER_POINTER(DECL_NAME(decl));
      XIL_CSUName(type, name);
    }
  }

  // check for a global variable.
  bool is_global = false;

  if (TREE_CODE(decl) == VAR_DECL) {
    if (DECL_CONTEXT(decl) == NULL)
      is_global = true;
    if (TREE_STATIC(decl))
      is_global = true;
  }

  bool is_function = (TREE_CODE(decl) == FUNCTION_DECL);

  if (!is_global && !is_function)
    return;

  // only processing the output function for annotations.
  if (xil_has_annotation)
    return;

  XIL_Var var = XIL_TranslateVar(decl);
  const char *name = XIL_GetVarName(var);

  // future parameter declarations will be for a different function.
  xil_pending_param_decls = NULL;

  if (!is_global)
    return;

  // check if this is a global variable we want to skip. these are introduced
  // for type information globals.
  static const char *bad_prefix_list[] = {
    "const __class_type_info_pseudo",
    "const __si_class_type_info_pseudo",
    "const __vmi_class_type_info_pseudo",
    "const char _ZTS",
    NULL
  };
  int ind;
  for (ind = 0; bad_prefix_list[ind]; ind++) {
    const char *bad_prefix = bad_prefix_list[ind];
    if (!strncmp(name, bad_prefix, strlen(bad_prefix)))
      return;
  }

  // if the decl is contained in a template class then skip it. we can only
  // handle instantiated declarations, and will only see the uninstantiated
  // declarations here. TODO: is there a way to get these?
  if (DECL_LANG_SPECIFIC(decl) != NULL &&
      DECL_TEMPLATE_INFO(decl) != NULL)
    return;
  tree context = DECL_CONTEXT(decl);
  while (context && TREE_CODE(context) == FUNCTION_DECL) {
    if (DECL_LANG_SPECIFIC(context) != NULL &&
        DECL_TEMPLATE_INFO(context) != NULL)
      return;
    context = DECL_CONTEXT(context);
  }

  // this is a function or global, process any annotation attributes.
  tree attr = DECL_ATTRIBUTES(decl);
  while (attr) {
    XIL_ProcessAnnotationAttr(decl, attr, NULL, NULL);
    attr = TREE_CHAIN(attr);
  }

  // also look for annotations read in from file.
  for (ind = 0; ind < XIL_GetAnnotationCount(name, !is_function, false); ind++) {
    const char *where;
    const char *point_text, *annot_text;
    int trusted;
    XIL_GetAnnotation(name, !is_function, false, ind, &where,
                      &point_text, &annot_text, &trusted);

    // we'll handle loop invariants and point assertions after seeing the
    // function's definition.
    if (!strncmp(where, "loop", 4) || point_text)
      continue;

    XIL_ProcessAnnotationRead(decl, where, point_text, annot_text, trusted);
  }

  XIL_GenerateBlock(decl);
}

void gcc_plugin_finish_type(void *gcc_data, void *user_data)
{
  tree type = (tree) gcc_data;
  if (TREE_CODE(type) == ERROR_MARK) return;

  tree idnode = TYPE_NAME(type);

  // if the structure was declared with an explicit name then assign it that.
  if (idnode && TREE_CODE(idnode) == IDENTIFIER_NODE) {
    const char *name = IDENTIFIER_POINTER(idnode);
    XIL_CSUName(type, name);
  }

  // for C++ we check the type for a TYPE_DECL name within XIL_CSUName.
  // force this check now so that we don't get confused by any later typedefs.
  if (c_dialect_cxx())
    XIL_CSUName(type, NULL);
}

void gcc_plugin_finish_unit(void *gcc_data, void *user_data)
{
  // XIL_PrintGenerated();
  XIL_WriteGenerated();

  if (log_file) {
    gcc_assert(xil_log != stdout);
    fclose(xil_log);
  }
}

// let GCC know this plugin has a GPL-compatible license.
int plugin_is_GPL_compatible;

int plugin_init (struct plugin_name_args *plugin_info,
                 struct plugin_gcc_version *version)
{
  xil_plugin_path = plugin_info->full_name;

  // check the environment for the command used to invoke gcc. we can't pass
  // this as a plugin argument as the command line may include '=' and
  // use both single and double quotes.
  xil_command = getenv("XGILL_COMMAND");
  if (!xil_command)
    xil_command = "UNKNOWN";

  // process any plugin arguments.
  int arg_ind;
  for (arg_ind = 0; arg_ind < plugin_info->argc; arg_ind++) {
    char *arg_key = plugin_info->argv[arg_ind].key;
    char *arg_value = plugin_info->argv[arg_ind].value;

    if (!strcmp(arg_key,"gcc")) {
      if (arg_value)
        xil_gcc_path = arg_value;
      else
        printf("WARNING: xgill argument 'gcc' requires value\n");
    }
    else if (!strcmp(arg_key,"log")) {
      if (arg_value)
        log_file = arg_value;
      else
        printf("WARNING: xgill argument 'log' requires value\n");
    }
    else if (!strcmp(arg_key,"remote")) {
      if (arg_value)
        xil_remote_address = arg_value;
      else
        printf("WARNING: xgill argument 'remote' requires value\n");
    }
    else if (!strcmp(arg_key,"basedir")) {
      if (arg_value)
        normalize_directory = arg_value;
      else
        printf("WARNING: xgill argument 'basedir' requires value\n");
    }
    else if (!strcmp(arg_key,"annfile")) {
      if (arg_value)
        annotation_file = arg_value;
      else
        printf("WARNING: xgill argument 'annfile' requires value\n");
    }
    else if (!strcmp(arg_key,"annsingle")) {
      if (arg_value)
        xil_annotation_single = arg_value;
      else
        printf("WARNING: xgill argument 'annsingle' requires value\n");
      XIL_ForceAnnotationWrites();
    }
    else if (!strcmp(arg_key,"annot")) {
      if (arg_value) {
        // the annot argument should have the format class:kind
        char *new_arg = xstrdup(arg_value);
        annotation_class = new_arg;

        char *colon = strchr(new_arg, ':');
        if (colon) {
          *colon = 0;
          annotation_kind = colon + 1;
        }

        xil_has_annotation = true;
      }
      else {
        printf("WARNING: xgill argument 'annot' requires value\n");
      }
    }
    else {
      printf("WARNING: xgill unrecognized argument %s\n", arg_key);
    }
  }

  register_callback (plugin_info->base_name, PLUGIN_START_UNIT,
                     gcc_plugin_start_unit, NULL);
  register_callback (plugin_info->base_name, PLUGIN_ATTRIBUTES,
                     gcc_plugin_attributes, NULL);
  register_callback (plugin_info->base_name, PLUGIN_PRE_GENERICIZE, 
                     gcc_plugin_pre_genericize, NULL);
  register_callback (plugin_info->base_name, PLUGIN_FINISH_DECL,
                     gcc_plugin_finish_decl, NULL);
  register_callback (plugin_info->base_name, PLUGIN_FINISH_TYPE,
                     gcc_plugin_finish_type, NULL);
  register_callback (plugin_info->base_name, PLUGIN_FINISH_UNIT,
                     gcc_plugin_finish_unit, NULL);

  return 0;
}
