
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
#include <cp/cp-tree.h>

bool XIL_IsDestructor(tree decl)
{
  if (!c_dialect_cxx())
    return false;

  // somewhat crude, look for functions whose full name includes a '::~'
  if (TREE_CODE(decl) != FUNCTION_DECL)
    return false;
  int flags = TFF_DECL_SPECIFIERS;

  const char *name = decl_as_string(decl, flags);
  const char *tilde = strchr(name, '~');

  if (tilde && tilde >= name + 2) {
    if (*(tilde-1) == ':' && *(tilde-2) == ':')
      return true;
  }
  return false;
}

const char* XIL_GlobalName(tree decl)
{
  // if there is an annot_global then it has the global name.
  tree attr = DECL_ATTRIBUTES(decl);
  while (attr) {
    const char *full_name = NULL;
    const char *purpose = XIL_DecodeAttribute(attr, &full_name, NULL);

    if (purpose && !strcmp(purpose, "annot_global") && full_name)
      return full_name;
    attr = TREE_CHAIN(attr);
  }

  // there are several cases we need to consider in constructing decl's name.
  // 1. globals in C
  //    use the variable's name, this must be unique.
  // 2. globals in C++
  //    use the fully decorated name to account for overloading, namespaces,
  //    templates, etc. would be better to use the mangled name but mangling
  //    seems to be a separate module in g++.
  // 3. globals in C++ with C linkage
  //    use the variable's name as in C, so that C++ code can call
  //    C functions vice versa.
  // 4. static globals. use the name as above but prefix with the filename.
  // 5. static locals. prefix with the function's name as above.

  const char *name = IDENTIFIER_POINTER(DECL_NAME(decl));
  if (c_dialect_cxx() && !DECL_EXTERN_C_P(decl)) {
    int old_generate_record_types = xil_generate_record_types;
    xil_generate_record_types = 0;
    XIL_Type xil_type = XIL_TranslateType(TREE_TYPE(decl));
    xil_generate_record_types = old_generate_record_types;

    name = decl_as_string(decl, TFF_DECL_SPECIFIERS);
    name = XIL_MaybeDecorateFunction(name, xil_type);
  }

  // if the variable has a function context then prepend with the name
  // of the function variable. (static local variables).
  tree context = DECL_CONTEXT(decl);
  if (context && TREE_CODE(context) == FUNCTION_DECL) {
    const char *func_name = XIL_GlobalName(context);
    char *new_name = xmalloc(strlen(func_name) + strlen(name) + 2);
    sprintf(new_name, "%s:%s", func_name, name);
    return new_name;
  }

  // the variable has the 'static' keyword if it is not TREE_PUBLIC.
  // (TREE_STATIC only implies the decl has static non-stack storage, not that
  // it was declared with 'static').
  if (!TREE_PUBLIC(decl)) {
    // get the filename (excluding directories) of the source file.
    const char *file = DECL_SOURCE_FILE(decl);
    while (strchr(file, '/') != NULL)
      file = strchr(file, '/') + 1;

    char *new_name = xmalloc(strlen(file) + strlen(name) + 2);
    sprintf(new_name, "%s:%s", file, name);
    return new_name;
  }

  return name;
}

const char* XIL_SourceName(tree decl)
{
  // if there is an annot_source then it has the global name.
  tree attr = DECL_ATTRIBUTES(decl);
  while (attr) {
    const char *name = NULL;
    const char *purpose = XIL_DecodeAttribute(attr, &name, NULL);

    if (purpose && !strcmp(purpose, "annot_source") && name)
      return name;
    attr = TREE_CHAIN(attr);
  }

  // if the declaration has an explicit name then use that.
  tree idnode = DECL_NAME(decl);
  if (idnode) {
    TREE_CHECK(idnode, IDENTIFIER_NODE);
    return IDENTIFIER_POINTER(idnode);
  }

  // no name otherwise.
  return NULL;
}

// name might be NULL.
XIL_Var XIL_TranslateParam(tree param_decl, const char *name)
{
  // figure out the index into the parameters list of this parameter.
  int param_index = 0;

  tree func_decl = DECL_CONTEXT(param_decl);
  TREE_CHECK(func_decl, FUNCTION_DECL);

  gcc_assert(func_decl && func_decl == xil_active_env.decl);

  tree chk_param = DECL_ARGUMENTS(func_decl);
  while (chk_param) {
    TREE_CHECK(chk_param, PARM_DECL);

    if (chk_param == param_decl) {
      // found the parameter we want.
      break;
    }

    chk_param = TREE_CHAIN(chk_param);
    param_index++;
  }

  // should have found it and have the right index.
  gcc_assert(chk_param == param_decl);

  // for method types, the first parameter is the 'this' variable and the
  // remaining parameters need to be adjusted by one.
  if (TREE_CODE(TREE_TYPE(func_decl)) == METHOD_TYPE) {
    if (param_index == 0)
      return XIL_VarThis(false);
    param_index--;
  }

  if (!name) {
    name = xmalloc(10);
    sprintf((char*)name, "__arg%d", param_index);
  }

  return XIL_VarArg(param_index, name, false);
}

XIL_Var generate_TranslateVar(tree decl)
{
  static XIL_Var error_var = NULL;
  if (!error_var) error_var = XIL_VarGlob("error", "error");

  const char *name = XIL_SourceName(decl);
  tree type = TREE_TYPE(decl);

  // store here for function-scope variables and we'll add its type
  // to the enclosing CFG.
  XIL_Var xil_decl = NULL;

  switch (TREE_CODE(decl)) {

  case FUNCTION_DECL: {
    const char *full_name = XIL_GlobalName(decl);

    // for functions, change out the name for __base_ctor/__comp_ctor and dtor.
    // fortunately these have the same full name and type as the variable we
    // will replace them with, so just fixup the source name.
    if (!strncmp(name,"__base_ctor",11) || !strncmp(name,"__comp_ctor",11) ||
        !strncmp(name,"__base_dtor",11) || !strncmp(name,"__comp_dtor",11)) {
      // these all share the same structure name (will add the '~' for dtor
      // below). get the name of the structure and strip off any namespace
      // or template info.

      TREE_CHECK(type, METHOD_TYPE);
      tree base_type = TYPE_METHOD_BASETYPE(type);
      XIL_Type xil_base_type = XIL_TranslateType(base_type);
      char *new_name = xstrdup(XIL_GetTypeCSUName(xil_base_type));

      char *pos = strchr(new_name,' ');
      if (pos) new_name = pos + 1;
      while (strchr(new_name,':') != NULL)
        new_name = strchr(new_name,':') + 1;
      pos = strchr(new_name,'<');
      if (pos) *pos = 0;
      name = new_name;
    }

    // the source name for destructors does not include the '~'. add it here.
    if (XIL_IsDestructor(decl)) {
      char *new_name = xmalloc(strlen(name) + 2);
      *new_name = '~';
      strcpy(new_name + 1, name);
      name = new_name;
    }

    return XIL_VarFunc(full_name, name);
  }

  case PARM_DECL: {
    xil_decl = XIL_TranslateParam(decl, name);
    break;
  }

  case VAR_DECL: {
    if (!name) {
      // treat unnamed variables as temporaries. these are introduced by GCC
      // in some cases such as compound expressions ({ s1; s2; value; }).
      // TODO: should check later that these really are temporaries, e.g.
      // aren't live across loop boundaries.

      // we will associate an XIL var with each anonymous variable.
      XIL_Var *var_temp =
        (XIL_Var*) XIL_Associate(XIL_AscBlock, "TempVar", decl);

      if (!*var_temp) {
        // watch out for temporaries with anonymous types and try to assign
        // a name to them. use the index of the temporary.
        if (XIL_IsAnonymous(type)) {
          char *anon_name = xmalloc(strlen(xil_active_env.decl_name) + 100);
          sprintf(anon_name, "%s:__temp_%d",
                  xil_active_env.decl_name, xil_active_env.temp_count + 1);
          XIL_CSUName(type, anon_name);
        }

        XIL_Type xil_type = XIL_TranslateType(type);
        *var_temp = XIL_NewTemporary(xil_type);
      }

      // NewTemporary added its result to the CFG, we're done.
      return *var_temp;
    }

    // check for special annotation attributes if this is a param/local/etc.
    // in the function being annotated. don't add types in these cases,
    // the variable does not actually belong to the active block.
    tree attr = DECL_ATTRIBUTES(decl);
    while (attr) {
      const char *text_value = NULL;
      int int_value = 0;
      const char *purpose = XIL_DecodeAttribute(attr, &text_value, &int_value);

      if (purpose && !strcmp(purpose, "annot_param"))
        return XIL_VarArg(int_value, name, true);
      if (purpose && !strcmp(purpose, "annot_return"))
        return XIL_VarReturn(true);
      if (purpose && !strcmp(purpose, "annot_local") && text_value)
        return XIL_VarLocal(text_value, name, true);

      if (purpose && !strcmp(purpose, "annot_this_var")) {
        // should have already found and filtered these.
        XIL_PrintStack();
        gcc_unreachable();
      }

      attr = TREE_CHAIN(attr);
    }

    const char *full_name = NULL;

    // figure out whether this is a local.
    bool is_global = false;

    tree context = DECL_CONTEXT(decl);
    if (context && !TREE_STATIC(decl) &&
        TREE_CODE(context) != TRANSLATION_UNIT_DECL) {
      if (context == xil_active_env.decl) {
        // local variable.
        full_name = name;
      }
      else if (!xil_active_env.decl) {
        // not inside a block, we must be checking whether this is a global
        // variable we want to analyze. treat as a local.
        full_name = name;
      }
      else if (TREE_CODE(context) == NAMESPACE_DECL) {
        // usually things defined in a namespace do not have that namespace
        // for a context. sometimes they do. TODO: figure out why this is.
        is_global = true;
        full_name = XIL_GlobalName(decl);
      }
      else {
        TREE_UNEXPECTED(decl);
        return error_var;
      }
    }
    else {
      // global variable.
      is_global = true;
      full_name = XIL_GlobalName(decl);
    }

    gcc_assert(full_name);

    // if the variable's type is an anonymous structure, give the structure
    // a name based on the variable.
    if (XIL_IsAnonymous(type)) {
      const char *anon_name = NULL;
      if (is_global) {
        anon_name = full_name;
      }
      else {
        // use 'function:name' since the structure's name must be
        // globally unique.
        anon_name = xmalloc(strlen(xil_active_env.decl_name) +
			    strlen(full_name) + 2);
        sprintf((char*)anon_name, "%s:%s",
                xil_active_env.decl_name, full_name);
      }

      XIL_CSUName(type, anon_name);
    }

    if (is_global) {
      return XIL_VarGlob(full_name, name);
    }
    else {
      // need to watch for different local variables in a function which share
      // the same name. unique the name by adding ':ind'.
      struct XIL_LocalData *local = xil_active_env.locals;
      int index = 0;
      while (local) {
        if (local->decl == decl)
          return local->var;

        tree oidnode = DECL_NAME(local->decl);
        const char *oname = IDENTIFIER_POINTER(oidnode);
        if (!strcmp(name, oname))
          index++;

        local = local->block_next;
      }

      if (index) {
        char *new_name = xmalloc(strlen(name) + 10);
        sprintf(new_name, "%s:%d", name, index);
        xil_decl = XIL_VarLocal(new_name, name, false);
      }
      else {
        xil_decl = XIL_VarLocal(name, name, false);
      }

      local = xmalloc(sizeof(struct XIL_LocalData));
      memset(local, 0, sizeof(struct XIL_LocalData));
      local->decl = decl;
      local->var = xil_decl;
      local->block_next = xil_active_env.locals;
      xil_active_env.locals = local;
    }
    break;
  }

  case RESULT_DECL:
    xil_decl = XIL_VarReturn(false);
    break;

  default:
    TREE_UNEXPECTED(decl);
    return error_var;
  }

  gcc_assert(xil_decl);

  // this should be in the scope for the function we are processing.
  gcc_assert(DECL_CONTEXT(decl) == xil_active_env.decl);

  XIL_Type xil_type = XIL_TranslateType(type);

  XIL_CFGAddVar(xil_decl, xil_type, 0);
  return xil_decl;
}
