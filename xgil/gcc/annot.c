
#include "xgill.h"
#include <c-family/c-pragma.h>
#include <cpplib.h>
#include <cp/cp-tree.h>

// annotation file overview. we get the annotations as raw strings and need
// to parse them in the context where they appeared in the source. we do this
// by constructing an annotation file containing the annotation string and
// all declarations and definitions from the program which might be relevant
// to the annotation. we'll then ask gcc to parse the file we constructed,
// and recover the syntax for the annotation from that parse.

// here we keep track of what information needs to go in the annotation file,
// and the order in which that information should be added. the general order:
// - macro definitions.
// - enum definitions.
// - struct/typedef/fnptr declarations. these have an order.
// - struct definitions. these have an order.
// - function and variable declarations.
// - the annotation function.
// below are structures storing this information and the order to emit it.

// information about a macro definition to insert.

struct XIL_AnnotationMacro
{
  // macro to define. this is everything except the leading '#define'.
  const char *macro;

  struct XIL_AnnotationMacro *next;
};

// information about a name to declare. we want to flatten out the
// definitions of structures, enums and typedefs, while retaining the original
// names from the program so that they can be referred to in annotations.

// for any struct/enum/typedef name we encounter in the program, there are
// severalx possibilities.
// 1. the name is in global scope. declare, define and refer to the name as is.
// 2. the name is in a namespace. wrap the declare/define in namespace { ... }
//    qualifiers and refer to it via the explicit namespace path.
// 3. the name is nested in a structure. make an artificial __innerN name
//    and declare, define and refer to the name with this artificial name.
//    define the outer structure and add a typedef to it for this artificial
//    name so that annotations can refer to it.
// 4. the name is a template instantiation. make an artificial __templateN
//    name to declare/define/refer to it. don't do anything else, annotations
//    can't yet use template instantiations explicitly.
// 5. the name is for a type we are annotating an invariant on.

// declarations must be ordered such that if one declaration depends on another
// (i.e. from a typedef), the other declaration appears first.

struct XIL_AnnotationDecl
{
  // type declaration this is declaring. this may be a structure, enum
  // or typedef. note that types which have names but not type declarations
  // (i.e. 'struct foo' in C) will not have one of these structures,
  // and will have their names printed as is.
  tree decl;

  // function pointer type to introduce a new typedef for. this may be
  // specified instead of decl. we also include method types here,
  // though their typedef will look like a regular function and they
  // can't be called from annotations.
  tree fnptr;

  // name to print when referring to this declaration. for types in a namespace
  // this does not include any namespace qualifiers.
  const char *name;

  // whether name is artificial (__innerN or __templateN). namespace qualifiers
  // are not printed when referring to this declaration.
  bool artificial;

  struct XIL_AnnotationDecl *next;
};

// information about a structure or enum to define. definitions must be
// ordered such that if one definition depends on another (it contains the
// other in a field, say), the other definition appears first.

struct XIL_AnnotationDef
{
  // type being defined.
  tree type;

  // whether to add an explicit top level definition for this type.
  // types which do not get explicit definitions include inner types
  // (they will be defined when the outer type is) and anonymous types;
  // in this case this structure indicates that it is OK to define the type.
  bool define;

  struct XIL_AnnotationDef *next;
};

// information about a structure to give an empty definition. this is a hack
// to get around the 'dereferencing pointer to incomplete type' errors
// which gcc emits but doesn't indicate the type being dereferenced.
// instead we'll emit empty types and watch out for 'has no member' errors.
// this is only an issue with the C frontend. TODO: this hack breaks sizeof
// handling and this should really be fixed within gcc itself.

struct XIL_AnnotationEmptyDef
{
  // type being given an empty definition.
  tree type;

  struct XIL_AnnotationEmptyDef *next;
};

// information about a function or variable to declare.

struct XIL_AnnotationVar
{
  // function or variable to declare.
  tree decl;

  struct XIL_AnnotationVar *next;
};

// information about a namespace to use.

struct XIL_AnnotationNamespace
{
  // namespace context for 'using'.
  tree context;

  struct XIL_AnnotationNamespace *next;
};

// all state for processing an annotation.

struct XIL_AnnotationState
{
  // previous state in active stack. annotations are reentrant as we force
  // translation of types referred to, which may discover new invariants.
  struct XIL_AnnotationState *prev;

  // function/global declaration the annotation is attached to.
  tree decl;

  // CSU type the annotation is attached to. for annotations on methods both
  // this and decl will be specified.
  tree type;

  // NULL-terminated array of local variables to add to the generated file.
  struct XIL_LocalData **locals;

  // name of the annotation.
  const char *name;

  // text of the annotation.
  const char *text;

  // all declarations and definitions to add to the annotation file.
  struct XIL_AnnotationMacro *macros;
  struct XIL_AnnotationDecl *decls;
  struct XIL_AnnotationDef *defs;
  struct XIL_AnnotationEmptyDef *emptydefs;
  struct XIL_AnnotationVar *vars;
  struct XIL_AnnotationNamespace *namespaces;

  // number of artificial names that have been declared.
  int artificial_count;
};

// the active annotation state.
static struct XIL_AnnotationState *state = NULL;

// whether a type needs a top-level declaration. this includes any non-anonymous
// type as well as the 'this' type for invariants on anonymous types.
static inline bool TypeNeedsDecl(tree type)
{
  tree name = TYPE_NAME(type);
  if (name && TREE_CODE(name) == TYPE_DECL) {
    if (!XIL_IsAnonymousCxx(name))
      return true;
    if (state->type && TREE_CODE(type) == TREE_CODE(state->type))
      return TYPE_FIELDS(state->type) == TYPE_FIELDS(type);
  }
  return false;
}

// makes a declaration and appends it to the end of the state.
// ignores duplicate additions.
static void XIL_AddDecl(tree decl)
{
  gcc_assert(decl);

  // check to make sure this is not a duplicate addition.
  struct XIL_AnnotationDecl *last = state->decls;
  while (last) {
    if (last->decl == decl) return;
    if (!last->next) break;
    last = last->next;
  }

  // compute the name to use for this declaration.
  const char *name = NULL;
  bool artificial = false;

  // if decl is anonymous, we are handling the 'this' type.
  if (c_dialect_cxx() && XIL_IsAnonymousCxx(decl)) {
    name = "__anonymous_this";
    artificial = true;
  }

  // make an artificial name for declarations inside a structure.
  if (!name && c_dialect_cxx() && DECL_CONTEXT(decl) &&
      TREE_CODE(DECL_CONTEXT(decl)) != NAMESPACE_DECL) {
    name = xmalloc(30); artificial = true;
    sprintf((char*)name, "__inner%d", ++state->artificial_count);
  }

  // make an artificial name for template instantiations.
  tree type = TREE_TYPE(decl);
  if (!name && c_dialect_cxx() &&
      (TREE_CODE(type) == RECORD_TYPE || TREE_CODE(type) == UNION_TYPE) &&
      CLASSTYPE_USE_TEMPLATE(TREE_TYPE(decl))) {
    name = xmalloc(30); artificial = true;
    sprintf((char*)name, "__template%d", ++state->artificial_count);
  }

  // otherwise use the name of the declaration itself.
  if (!name) {
    gcc_assert(DECL_NAME(decl));
    name = IDENTIFIER_POINTER(DECL_NAME(decl));
  }

  struct XIL_AnnotationDecl *info =
    xcalloc(1, sizeof(struct XIL_AnnotationDecl));

  TREE_CHECK(decl, TYPE_DECL);
  info->decl = decl;
  info->name = name;
  info->artificial = artificial;

  if (last)
    last->next = info;
  else
    state->decls = info;
}

// gets the declaration info for decl, NULL if there is none.
static struct XIL_AnnotationDecl* XIL_GetDecl(tree decl)
{
  struct XIL_AnnotationDecl *info = state->decls;
  while (info) {
    if (info->decl == decl)
      return info;
    info = info->next;
  }
  return NULL;
}

// get the name to print for the specified type, indicating whether
// namespace information should be accounted for through pnamespace.
// the type must have a name.
static const char* XIL_GetTypeName(tree type, bool *pnamespace)
{
  tree name = TYPE_NAME(type);
  if (!name) {
    // this must be the 'this' type or an anonymous enum.
    *pnamespace = false;
    if (TREE_CODE(type) == ENUMERAL_TYPE)
      return "";
    return "__this";
  }

  if (TREE_CODE(name) == TYPE_DECL) {
    struct XIL_AnnotationDecl *decl = XIL_GetDecl(name);
    if (decl) {
      *pnamespace = !decl->artificial;
      return decl->name;
    }
    *pnamespace = false;
    return IDENTIFIER_POINTER(DECL_NAME(name));
  }
  else if (TREE_CODE(name) == IDENTIFIER_NODE) {
    *pnamespace = false;
    return IDENTIFIER_POINTER(name);
  }

  gcc_unreachable();
}

// makes a definition and appends it to the end of the state.
// ignores duplicate additions.
static void XIL_AddDef(tree type)
{
  // check whether this is a duplicate insert.
  struct XIL_AnnotationDef *last = state->defs;
  while (last) {
    // make sure don't add multiple definitions for the same struct/enum.
    // there can be multiple trees floating around for the same
    // conceptual type, so test equivalence as either having the same
    // name or the same fields/values.
    if (TYPE_NAME(type) && TYPE_NAME(type) == TYPE_NAME(last->type))
      return;
    if (TREE_CODE(type) == TREE_CODE(last->type) &&
        (TREE_CODE(type) == RECORD_TYPE || TREE_CODE(type) == UNION_TYPE) &&
        TYPE_FIELDS(type) && TYPE_FIELDS(type) == TYPE_FIELDS(last->type))
      return;
    if (TREE_CODE(type) == TREE_CODE(last->type) &&
        TREE_CODE(type) == ENUMERAL_TYPE &&
        TYPE_VALUES(type) && TYPE_VALUES(type) == TYPE_VALUES(last->type))
      return;
    if (!last->next) break;
    last = last->next;
  }

  bool define = true;

  // structs without names are not defined at the top level. make an exception
  // for the 'this' type on invariants in C, which might be anonymous.
  tree name = TYPE_NAME(type);
  if (!name && TREE_CODE(type) != ENUMERAL_TYPE) {
    if (!state->type || TREE_CODE(type) != TREE_CODE(state->type) ||
        TYPE_FIELDS(type) != TYPE_FIELDS(state->type))
      define = false;
  }

  // non-this structs/enums with C++ fake names are not defined at the top level.
  if (c_dialect_cxx() && !TypeNeedsDecl(type))
    define = false;

  // make sure that definitions with names have existing declarations.
  if (define && name && TREE_CODE(name) == TYPE_DECL) {
    gcc_assert(XIL_GetDecl(name));
    gcc_assert(DECL_RESULT_FLD(name) == NULL);
  }

  struct XIL_AnnotationDef *info =
    xcalloc(1, sizeof(struct XIL_AnnotationDef));

  info->type = type;
  info->define = define;

  if (last)
    last->next = info;
  else
    state->defs = info;
}

// define type if necessary, as well as all types which it depends on
// (declared as fields of the type without a pointer). if scan_context is set
// then any structures in which type was defined will be scanned first.
void XIL_ScanDefineType(tree type);

// scan type and add any declarations and definitions which type depends on
// before it can be printed. from_decl indicates that this came directly
// from a declaration.
void XIL_ScanPrintType(tree type, bool from_decl)
{
  gcc_assert(type);

  // construct the XIL representation, to ensure structs/etc. have names.
  XIL_TranslateType(type);

  // see if we scanned this type before. associate a flag with each type.
  // we can rescan the same type, we might see it both with and without
  // from_decl. this flag is just used to make sure we can all types we print.
  bool *scanned = (bool*) XIL_Associate(XIL_AscAnnotate, "ScanPrint", type);
  *scanned = true;

  tree name = TYPE_NAME(type);

  // add a declaration for named types.
  if (TypeNeedsDecl(type)) {
    // if this is a typedef then scan the target so any declarations
    // it uses are generated first.
    tree target_type = DECL_RESULT_FLD(name);
    if (target_type)
      XIL_ScanPrintType(target_type, true);
    // skip the declaration for types that are not typedefs or structs/enums.
    // these include builtins like 'void' and 'int'.
    if (target_type ||
        TREE_CODE(type) == RECORD_TYPE ||
        TREE_CODE(type) == UNION_TYPE ||
        TREE_CODE(type) == ENUMERAL_TYPE)
      XIL_AddDecl(name);
  }

  // add a definition for any enum type.
  if (TREE_CODE(type) == ENUMERAL_TYPE) {
    XIL_AddDef(type);
    return;
  }

  // add a definition for unnamed anonymous structures. the contents will have
  // to be printed out explicitly.
  if (TREE_CODE(type) == RECORD_TYPE || TREE_CODE(type) == UNION_TYPE) {
    if (!TypeNeedsDecl(type))
      XIL_ScanDefineType(type);
  }

  switch (TREE_CODE(type)) {
  case RECORD_TYPE:
  case UNION_TYPE: {
    // add an empty definition. if we end up adding a real definition later,
    // the empty definition will not be printed out.
    if (c_dialect_cxx() || !TYPE_FIELDS(type) ||
        !name || TREE_CODE(name) == TYPE_DECL)
      return;

    struct XIL_AnnotationEmptyDef *empty = state->emptydefs;
    while (empty) {
      if (TYPE_FIELDS(empty->type) == TYPE_FIELDS(type)) return;
      empty = empty->next;
    }
    empty = xcalloc(1, sizeof(struct XIL_AnnotationEmptyDef));
    empty->type = type;
    empty->next = state->emptydefs;
    state->emptydefs = empty;
    return;
  }

  case POINTER_TYPE:
  case REFERENCE_TYPE:
  case ARRAY_TYPE: {
    tree target_type = TREE_TYPE(type);
    XIL_ScanPrintType(target_type, false);

    // introduce typedefs for fnptr types that are not part of a decl.
    if (!from_decl &&
        (TREE_CODE(target_type) == FUNCTION_TYPE ||
         TREE_CODE(target_type) == METHOD_TYPE)) {
      struct XIL_AnnotationDecl *last = state->decls;
      while (last) {
        if (last->fnptr == type) return;
        if (!last->next) break;
        last = last->next;
      }
      struct XIL_AnnotationDecl *info =
        xcalloc(1, sizeof(struct XIL_AnnotationDecl));
      info->fnptr = type;

      info->name = xmalloc(30);
      sprintf((char*)info->name, "__fnptr%d", ++state->artificial_count);
      info->artificial = true;

      if (last)
        last->next = info;
      else
        state->decls = info;
    }

    return;
  }
  case FUNCTION_TYPE:
  case METHOD_TYPE: {
    tree return_type = TREE_TYPE(type);
    XIL_ScanPrintType(return_type, false);

    tree arg_types = TYPE_ARG_TYPES(type);
    while (arg_types) {
      gcc_assert(TREE_CODE(arg_types) == TREE_LIST);

      tree arg_type = TREE_VALUE(arg_types);
      XIL_ScanPrintType(arg_type, false);

      arg_types = TREE_CHAIN(arg_types);
    }
    return;
  }
  default:
    return;
  }
}

void XIL_ScanTemplateInfo(tree node)
{
  tree tinfo = get_template_info(node);
  gcc_assert(tinfo);

  tree arguments = TI_ARGS(tinfo);
  int arg_count = TREE_VEC_LENGTH(arguments);

  size_t ind;
  for (ind = 0; ind < arg_count; ind++) {
    tree arg = TREE_VEC_ELT(arguments, ind);
    if (TYPE_P(arg))
      XIL_ScanPrintType(arg, false);
  }
}

void XIL_ScanDefineType(tree type)
{
  // if the type is an inner structure then define the parent structure too.
  // this will end up scanning this structure recursively. we need this to
  // go first so as to not force an ordering of definitions between
  // the parent and inner structure (see below).
  tree name = TYPE_NAME(type);
  if (name && TREE_CODE(name) == TYPE_DECL) {
    tree context = DECL_CONTEXT(name);
    if (context &&
        (TREE_CODE(context) == RECORD_TYPE ||
         TREE_CODE(context) == UNION_TYPE))
      XIL_ScanDefineType(context);
  }

  // see if we scanned this type for defining before, associate a flag as
  // with ScanPrintType. unlike ScanPrintType, ScanDefineType may call itself
  // on the same type so we need to identify and block that recursion here.
  bool *scanned = (bool*) XIL_Associate(XIL_AscAnnotate, "ScanDefine", type);
  if (*scanned) return;
  *scanned = true;

  XIL_ScanPrintType(type, true);

  if (TREE_CODE(type) == ARRAY_TYPE)
    type = TREE_TYPE(type);

  // follow any typedef chains for the type. (we added declarations for
  // the typedefs in ScanPrintType).
  while (true) {
    tree name = TYPE_NAME(type);
    if (name && TREE_CODE(name) == TYPE_DECL) {
      tree target_type = DECL_RESULT_FLD(name);
      if (target_type) {
        type = target_type;
        continue;
      }
    }
    break;
  }

  if (TREE_CODE(type) != RECORD_TYPE && TREE_CODE(type) != UNION_TYPE)
    return;

  // scan and add definitions for all fields and types in the structure.
  // we will defer adding definitions for inner types/typedefs until
  // after we have made the definition for this struct and its fields:
  // defining this structure does not directly depend on definitions of
  // the inner type (though fields of this structure might).
  tree field = TYPE_FIELDS(type);
  while (field) {
    if (TREE_CODE(field) == FIELD_DECL || TREE_CODE(field) == VAR_DECL)
      XIL_ScanDefineType(TREE_TYPE(field));
    if (TREE_CODE(field) == TYPE_DECL)
      XIL_ScanPrintType(TREE_TYPE(field), true);
    field = TREE_CHAIN(field);
  }

  if (c_dialect_cxx()) {
    // scan the types of any template arguments.
    if (CLASSTYPE_USE_TEMPLATE(type))
      XIL_ScanTemplateInfo(type);

    // scan the types of any methods.
    VEC(tree,gc) *methods = CLASSTYPE_METHOD_VEC(type);
    int ind = 2;
    tree node = NULL;
    for (; VEC_iterate(tree,methods,ind,node); ind++) {
      while (node) {
        tree method = OVL_CURRENT(node);
        if (TREE_CODE(method) == FUNCTION_DECL)
          XIL_ScanPrintType(TREE_TYPE(method), true);
        node = OVL_NEXT(node);
      }
    }
  }

  // add a definition for the structure itself now.
  XIL_AddDef(type);

  // add definitions for the inner structures which we deferred earlier.
  field = TYPE_FIELDS(type);
  while (field) {
    if (TREE_CODE(field) == TYPE_DECL &&
        DECL_RESULT_FLD(field) == NULL)
      XIL_ScanDefineType(TREE_TYPE(field));
    field = TREE_CHAIN(field);
  }
}

// characters that can appear between quotes we process.
static inline bool quote_char(char c)
{
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
      || (c >= '0' && c <= '9') || (c == '_') || (c == ' ') || (c == ':');
}

// if *str is a string quoted with three-character unicode sequences,
// get the quoted contents and set *str to the position immediately after
// the quoted string.
char* GetNameQuote(char **str)
{
  // the first character in the unicode sequences are ASCII -30.
  if (**str != (char) -30)
    return NULL;

  char *pos = *str + 3;
  while (quote_char(*pos)) pos++;

  if (*pos != (char) -30)
    return NULL;

  int length = pos - (*str + 3);
  char *res = xmalloc(length + 1);
  memcpy(res, *str + 3, length);
  res[length] = 0;

  *str = pos + 3;
  return res;
}

// if message follows the form "pre_text `quoted' post_text" then store
// those three components of the string in pre, quoted and post.
bool GetQuoteMessage(char *message, char **pre, char **quoted, char **post)
{
  // scan for an open quote character.
  char *pos = message;
  while (*pos && *pos != (char) -30) pos++;
  if (!*pos) return false;

  char *quote_begin = pos;
  char *str = GetNameQuote(&pos);
  if (!str) return false;

  *pre = xmalloc(quote_begin - message + 1);
  memcpy(*pre, message, quote_begin - message);
  (*pre)[quote_begin - message] = 0;

  // eat any leading 'const ', 'struct ' and/or 'union ' from the quoted
  // portion of the string.
  if (!strncmp(str,"const ",6)) str += 6;
  if (!strncmp(str,"struct ",7)) str += 7;
  if (!strncmp(str,"union ",6)) str += 6;

  // eat any namespaces from the quoted portion of the string.
  while (true) {
    char *colon = strchr(str, ':');
    if (!colon) break;
    str = colon + 1;
  }

  *quoted = str;
  *post = xstrdup(pos);
  return true;
}

static bool HandleMissingDeclaration(const char *name)
{
  tree idnode = get_identifier(name);
  tree decl = lookup_name(idnode);

  if (!decl)
    return false;

  // use any namespace for this declaration.
  if (c_dialect_cxx() && DECL_CONTEXT(decl) &&
      TREE_CODE(DECL_CONTEXT(decl)) == NAMESPACE_DECL &&
      DECL_NAME(DECL_CONTEXT(decl))) {
    struct XIL_AnnotationNamespace *namespc =
      xcalloc(1, sizeof(struct XIL_AnnotationNamespace));
    namespc->context = DECL_CONTEXT(decl);
    namespc->next = state->namespaces;
    state->namespaces = namespc;
  }

  if (TREE_CODE(decl) == FUNCTION_DECL || TREE_CODE(decl) == VAR_DECL) {
    // the missing declaration is a function or global variable.
    XIL_ScanPrintType(TREE_TYPE(decl), true);

    struct XIL_AnnotationVar *info =
      xcalloc(1, sizeof(struct XIL_AnnotationVar));
    info->decl = decl;
    info->next = state->vars;
    state->vars = info;
    return true;
  }

  if (TREE_CODE(decl) == OVERLOAD) {
    // the missing declaration is one of a number of overloaded functions.
    while (decl) {
      tree function = OVL_CURRENT(decl);
      if (TREE_CODE(function) == FUNCTION_DECL) {
        XIL_ScanPrintType(TREE_TYPE(function), true);

        struct XIL_AnnotationVar *info =
          xcalloc(1, sizeof(struct XIL_AnnotationVar));
        info->decl = function;
        info->next = state->vars;
        state->vars = info;
      }

      decl = OVL_NEXT(decl);
    }
    return true;
  }

  if (TREE_CODE(decl) == TYPE_DECL) {
    // the missing declaration is a typedef. scanning the type will
    // add the appropriate declaration.
    gcc_assert(TYPE_NAME(TREE_TYPE(decl)) == decl);
    XIL_ScanPrintType(TREE_TYPE(decl), false);
    return true;
  }

  if (TREE_CODE(decl) == CONST_DECL) {
    // the missing declaration is an enum constant. define the whole enum.
    tree type = TREE_TYPE(decl);
    TREE_CHECK(type, ENUMERAL_TYPE);
    XIL_ScanPrintType(type, false);
    return true;
  }

  if (TREE_CODE(decl) == TEMPLATE_DECL) {
    TREE_UNHANDLED();
    return false;
  }

  TREE_UNEXPECTED(decl);
  return false;
}

static bool HandleMissingDefinition(const char *name)
{
  // find a matching typedef or struct.
  struct XIL_AnnotationDecl *info = state->decls;
  while (info) {
    if (!strcmp(name, info->name))
      break;
    info = info->next;
  }

  if (!info) {
    if (!HandleMissingDeclaration(name))
      return false;

    // try again.
    info = state->decls;
    while (info) {
      if (!strcmp(name, info->name))
        break;
      info = info->next;
    }

    if (!info)
      return false;
  }

  XIL_ScanDefineType(TREE_TYPE(info->decl));
  return true;
}

// returns true if the error message was interpreted successfully and the
// state was changed to fix the error.
bool XIL_ProcessAnnotationError(char *error_message)
{
  char *pre, *quoted, *post;
  if (!GetQuoteMessage(error_message, &pre, &quoted, &post))
    return false;

  // look for a missing declaration.
  // different messages we can see, depending on the frontend and usage.
  const char *decl_msg_1 = " undeclared";
  const char *decl_msg_2 = " was not declared in this scope";
  const char *decl_msg_3 = " has not been declared";

  if (!strncmp(post, decl_msg_1, strlen(decl_msg_1)) ||
      !strncmp(post, decl_msg_2, strlen(decl_msg_2)) ||
      !strncmp(post, decl_msg_3, strlen(decl_msg_3))) {
    if (cpp_defined(parse_in,
                    (unsigned char*) quoted, strlen(quoted))) {
      // the missing declaration is a macro.
      cpp_hashnode *node =
        cpp_lookup(parse_in,
                   (unsigned char*) quoted, strlen(quoted));
      const char *macro = (const char*) cpp_macro_definition(parse_in, node);

      struct XIL_AnnotationMacro *info =
        xcalloc(1, sizeof(struct XIL_AnnotationMacro));
      info->macro = macro;
      info->next = state->macros;
      state->macros = info;
      return true;
    }

    return HandleMissingDeclaration(quoted);
  }

  // look for an incomplete type.
  const char *incomplete_msg_1 = "invalid use of incomplete type ";
  const char *incomplete_msg_2 = "incomplete type ";

  if (!strcmp(pre, incomplete_msg_1) ||
      !strcmp(pre, incomplete_msg_2)) {
    return HandleMissingDefinition(quoted);
  }

  // look for a use of 'sizeof', which is quoted in error messages.
  if (!strcmp(pre, "invalid application of ") && !strcmp(quoted, "sizeof")) {
    char *npre, *nquoted, *npost;
    if (GetQuoteMessage(post, &npre, &nquoted, &npost)) {
      if (!strcmp(npre, " to incomplete type "))
        return HandleMissingDefinition(nquoted);
    }
  }

  // look for an incomplete type for C frontend hack.
  const char *nomember_msg = " has no member named ";

  if (!strncmp(post, nomember_msg, strlen(nomember_msg))) {
    // find a matching empty definition.
    struct XIL_AnnotationEmptyDef *empty = state->emptydefs;
    while (empty) {
      if (!strcmp(quoted, IDENTIFIER_POINTER(TYPE_NAME(empty->type))))
        break;
      empty = empty->next;
    }

    if (!empty)
      return false;

    XIL_ScanDefineType(empty->type);
    return true;
  }

  return false;
}

// print the specified type to file.
void XIL_PrintType(FILE *file, tree type);

// print a declaration of a variable name with the specified type to file.
// type may be a function, method, array, or simpler type.
void XIL_PrintDeclaration(FILE *file, tree type, const char *name);

// print a struct/union definition to file.
void XIL_PrintStruct(FILE *file, const char *csu_name, tree type);

// print an enum definition to file.
void XIL_PrintEnum(FILE *file, const char *enum_name, tree type);

// print a function or function pointer type with the specified name to file.
void XIL_PrintFunctionType(FILE *file, tree type, bool function_pointer,
                           const char *name);

// print the declaration for the annotation function to file.
void XIL_PrintAnnotationHeader(FILE *file);

// print any namespace context information for decl to file.
void XIL_PrintContext(FILE *file, tree decl)
{
  tree context = DECL_CONTEXT(decl);
  if (context) {
    // should only see namespace contexts here.
    gcc_assert(TREE_CODE(context) != RECORD_TYPE);
    gcc_assert(TREE_CODE(context) != UNION_TYPE);
    if (TREE_CODE(context) == NAMESPACE_DECL && DECL_NAME(context)) {
      XIL_PrintContext(file, context);
      fprintf(file, "%s", IDENTIFIER_POINTER(DECL_NAME(context)));
      fprintf(file, "::");
    }
  }
}

// print a namespace to file, without a trailing '::'.
void XIL_PrintBaseContext(FILE *file, tree context)
{
  TREE_CHECK(context, NAMESPACE_DECL);
  XIL_PrintContext(file, context);
  fprintf(file, "%s", IDENTIFIER_POINTER(DECL_NAME(context)));
}

// print any struct/union/enum prefix for type.
void XIL_PrintStructPrefix(FILE *file, tree type)
{
  switch (TREE_CODE(type)) {
  case RECORD_TYPE:   fprintf(file, "struct "); break;
  case UNION_TYPE:    fprintf(file, "union "); break;
  case ENUMERAL_TYPE: fprintf(file, "enum "); break;
  default: TREE_UNEXPECTED(type);
  }
}

void XIL_PrintType(FILE *file, tree type)
{
  // make sure we previously scanned this type.
  bool *scanned = (bool*) XIL_Associate(XIL_AscAnnotate, "ScanPrint", type);
  gcc_assert(*scanned);

  tree name = TYPE_NAME(type);

  if (TypeNeedsDecl(type)) {
    // use the name from the declaration we added earlier. if there is no
    // declaration then use the type's name as is.
    bool use_namespace = false;
    const char *print_name = XIL_GetTypeName(type, &use_namespace);
    if (use_namespace)
      XIL_PrintContext(file, name);
    fprintf(file, "%s", print_name);
    return;
  }

  switch (TREE_CODE(type)) {
  case RECORD_TYPE:
  case UNION_TYPE:
  case ENUMERAL_TYPE: {
    if (name && TREE_CODE(name) == IDENTIFIER_NODE) {
      // regular name, use it but add a prefix according to the kind.
      XIL_PrintStructPrefix(file, type);
      fprintf(file, "%s", IDENTIFIER_POINTER(name));
    }
    else if (TREE_CODE(type) == ENUMERAL_TYPE) {
      // anonymous enum.
      XIL_PrintEnum(file, NULL, type);
    }
    else {
      // anonymous struct/union.
      XIL_PrintStruct(file, NULL, type);
    }
    return;
  }
  case INTEGER_TYPE: {
    // integer type not declared through a typedef. this is either
    // 'signed' or 'unsigned'.
    if (TYPE_UNSIGNED(type))
      fprintf(file, "unsigned");
    else
      fprintf(file, "signed");
    return;
  }
  case POINTER_TYPE: {
    tree target = TREE_TYPE(type);

    // check for a function pointer. we scanned this type so there should
    // be a function pointer typedef.
    if (TREE_CODE(target) == FUNCTION_TYPE ||
        TREE_CODE(target) == METHOD_TYPE) {
      struct XIL_AnnotationDecl *info = state->decls;
      while (info) {
        if (info->fnptr == type) {
          fprintf(file, "%s", info->name);
          return;
        }
        info = info->next;
      }
      gcc_unreachable();
    }

    // print out the type with any associated 'const', which we need
    // to resolve overloaded functions correctly.
    XIL_PrintType(file, target);
    if (c_dialect_cxx() && CP_TYPE_CONST_P(target))
      fprintf(file, " const");
    fprintf(file, "*");
    return;
  }
  case REFERENCE_TYPE: {
    tree target = TREE_TYPE(type);

    // check for an array reference.
    if (TREE_CODE(target) == ARRAY_TYPE) {
      tree domain = TYPE_DOMAIN(target);
      if (domain) {
        tree minval = TYPE_MIN_VALUE(domain);
        tree maxval = TYPE_MAX_VALUE(domain);
        gcc_assert(TREE_UINT(minval) == 0);

        if (maxval && TREE_CODE(maxval) == INTEGER_CST) {
          XIL_PrintType(file, TREE_TYPE(target));
          fprintf(file, " (&)[%lu]", TREE_UINT(maxval));
          return;
        }
      }
    }

    // need to handle 'const' in the same manner as for pointer types.
    XIL_PrintType(file, target);
    if (c_dialect_cxx() && CP_TYPE_CONST_P(target))
      fprintf(file, " const");
    fprintf(file, "&");
    return;
  }
  case OFFSET_TYPE: {
    // TODO: width is wrong here.
    fprintf(file, "void*");
    return;
  }
  default:
    TREE_UNEXPECTED(type);
  }
}

void XIL_PrintDeclaration(FILE *file, tree type, const char *name)
{
  // check for a function pointer or function type.
  bool function_pointer = false;
  if (TREE_CODE(type) == POINTER_TYPE) {
    tree target_type = TREE_TYPE(type);
    if (TREE_CODE(target_type) == FUNCTION_TYPE ||
        TREE_CODE(target_type) == METHOD_TYPE) {
      function_pointer = true;
      type = target_type;
    }
  }

  // check for a declaration of a function or method or function pointer.
  if (TREE_CODE(type) == FUNCTION_TYPE || TREE_CODE(type) == METHOD_TYPE) {
    XIL_PrintFunctionType(file, type, function_pointer, name);
    return;
  }

  if (TREE_CODE(type) == ARRAY_TYPE) {
    tree element_type = TREE_TYPE(type);

    // extract the element count. this mirrors TranslateArrayType.
    int count = 0;

    tree domain = TYPE_DOMAIN(type);
    if (domain) {
      tree minval = TYPE_MIN_VALUE(domain);
      tree maxval = TYPE_MAX_VALUE(domain);
      gcc_assert(TREE_UINT(minval) == 0);

      if (maxval) {
        if (TREE_CODE(maxval) != INTEGER_CST) {
          // variable sized array. promote this to a pointer so the treatment
          // in the annotation and original source is consistent.
          XIL_PrintType(file, element_type);
          fprintf(file, "* %s", name);
          return;
        }

        if (TREE_INT_CST_HIGH(maxval) == 0)
          count = TREE_UINT(maxval) + 1;
      }
    }

    // watch out for element types which are also arrays (multidimensional).
    // these need to be special cased so that we don't do the wrong thing
    // for arrays of function pointers.
    if (TREE_CODE(element_type) == ARRAY_TYPE) {
      XIL_PrintDeclaration(file, element_type, name);
      fprintf(file, " [%d]", count);
    }
    else {
      XIL_PrintType(file, element_type);
      if (count) fprintf(file, " %s[%d]", name, count);
      else       fprintf(file, " %s[]", name);
    }

    return;
  }

  // plain integer/pointer/structure/etc. type.
  XIL_PrintType(file, type);
  fprintf(file, " %s", name);
}

void XIL_PrintTemplateInfo(FILE *file, tree node)
{
  tree tinfo = get_template_info(node);
  gcc_assert(tinfo);

  tree parameters = DECL_INNERMOST_TEMPLATE_PARMS(TI_TEMPLATE(tinfo));
  tree arguments = TI_ARGS(tinfo);

  // TODO: handle default arguments?
  int parm_count = TREE_VEC_LENGTH(parameters);
  int arg_count = TREE_VEC_LENGTH(arguments);
  int count = MIN(parm_count, arg_count);

  size_t ind;
  for (ind = 0; ind < count; ind++) {
    // TODO: handle template parameters which aren't typedefs.
    tree parm = TREE_VEC_ELT(parameters, ind);
    tree decl = TREE_VALUE(parm);
    if (TREE_CODE(decl) != TYPE_DECL)
      continue;

    tree arg = TREE_VEC_ELT(arguments, ind);
    if (!TYPE_P(arg))
      continue;

    fprintf(file, "typedef ");
    XIL_PrintType(file, arg);
    fprintf(file, " %s;\n", IDENTIFIER_POINTER(DECL_NAME(decl)));
  }
}

void XIL_PrintStruct(FILE *file, const char *csu_name, tree type)
{
  gcc_assert(state);
  XIL_PrintStructPrefix(file, type);

  // tag the structure with its real name.
  const char *full_name = XIL_CSUName(type, NULL);
  gcc_assert(full_name);
  fprintf(file, " __attribute__((annot_global(\"%s\")))", full_name);

  // whether we are printing the 'this' structure.
  bool this_struct = false;

  if (state->type && TYPE_FIELDS(type) == TYPE_FIELDS(state->type)) {
    this_struct = true;

    // mark the structure with an attribute.
    fprintf(file, "__attribute__((annot_this))");

    // type invariants in C always use a special '__this' name in case they
    // are anonymous. an annot_global attribute indicates the real type name.
    if (!c_dialect_cxx())
      csu_name = "__this";
  }

  if (csu_name)
    fprintf(file, " %s", csu_name);

  // look for any base classes. these are anonymous fields with names,
  // and tend to appear at the beginning of the type's fields (except in
  // cases such as a base without a vtable and a subclass with one).
  tree field = TYPE_FIELDS(type);
  bool has_base = false;
  while (c_dialect_cxx() && field) {
    if (XIL_IsBaseField(field, NULL)) {
      if (!has_base) {
        fprintf(file, " : ");
        has_base = true;
      }
      else {
        fprintf(file, ", ");
      }

      XIL_PrintType(file, TREE_TYPE(field));
    }

    field = TREE_CHAIN(field);
  }

  fprintf(file, " {\n");

  // print out the fields, static fields, and typedefs for all inner typedefs
  // and struct/union/enum definitions.
  field = TYPE_FIELDS(type);
  while (field) {
    if (XIL_IsBaseField(field, NULL)) {
      field = TREE_CHAIN(field);
      continue;
    }

    if (TREE_CODE(field) == FIELD_DECL) {
      if (DECL_NAME(field) != NULL) {
        const char *name = IDENTIFIER_POINTER(DECL_NAME(field));

        // watch for fake vtable fields. these start with '_vptr.'
        if (!strncmp(name, "_vptr.", 6)) {
          fprintf(file, "void* __annotation_vptr;\n");
          field = TREE_CHAIN(field);
          continue;
        }

        tree type = TREE_TYPE(field);
        XIL_PrintDeclaration(file, type, name);
      }
      else {
        tree type = TREE_TYPE(field);
        XIL_PrintType(file, type);
      }
      fprintf(file, ";\n");
    }
    else if (TREE_CODE(field) == VAR_DECL) {
      // static member.
      const char *name = IDENTIFIER_POINTER(DECL_NAME(field));

      // make a fake ENUM constant for constant static members.
      if (TYPE_READONLY(TREE_TYPE(field))) {
        tree initial = DECL_INITIAL(field);
        if (initial && TREE_CODE(initial) == INTEGER_CST) {
          const char *str = XIL_TreeIntString(initial);
          fprintf(file, "enum { %s = %s };\n", name, str);
          field = TREE_CHAIN(field);
          continue;
        }
      }

      const char *full_name = XIL_GlobalName(field);
      fprintf(file, "__attribute__((annot_global(\"%s\"))) static\n", full_name);
      XIL_PrintDeclaration(file, TREE_TYPE(field), name);
      fprintf(file, ";\n");
    }
    else if (TREE_CODE(field) == TYPE_DECL) {
      // structure or typedef. inner structures were already marked for
      // definition with an artificial name, so we can do both cases here with
      // typedefs. scan the previous fields of the structure for any other type
      // with the same name (one must be a struct, the other must be a typedef)
      // and skip if this is a duplicate.
      if (!XIL_IsSelfTypeDecl(field) && !XIL_IsAnonymousCxx(field)) {
        const char *name = IDENTIFIER_POINTER(DECL_NAME(field));
        bool duplicate = false;
        tree ofield = TYPE_FIELDS(type);
        while (ofield) {
          if (TREE_CODE(ofield) == TYPE_DECL &&
              !strcmp(IDENTIFIER_POINTER(DECL_NAME(ofield)), name))
            duplicate = true;
          ofield = TREE_CHAIN(ofield);
        }

        if (!duplicate) {
          fprintf(file, "typedef ");
          XIL_PrintDeclaration(file, TREE_TYPE(field), name);
          fprintf(file, ";\n");
        }
      }
    }
    else if (TREE_CODE(field) == CONST_DECL) {
      tree initial = DECL_INITIAL(field);
      gcc_assert(initial);
      if (TREE_CODE(initial) == INTEGER_CST) {
        // maybe a member of an anonymous enum.
        const char *str = XIL_TreeIntString(initial);
        fprintf(file, "enum { %s = %s };\n", IDENTIFIER_POINTER(DECL_NAME(field)), str);
      }
    }

    field = TREE_CHAIN(field);
  }

  if (c_dialect_cxx() && CLASSTYPE_USE_TEMPLATE(type))
    XIL_PrintTemplateInfo(file, type);

  if (c_dialect_cxx() && !XIL_IsAnonymousCxx(TYPE_NAME(type))) {
    // print out the methods as well. start at index 2 in the methods vector,
    // which skips all constructors and destructors for the class. don't do
    // this for anonymous structures, as they may have copy constructors
    // that take the same type as an argument, leading to infinite recursion.
    VEC(tree,gc) *methods = CLASSTYPE_METHOD_VEC(type);
    int ind = 2;
    tree node = NULL;
    for (; VEC_iterate(tree,methods,ind,node); ind++) {
      while (node) {
        // the node may or may not be an overload. these handle both cases.
        tree method = OVL_CURRENT(node);
        if (TREE_CODE(method) != FUNCTION_DECL) {
          node = OVL_NEXT(node);
          continue;
        }

        tree method_type = TREE_TYPE(method);
        const char *name = IDENTIFIER_POINTER(DECL_NAME(method));

        // skip printing for assignment operators, these can't be in unions.
        // TODO: use of assignment operators in annotations is problematic.
        // if the annotation uses this and it is a non-default operator,
        // the annotation won't compile. if it is a default operator,
        // GCC will fabricate a new one with the wrong name while processing
        // the annotation file.
        if (!strcmp(name, "operator=")) {
          node = OVL_NEXT(node);
          continue;
        }

        const char *full_name = XIL_GlobalName(method);
        fprintf(file, "__attribute__((annot_global(\"%s\")))\n",
                full_name);

        if (DECL_STATIC_FUNCTION_P(method))
          fprintf(file, "static ");

        XIL_PrintDeclaration(file, method_type, name);
        fprintf(file, ";\n");

        node = OVL_NEXT(node);
      }
    }
  }

  // print the annotation header if we are in the 'this' type.
  if (c_dialect_cxx() && this_struct) {
    XIL_PrintAnnotationHeader(file);
    fprintf(file, ";\n");
  }

  // don't include the closing ';', callers need to do this if necessary.
  fprintf(file, "}");
}

void XIL_PrintEnum(FILE *file, const char *enum_name, tree type)
{
  if (!enum_name) enum_name = "";
  fprintf(file, "enum %s {\n", enum_name);

  tree value = TYPE_VALUES(type);
  while (value) {
    tree decl = TREE_VALUE(value);

    // enums look different in C vs. C++. C enums use a purpose/value pair,
    // C++ enums use a CONST_DECL for the value.
    if (TREE_CODE(decl) == INTEGER_CST) {
      tree purpose = TREE_PURPOSE(value);
      if (purpose && TREE_CODE(purpose) == IDENTIFIER_NODE) {
        const char *str = XIL_TreeIntString(decl);
        fprintf(file, "%s = %s,\n", IDENTIFIER_POINTER(purpose), str);
      }
      else {
        TREE_UNEXPECTED(value);
      }
    }
    else if (TREE_CODE(decl) == CONST_DECL) {
      tree initial = DECL_INITIAL(decl);
      gcc_assert(initial && TREE_CODE(initial) == INTEGER_CST);
      const char *str = XIL_TreeIntString(initial);
      fprintf(file, "%s = %s,\n", IDENTIFIER_POINTER(DECL_NAME(decl)), str);
    }
    else {
      TREE_UNEXPECTED(decl);
    }

    value = TREE_CHAIN(value);
  }

  fprintf(file, "}");
}

void XIL_PrintFunctionType(FILE *file, tree type, bool function_pointer,
                           const char *name)
{
  tree return_type = TREE_TYPE(type);

  // special case conversion operators, these have to be printed differently.
  // this has the name 'operator N' for some N (seems to be a counter
  // similar to the one found by IsAnonymousCxx).
  bool convert = false;
  if (!strncmp(name, "operator ",9)) {
    char pos = name[9];
    if (pos >= '1' && pos <= '9')
      convert = true;
  }

  if (convert) {
    fprintf(file, "operator ");
    XIL_PrintType(file, return_type);
    fprintf(file, "(");
  }
  else {
    // regular function or function pointer.
    XIL_PrintType(file, return_type);

    if (function_pointer)
      fprintf(file, " (*%s)(", name);
    else
      fprintf(file, " %s(", name);
  }

  tree arg_types = TYPE_ARG_TYPES(type);
  bool first_arg = true;

  // skip the implicit 'this' argument, if this is a method then it is being
  // printed in the enclosing structure's definition.
  tree this_type = NULL;
  if (TREE_CODE(type) == METHOD_TYPE) {
    gcc_assert(arg_types);
    this_type = TREE_VALUE(arg_types);
    arg_types = TREE_CHAIN(arg_types);
  }

  while (arg_types) {
    gcc_assert(TREE_CODE(arg_types) == TREE_LIST);
    tree arg_type = TREE_VALUE(arg_types);
    arg_types = TREE_CHAIN(arg_types);

    // skip the fake last argument, see type.c
    if (TREE_CODE(arg_type) == VOID_TYPE) {
      gcc_assert(arg_types == NULL);
      break;
    }

    if (first_arg)
      first_arg = false;
    else
      fprintf(file,",");

    XIL_PrintType(file, arg_type);
  }

  fprintf(file, ")");

  // print out the 'const' for appropriate methods. this shows up as
  // a 'const' on the target of the this parameter.
  if (this_type && CP_TYPE_CONST_P(TREE_TYPE(this_type)))
    fprintf(file, " const");
}

// print declarations for a function parameter. there is always an argN
// declaration, and a declaration using the actual name if it has one.
void XIL_PrintParameter(FILE *file, tree decl, int index)
{
  tree type = TREE_TYPE(decl);

  const char *param_name = NULL;
  char *index_name = xmalloc(20);
  sprintf(index_name, "arg%d", index);

  if (DECL_NAME(decl)) {
    param_name = IDENTIFIER_POINTER(DECL_NAME(decl));
    fprintf(file, "__attribute__((annot_param(%d))) extern\n", index);
    XIL_PrintDeclaration(file, type, param_name);
    fprintf(file, ";\n");
  }
  else {
    param_name = index_name;
  }

  fprintf(file, "__attribute__((annot_param(%d),annot_source(\"%s\"))) extern\n", index, param_name);
  XIL_PrintDeclaration(file, type, index_name);
  fprintf(file, ";\n");
}

void XIL_PrintAnnotationHeader(FILE *file)
{
  const char *name = NULL;
  const char *full_name = NULL;

  if (state->decl) {
    name = XIL_SourceName(state->decl);
    full_name = XIL_GlobalName(state->decl);
  }
  else {
    gcc_assert(state->type);
    name = full_name = XIL_CSUName(state->type, NULL);
    gcc_assert(name);
  }

  fprintf(file, "__attribute__((annot_name(\"%s\")))\n", state->name);
  fprintf(file, "__attribute__((annot_global(\"%s\")))\n", full_name);
  fprintf(file, "__attribute__((annot_source(\"%s\")))\n", name);
  fprintf(file, "void __annotation()");
}

// print 'namespace NAME {' wrappers for each namespace enclosing decl.
// returns the number of namespaces printed.
int XIL_PrintNamespaces(FILE *file, tree decl)
{
  if (!decl)
    return 0;
  if (TREE_CODE(decl) != TYPE_DECL && TREE_CODE(decl) != NAMESPACE_DECL)
    return 0;
  tree context = DECL_CONTEXT(decl);
  if (context && TREE_CODE(context) == NAMESPACE_DECL && DECL_NAME(context)) {
    int count = XIL_PrintNamespaces(file, context);
    fprintf(file, "namespace %s { ", IDENTIFIER_POINTER(DECL_NAME(context)));
    return count + 1;
  }
  return 0;
}

void WriteAnnotationFile(FILE *file)
{
  // add macro for return variable.
  fprintf(file, "#define return __return\n");

  // add any extra macros.
  struct XIL_AnnotationMacro *macro = state->macros;
  while (macro) {
    fprintf(file, "#define %s\n", macro->macro);
    macro = macro->next;
  }

  // add declarations for annotation functions. these need to be wrapped
  // in macros to ensure they can be passed any type without casts and that
  // we see whichever type was used for the bound functions.
  fprintf(file,
"#define ubound(X) ({ extern typeof((X)[0]) __data; extern long __ubound(typeof((X)[0]) *ptr); __ubound(X); })\n"
"#define lbound(X) ({ extern typeof((X)[0]) __data; extern long __lbound(typeof((X)[0]) *ptr); __lbound(X); })\n"
"#define zterm(X) ({ extern typeof((X)[0]) __data; extern long __zterm(typeof((X)[0]) *ptr); __zterm(X); })\n"
"#define initial(X) ({ typeof(X) __initial = (X); __initial; })\n"
"#define gcsafe(X) ({ typeof(X) __gcsafe = (X); (long) __gcsafe; })\n"
"int skip_inference();\n"
  );

  // add any enum definitions. enum definitions have to go before declarations
  // because enums cannot be declared in the way structs or unions are.
  struct XIL_AnnotationDef *def = state->defs;
  while (def) {
    if (def->define && TREE_CODE(def->type) == ENUMERAL_TYPE) {
      // get the name to define it as, either from a declaration or from
      // the type itself.
      bool use_namespace = false;
      const char *print_name = XIL_GetTypeName(def->type, &use_namespace);

      // wrap the definition in any namespace context.
      int namespace_count = 0;
      if (use_namespace)
        namespace_count = XIL_PrintNamespaces(file, TYPE_NAME(def->type));

      XIL_PrintEnum(file, print_name, def->type);

      // close the namespace context.
      fprintf(file, ";");
      while (namespace_count--)
        fprintf(file, " }");
      fprintf(file, "\n");
    }

    def = def->next;
  }

  // add any declarations.
  struct XIL_AnnotationDecl *decl = state->decls;
  while (decl) {
    // handle function pointer typedefs we've introduced.
    if (decl->fnptr) {
      fprintf(file, "typedef ");
      XIL_PrintDeclaration(file, decl->fnptr, decl->name);
      fprintf(file, ";\n");
      decl = decl->next;
      continue;
    }

    tree target_type = DECL_RESULT_FLD(decl->decl);
    // skip non-typedef enum declarations, these were already defined.
    if (!target_type && TREE_CODE(TREE_TYPE(decl->decl)) == ENUMERAL_TYPE) {
      decl = decl->next;
      continue;
    }

    // wrap the declaration in any namespace context.
    int namespace_count = 0;
    if (!decl->artificial)
      namespace_count = XIL_PrintNamespaces(file, decl->decl);

    if (target_type) {
      // this is a typedef declaration.
      fprintf(file, "typedef ");
      XIL_PrintDeclaration(file, target_type, decl->name);
      fprintf(file, ";");
    }
    else {
      // this is a struct/union/enum declaration.
      tree type = TREE_TYPE(decl->decl);
      XIL_PrintStructPrefix(file, type);

      // mark the name we are using in the generated blocks for structs/unions.
      if (TREE_CODE(type) == RECORD_TYPE || TREE_CODE(type) == UNION_TYPE) {
        const char *full_name = XIL_CSUName(type, NULL);
        gcc_assert(full_name);
        fprintf(file, "__attribute__((annot_global(\"%s\"))) ", full_name);
      }

      fprintf(file, "%s;", decl->name);
    }

    // close any namespaces we printed earlier.
    while (namespace_count--)
      fprintf(file, " }");
    fprintf(file, "\n");

    decl = decl->next;
  }

  // add any struct/union definitions.
  def = state->defs;
  while (def) {
    if (def->define && TREE_CODE(def->type) != ENUMERAL_TYPE) {
      // get the name to define it as, either from a declaration or from
      // the type itself.
      bool use_namespace = false;
      const char *print_name = XIL_GetTypeName(def->type, &use_namespace);

      // wrap the definition in any namespace context.
      int namespace_count = 0;
      if (use_namespace)
        namespace_count = XIL_PrintNamespaces(file, TYPE_NAME(def->type));

      XIL_PrintStruct(file, print_name, def->type);

      // close the namespace context.
      fprintf(file, ";");
      while (namespace_count--)
        fprintf(file, " }");
      fprintf(file, "\n");
    }
    def = def->next;
  }

  struct XIL_AnnotationEmptyDef *empty = state->emptydefs;
  while (empty) {
    // check if we added a real definition for this type.
    bool defined = false;
    def = state->defs;
    while (def) {
      if (TREE_CODE(def->type) != ENUMERAL_TYPE &&
          TYPE_FIELDS(def->type) == TYPE_FIELDS(empty->type))
        defined = true;
      def = def->next;
    }

    if (!defined) {
      XIL_PrintStructPrefix(file, empty->type);
      const char *name = IDENTIFIER_POINTER(TYPE_NAME(empty->type));
      fprintf(file, " %s { };\n", name);
    }

    empty = empty->next;
  }

  // add any variable declarations.
  struct XIL_AnnotationVar *var = state->vars;
  while (var) {
    tree type = TREE_TYPE(var->decl);
    const char *name = IDENTIFIER_POINTER(DECL_NAME(var->decl));

    // make a fake ENUM constant for constant globals.
    if (TYPE_READONLY(type)) {
      tree initial = DECL_INITIAL(var->decl);
      if (initial && TREE_CODE(initial) == INTEGER_CST) {
        const char *str = XIL_TreeIntString(initial);
        fprintf(file, "enum { %s = %s };\n", name, str);
        var = var->next;
        continue;
      }
    }

    const char *full_name = XIL_GlobalName(var->decl);
    fprintf(file, "__attribute__((annot_global(\"%s\"))) extern\n",
            full_name);

    XIL_PrintDeclaration(file, type, name);
    fprintf(file, ";\n");
    var = var->next;
  }

  // print out the annotation function to file.
  if (c_dialect_cxx() && state->type) {
    fprintf(file, "void ");
    XIL_PrintType(file, state->type);
    fprintf(file, "::__annotation() {\n");
  }
  else {
    XIL_PrintAnnotationHeader(file);
    fprintf(file, " {\n");
  }

  if (state->decl && TREE_CODE(state->decl) == FUNCTION_DECL) {
    // add the parameters to the annotation.
    tree param = DECL_ARGUMENTS(state->decl);
    int param_index = 0;

    // use the parameter declaration list we've constructed for function
    // declarations in C. these won't have an arguments list.
    if (!param) {
      struct XIL_ParamDecl *param_decl = xil_pending_param_decls;
      while (param_decl) {
        XIL_PrintParameter(file, param_decl->decl, param_index);
        param_decl = param_decl->next;
        param_index++;
      }
    }

    // skip any implicit 'this' variable so the param index is correct,
    // see variable.c
    if (TREE_CODE(TREE_TYPE(state->decl)) == METHOD_TYPE)
      param = TREE_CHAIN(param);

    while (param) {
      XIL_PrintParameter(file, param, param_index);
      param = TREE_CHAIN(param);
      param_index++;
    }

    // add any return variable to the annotation.
    tree result_type = TREE_TYPE(TREE_TYPE(state->decl));
    if (TREE_CODE(result_type) != VOID_TYPE) {
      fprintf(file, "__attribute__((annot_return)) extern\n");
      XIL_PrintDeclaration(file, result_type, "return");
      fprintf(file, ";\n");
    }

    if (c_dialect_cxx() && DECL_USE_TEMPLATE(state->decl))
      XIL_PrintTemplateInfo(file, state->decl);
  }

  if (state->decl && TREE_CODE(state->decl) == VAR_DECL) {
    // add the global variable itself to the annotation.
    tree type = TREE_TYPE(state->decl);
    const char *name = XIL_SourceName(state->decl);
    const char *full_name = XIL_GlobalName(state->decl);
    fprintf(file, "__attribute__((annot_global(\"%s\"))) extern\n", full_name);
    XIL_PrintDeclaration(file, type, name);
    fprintf(file, ";\n");
  }

  if (state->locals) {
    // add any local variables in scope to the annotation.
    int ind = 0;
    for (; state->locals[ind]; ind++) {
      struct XIL_LocalData *local = state->locals[ind];

      tree type = TREE_TYPE(local->decl);
      XIL_Var xil_decl = XIL_TranslateVar(local->decl);
      const char *local_full_name = XIL_GetVarName(xil_decl);
      const char *local_name = IDENTIFIER_POINTER(DECL_NAME(local->decl));

      fprintf(file, "__attribute__((annot_local(\"%s\"))) extern\n",
              local_full_name);
      XIL_PrintDeclaration(file, type, local_name);
      fprintf(file, ";\n");
      local = local->scope_next;
    }
  }

  if (!c_dialect_cxx() && state->type) {
    // type invariant on a C structure. since this is not a member function
    // the fields are not in scope. make a 'this' variable and individual
    // variables for each field, so that C++-like syntax works.
    fprintf(file, "__attribute__((annot_this_var(0)))\n");
    XIL_PrintStructPrefix(file, state->type);
    fprintf(file, "__this *this;\n");

    tree field = TYPE_FIELDS(state->type);
    while (field) {
      if (TREE_CODE(field) == FIELD_DECL && DECL_NAME(field)) {
        const char *name = IDENTIFIER_POINTER(DECL_NAME(field));

        fprintf(file, "__attribute__((annot_this_var(1)))\n");
        XIL_PrintDeclaration(file, TREE_TYPE(field), name);
        fprintf(file, ";\n");
      }
      field = TREE_CHAIN(field);
    }
  }

  // print any namespace 'using' declarations.
  struct XIL_AnnotationNamespace *namespc = state->namespaces;
  while (namespc) {
    fprintf(file, "using namespace ");
    XIL_PrintBaseContext(file, namespc->context);
    fprintf(file, ";\n");
    namespc = namespc->next;
  }

  fprintf(file, "int __value__ = 0 != (%s);\n", state->text);
  fprintf(file, "}\n");
}

// maximum number of times we will try to recompile an annotation file
// before giving up.
#define PROCESS_MAX_TRIES 8

// process an annotation either from an attribute or read in from a file.
void XIL_ProcessAnnotation(tree node, XIL_PPoint *point, bool all_locals,
                           XIL_Location loc, XIL_AnnotationKind annot_kind,
                           const char *point_text, const char *annot_text)
{
  gcc_assert(xil_plugin_path);
  if (!xil_gcc_path) {
    fprintf(xil_log,
      "ERROR: Can't process annotation without -fplugin-arg-xgill-gcc\n");
    return;
  }

  // get the class, name and target of the annotation.
  const char *annot_class = NULL;
  char *annot_name = xmalloc(strlen(annot_text) + 100);
  XIL_Var annot_var = NULL;
  bool annot_type = false;

  // get the purpose of the annotation, the same as from an attribute.
  const char *purpose = NULL;

#define XIL_CHECK_ATTR(_, STR, VALUE)                   \
    if (annot_kind == VALUE) purpose = STR;
  XIL_ITERATE_ANNOT(XIL_CHECK_ATTR)
#undef XIL_CHECK_ATTR

  gcc_assert(purpose);

  if (TREE_CODE(node) == FUNCTION_DECL) {
    annot_class = "func";

    if (point) {
      // distinguish annotations at points in the function by a count, not just
      // the syntax. there may be multiple intermediate asserts with the same
      // text but different meanings (i.e. duplicate local variables).
      xil_active_env.annot_count++;
      sprintf(annot_name, "%s:%d:(%s)", purpose,
              xil_active_env.annot_count, annot_text);
    }
    else {
      sprintf(annot_name, "%s:(%s)", purpose, annot_text);
    }

    annot_var = XIL_TranslateVar(node);
  }
  else if (TREE_CODE(node) == VAR_DECL) {
    annot_class = "init";
    sprintf(annot_name, "%s:(%s)", purpose, annot_text);
    annot_var = XIL_TranslateVar(node);
  }
  else if (TREE_CODE(node) == RECORD_TYPE ||
           TREE_CODE(node) == UNION_TYPE) {
    annot_class = "comp";
    sprintf(annot_name, "%s:(%s)", purpose, annot_text);

    const char *csu_name = XIL_CSUName(node, NULL);
    gcc_assert(csu_name);

    annot_var = XIL_VarGlob(csu_name, csu_name);
    annot_type = true;
  }

  if (point) {
    XIL_PPoint after_point = XIL_CFGAddPoint(loc);
    XIL_CFGEdgeAnnotation(*point, after_point, annot_name);
    *point = after_point;
  }

  if (XIL_HasAnnotation(annot_var, annot_name, annot_type)) {
    // we've seen this annotation before, don't need to process it again.
    return;
  }

  fprintf(xil_log, "Annotation: %s: %s: %s\n",
          XIL_GetVarName(annot_var), purpose, annot_text);

  // get a temporary file for the annotation contents.
  int file_len = xil_log_directory ? strlen(xil_log_directory) + 20 : 20;
  char *annotation_file = xmalloc(file_len);

  if (xil_log_directory)
    sprintf(annotation_file, "%s/tmp.XXXXXX", xil_log_directory);
  else
    strcpy(annotation_file, "tmp.XXXXXX");
  mktemp(annotation_file);

  char *out_file = xmalloc(strlen(annotation_file) + 10);
  sprintf(out_file, "%s.out", annotation_file);

  char *object_file = xmalloc(strlen(annotation_file) + 10);
  sprintf(object_file, "%s.o", annotation_file);

  // add the proper extension to the annotation source file.
  strcat(annotation_file, c_dialect_cxx() ? ".cc" : ".c");

  struct XIL_AnnotationState *nstate =
    xcalloc(1, sizeof(struct XIL_AnnotationState));
  nstate->name = annot_name;
  nstate->text = annot_text;
  nstate->prev = state;
  state = nstate;

  if (annot_type) {
    state->type = node;
  }
  else {
    state->decl = node;

    // set the structure type for methods and other declarations inside a type.
    tree context = DECL_CONTEXT(node);
    if (context) {
      if (TREE_CODE(context) == RECORD_TYPE ||
          TREE_CODE(context) == UNION_TYPE)
        state->type = context;
    }
  }

  // get the base plugin arguments.
  char plugin_buf[1024];
  if (xil_remote_address)
    sprintf(plugin_buf, "%s -c -fplugin=%s -fplugin-arg-xgill-remote=%s",
            xil_gcc_path, xil_plugin_path, xil_remote_address);
  else
    sprintf(plugin_buf, "%s -c -fplugin=%s", xil_gcc_path, xil_plugin_path);

  // get the entire command to run.
  char system_buf[2048];
  sprintf(system_buf,
          "%s -fplugin-arg-xgill-annot=%s:%s %s -o %s > /dev/null 2> %s",
          plugin_buf, annot_class, purpose,
          annotation_file, object_file, out_file);

  fprintf(xil_log, "%s\n", system_buf);

  if (state->decl && TREE_CODE(state->decl) == FUNCTION_DECL) {
    // scan for any structs/typedefs used in parameter/return vars.
    tree param = DECL_ARGUMENTS(state->decl);

    if (!param) {
      struct XIL_ParamDecl *param_decl = xil_pending_param_decls;
      while(param_decl) {
        XIL_ScanDefineType(TREE_TYPE(param_decl->decl));
        param_decl = param_decl->next;
      }
    }

    while (param) {
      XIL_ScanDefineType(TREE_TYPE(param));
      param = TREE_CHAIN(param);
    }

    tree result_type = TREE_TYPE(TREE_TYPE(state->decl));
    if (TREE_CODE(result_type) != VOID_TYPE)
      XIL_ScanDefineType(result_type);

    if (c_dialect_cxx() && DECL_USE_TEMPLATE(state->decl))
      XIL_ScanTemplateInfo(state->decl);

// maximum number of locals we will consider for a function.
#define MAX_LOCALS 500

    // also look at local vars for intermediate assertions.
    if (point || all_locals) {
      state->locals = xcalloc(MAX_LOCALS + 1, sizeof(struct XIL_LocalData*));
      int ind = 0;

      if (point) {
        // get all local variables in scope.
        struct XIL_ScopeEnv *scope = xil_active_scope;
        while (scope) {
          struct XIL_LocalData *local = scope->locals;
          while (local) {
            if (ind == MAX_LOCALS)
              break;

            state->locals[ind++] = local;
            XIL_ScanDefineType(TREE_TYPE(local->decl));
            local = local->scope_next;
          }
          scope = scope->parent;
        }
      }
      else {
        // get all local variables for the entire function. this is only used
        // for web interface annotations; it would be nice to fix this so
        // that we don't get confused if multiple locals share the same name,
        // but I don't see an easy way of doing so.

        struct XIL_LocalData *local = xil_active_env.locals;
        while (local) {
          if (ind == MAX_LOCALS)
            break;

          state->locals[ind++] = local;
          XIL_ScanDefineType(TREE_TYPE(local->decl));
          local = local->block_next;
        }
      }
    }
  }

  if (state->decl && TREE_CODE(state->decl) == VAR_DECL) {
    // scan the type of the global variable itself.
    XIL_ScanDefineType(TREE_TYPE(state->decl));
  }

  if (state->type) {
    // scan and add a definition for the type containing the annotation.
    if (c_dialect_cxx())
      XIL_ScanPrintType(state->type, true);
    XIL_ScanDefineType(state->type);
  }

  // message to associate with the annotation if we fail to process it.
  char error_buf[1024];

  int tries = 0;
  for (; tries < PROCESS_MAX_TRIES; tries++) {
    FILE *file_out = fopen(annotation_file, "w");
    if (!file_out) {
      sprintf(error_buf, "Could not write to annotation file");
      break;
    }

    WriteAnnotationFile(file_out);
    fclose(file_out);

    int res = system(system_buf);
    remove(object_file);

    if (res == 0) {
      // successfully processed the annotation file.
      XIL_ClearAssociate(XIL_AscAnnotate);

      state = state->prev;
      return;
    }

    // parse the first error from the output file. this is the text
    // from an 'error:' to the end of that line.
    FILE *out_read = fopen(out_file, "r");

    static char file_contents[1024 * 1024];
    if (out_read) {
      int count = fread(file_contents, 1, sizeof(file_contents) - 1, out_read);
      file_contents[count] = 0;
    }

    if (!out_read || ferror(out_read) || !feof(out_read)) {
      sprintf(error_buf, "Could not read annotation output");
      if (out_read)
        fclose(out_read);
      break;
    }
    fclose(out_read);

    char *error_message = NULL;

    char *pos = file_contents;
    while (*pos) {
      if (!strncmp(pos,"error: ",7)) {
        error_message = pos + 7;
        char *line_end = strchr(pos,'\n');
        if (line_end) *line_end = 0;
        break;
      }
      pos++;
    }

    if (!error_message) {
      sprintf(error_buf, "Did not get error from annotation output");
      break;
    }

    bool success = XIL_ProcessAnnotationError(error_message);
    if (!success) {
      // found an error but couldn't process it. give up.
      sprintf(error_buf, "Compiler message: %s", error_message);
      break;
    }

    remove(out_file);
  }

  if (tries == PROCESS_MAX_TRIES)
    sprintf(error_buf, "Tries threshold reached for annotation");

  // log the error message.
  fprintf(xil_log, "ERROR: %s\n\n", error_buf);

  // write a separate file with the error message for web annotations.
  if (xil_annotation_single) {
    FILE *xil_annot = fopen(xil_annotation_single, "w");
    fprintf(xil_annot, "%s\n", error_buf);
    fclose(xil_annot);
  }

  // there isn't any location information available for attributes.
  XIL_Location error_loc = XIL_MakeLocation("<error>", 0);

  // make an annotation CFG so we remember this later (and don't try again
  // in another translation unit).
  XIL_AddAnnotationMsg(annot_var, annot_name, annot_kind, annot_type,
                       error_loc, error_buf);

  state = state->prev;
  XIL_ClearAssociate(XIL_AscAnnotate);
}

bool XIL_ProcessAnnotationAttr(tree node, tree attr, XIL_PPoint *point,
                               XIL_Location loc)
{
  const char *annot_text = NULL;
  const char *purpose = XIL_DecodeAttribute(attr, &annot_text, NULL);

  if (!purpose)
    return false;

  // figure out the kind of annotation, if this is an annotation.
  XIL_AnnotationKind annot_kind = 0;

#define XIL_CHECK_ATTR(_, STR, VALUE)                   \
    if (!strcmp(purpose, STR)) annot_kind = VALUE;
  XIL_ITERATE_ANNOT(XIL_CHECK_ATTR)
#undef XIL_CHECK_ATTR

  if (!annot_kind)
    return false;

  // make sure annotations which expect a program point are attached to one,
  // and annotations which don't expect a point aren't. annotations not meeting
  // these criteria are silently dropped; in the future we should warn.

  bool expect_point = false;
  if (annot_kind == XIL_AK_Assert || annot_kind == XIL_AK_Assume ||
      annot_kind == XIL_AK_AssertRuntime)
    expect_point = true;

  if (expect_point && !point) return true;
  if (!expect_point && point) return true;

  if (!annot_text) {
    TREE_UNEXPECTED(attr);
    return true;
  }

  XIL_ProcessAnnotation(node, point, false, loc, annot_kind,
                        NULL, annot_text);
  return true;
}

void XIL_ProcessAnnotationRead(tree node, const char *where,
                               const char *point_text, const char *annot_text,
                               bool trusted)
{
  XIL_AnnotationKind annot_kind = 0;
  bool all_locals = false;

  if (!strcmp(where, "pre")) {
    annot_kind = trusted ? XIL_AK_PreconditionAssume : XIL_AK_Precondition;
  }
  else if (!strcmp(where, "post")) {
    annot_kind = trusted ? XIL_AK_PostconditionAssume : XIL_AK_Postcondition;
  }
  else if (!strncmp(where, "loop", 4)) {
    annot_kind = trusted ? XIL_AK_Assume : XIL_AK_Assert;
    all_locals = true;
  }
  else if (!strcmp(where, "global") || !strcmp(where, "type")) {
    annot_kind = trusted ? XIL_AK_InvariantAssume : XIL_AK_Invariant;
  }

  if (point_text) {
    annot_kind = trusted ? XIL_AK_Assume : XIL_AK_Assert;
    all_locals = true;
  }

  XIL_ProcessAnnotation(node, NULL, all_locals, NULL, annot_kind,
                        point_text, annot_text);
}
