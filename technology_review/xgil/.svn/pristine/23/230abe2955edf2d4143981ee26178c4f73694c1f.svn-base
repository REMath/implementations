
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

XIL_Type XIL_TranslateIntType(tree type)
{
  int bits = TYPE_SIZE(type) ?
    TREE_UINT(TYPE_SIZE(type)) : TYPE_PRECISION(type);
  int bytes = bits / 8;

  if (!bytes || bytes * 8 != bits)
    TREE_UNEXPECTED(type);

  int sign = !(TYPE_UNSIGNED(type));
  return XIL_TypeInt(bytes, sign);
}

XIL_Type XIL_TranslateRealType(tree type)
{
  int bits = TYPE_PRECISION(type);
  int bytes = bits / 8;

  if (!bytes || bytes * 8 != bits)
    TREE_UNEXPECTED(type);

  return XIL_TypeFloat(bytes);
}

XIL_Type XIL_TranslatePointerType(tree type)
{
  // get the width of the pointer.
  tree size = TYPE_SIZE_UNIT(type);
  int bytes = TREE_UINT(size);

  if (bytes != xil_pointer_width) {
    TREE_UNEXPECTED(type);
    return XIL_TypeError();
  }

  tree target_type = TREE_TYPE(type);
  XIL_Type xil_target_type = XIL_TranslateType(target_type);

  return XIL_TypePointer(xil_target_type, bytes);
}

XIL_Type XIL_TranslateNullptrType(tree type)
{
  tree size = TYPE_SIZE_UNIT(type);
  int bytes = TREE_UINT(size);

  if (bytes != xil_pointer_width) {
    TREE_UNEXPECTED(type);
    return XIL_TypeError();
  }

  return XIL_TypePointer(XIL_TypeVoid(), bytes);
}

XIL_Type XIL_TranslateArrayType(tree type)
{
  tree element_type = TREE_TYPE(type);
  XIL_Type xil_element_type = XIL_TranslateType(element_type);
  int count = 0;

  tree domain = TYPE_DOMAIN(type);
  if (domain) {
    tree minval = TYPE_MIN_VALUE(domain);
    tree maxval = TYPE_MAX_VALUE(domain);
    gcc_assert(TREE_UINT(minval) == 0);

    if (maxval) {
      if (TREE_CODE(maxval) != INTEGER_CST) {
        // variable sized array. treat this as a pointer type.
        return XIL_TypePointer(xil_element_type, xil_pointer_width);
      }

      if (TREE_INT_CST_HIGH(maxval) != 0) {
        // should be negative one, which shows up for arrays explicitly
        // declared to have zero elements.
        tree size = TYPE_SIZE(type);
        gcc_assert(size && TREE_UINT(size) == 0);

        count = 0;
      }
      else {
        count = TREE_UINT(maxval) + 1;
      }
    }
    else {
      // array explicitly declared with length 0 (typically a resizable array
      // at the end of a structure).
      count = 0;
    }
  }
  else {
    // array of unknown length, e.g. extern int array[];
    // treat as having zero length. TODO: if we see a definition later we need
    // to replace the type we generated here.
    count = 0;
  }

  return XIL_TypeArray(xil_element_type, count);
}

bool XIL_IsAnonymous(tree type)
{
  // anonymous types can be structs, unions, or arrays/ptrs to structs/unions.
  if (TREE_CODE(type) == POINTER_TYPE)
    type = TREE_TYPE(type);
  while (TREE_CODE(type) == ARRAY_TYPE)
    type = TREE_TYPE(type);

  switch (TREE_CODE(type)) {
  case RECORD_TYPE:
  case UNION_TYPE:
  case QUAL_UNION_TYPE:
    break;
  default:
    return false;
  }

  // anonymous types do not have explicit names. this includes all types in
  // the C++ frontend, which have TYPE_DECLs for their names.
  tree idnode = TYPE_NAME(type);
  if (idnode && TREE_CODE(idnode) == IDENTIFIER_NODE)
    return false;

  return true;
}

bool XIL_IsAnonymousCxx(tree decl)
{
  // C++ anonymous types have fake names '._N' for some integer N
  // (the order the structure was encountered during compilation).
  if (decl && TREE_CODE(decl) == TYPE_DECL) {
    const char *name = IDENTIFIER_POINTER(DECL_NAME(decl));
    if (name[0] == '.' && name[1] == '_')
      return true;
  }

  return false;
}

bool XIL_IsSelfTypeDecl(tree decl)
{
  if (TREE_CODE(decl) != TYPE_DECL)
    return false;

  tree context = DECL_CONTEXT(decl);
  gcc_assert(context);

  if (TREE_CODE(context) != RECORD_TYPE && TREE_CODE(context) != UNION_TYPE)
    return false;

  // the self and base type declarations may not have the same fields if
  // we get here before finishing parsing the type. compare both the fields
  // and the names (names are also not sufficient if the type was typedefed).

  if (TYPE_FIELDS(context) &&
      TREE_CODE(context) == TREE_CODE(TREE_TYPE(decl)) &&
      TYPE_FIELDS(context) == TYPE_FIELDS(TREE_TYPE(decl)))
    return true;

  tree context_idnode = TYPE_NAME(context);
  if (context_idnode && DECL_NAME(context_idnode) == DECL_NAME(decl))
    return true;

  return false;
}

const char* XIL_QualifiedName(tree decl)
{
  if (TREE_CODE(decl) != TYPE_DECL && TREE_CODE(decl) != NAMESPACE_DECL) {
    TREE_UNEXPECTED(decl);
    return "<unknown>";
  }

  const char *name = IDENTIFIER_POINTER(DECL_NAME(decl));

  tree context = DECL_CONTEXT(decl);
  if (!context || TREE_CODE(context) == TRANSLATION_UNIT_DECL)
    return name;

  const char *context_name = NULL;
  if (TREE_CODE(context) == RECORD_TYPE ||
      TREE_CODE(context) == UNION_TYPE) {
    // structure nested in another structure declaration. use the outer
    // structure's name except when it is anonymous (nothing we can do for
    // these yet).
    if (XIL_IsAnonymousCxx(TYPE_NAME(context)))
      return name;
    context_name = XIL_QualifiedName(TYPE_NAME(context));

    // watch out for the inner decl in a record which contains the record
    // it defines as its context.
    if (XIL_IsSelfTypeDecl(decl))
      return context_name;
  }
  else if (TREE_CODE(context) == NAMESPACE_DECL) {
    // watch out for unnamed namespaces (?!).
    if (DECL_NAME(context) == NULL)
      return name;
    context_name = XIL_QualifiedName(context);
  }
  else if (TREE_CODE(context) == FUNCTION_DECL) {
    context_name = XIL_GlobalName(context);
  }
  else {
    TREE_UNEXPECTED(context);
    return name;
  }

  // append name to the qualified name of its context.
  char *new_name = xmalloc(strlen(context_name) + strlen(name) + 3);
  sprintf(new_name, "%s::%s", context_name, name);
  return new_name;
}

bool XIL_IsBaseField(tree field, bool *offset_zero)
{
  if (c_dialect_cxx() && DECL_NAME(field) == NULL) {
    tree type = TREE_TYPE(field);
    tree idnode = TYPE_NAME(type);
    if (TREE_CODE(type) == RECORD_TYPE && idnode &&
        TREE_CODE(idnode) == TYPE_DECL && !XIL_IsAnonymousCxx(idnode)) {
      // figure out if this field is at offset zero.
      tree offset = DECL_FIELD_OFFSET(field);
      tree bit_offset = DECL_FIELD_BIT_OFFSET(field);
      int byte_offset = TREE_UINT(offset) + (TREE_UINT(bit_offset) / 8);

      if (offset_zero)
        *offset_zero = (byte_offset == 0);
      return true;
    }
  }

  return false;
}

const char* XIL_CSUName(tree type, const char *name)
{
  if (TREE_CODE(type) == POINTER_TYPE)
    type = TREE_TYPE(type);
  while (TREE_CODE(type) == ARRAY_TYPE)
    type = TREE_TYPE(type);

  switch (TREE_CODE(type)) {
  case RECORD_TYPE:
  case UNION_TYPE:
  case QUAL_UNION_TYPE:
    break;
  default:
    return NULL;
  }

  // this is a struct/union type. associate the name we find with
  // the first field of the type, as there may be multiple different
  // instances of the containing struct/union type (all of which share
  // the same field chain).

  tree first_field = TYPE_FIELDS(type);
  if (!first_field) {
    // structure with no fields. use a name from the type if there is one
    // (it doesn't matter if we pick multiple names for this from typedefs),
    // otherwise use a default name.
    if (TYPE_NAME(type) && TREE_CODE(TYPE_NAME(type)) == TYPE_DECL)
      return IDENTIFIER_POINTER(DECL_NAME(TYPE_NAME(type)));
    return "__empty__";
  }

  XIL_Type *field_csu =
    (XIL_Type*) XIL_Associate(XIL_AscGlobal, "CSUName", first_field);

  // do some last minute checking to see if we have a better name for this
  // structure.

  // watch for an annot_global attribute for annotation processing.
  tree attr = TYPE_ATTRIBUTES(type);
  while (attr) {
    const char *new_name = NULL;
    const char *purpose = XIL_DecodeAttribute(attr, &new_name, NULL);

    if (purpose && !strcmp(purpose, "annot_global") && new_name)
      *field_csu = XIL_TypeCSU(new_name, NULL);
    attr = TREE_CHAIN(attr);
  }

  // template instantiations do not have names filled in. get one now.
  if (c_dialect_cxx() && !*field_csu && CLASSTYPE_USE_TEMPLATE(type)) {
    const char *new_name = type_as_string(type, TFF_CLASS_KEY_OR_ENUM | TFF_CHASE_TYPEDEF);
    *field_csu = XIL_TypeCSU(new_name, NULL);
  }

  // cp uses TYPE_DECLs for structures with explicit names, as the
  // 'struct name' is not necessary to ID the struct later. do the name
  // assignment now, except for the fake names on anonymous structures.
  // we need to do this now as opposed to finish_type as we can see the type
  // before it is finished in some cases.
  tree idnode = TYPE_NAME(type);
  if (c_dialect_cxx() && !*field_csu && idnode &&
      TREE_CODE(idnode) == TYPE_DECL && !XIL_IsAnonymousCxx(idnode)) {
    const char *name = XIL_QualifiedName(idnode);
    *field_csu = XIL_TypeCSU(name, NULL);
  }

  // watch for the fake structure introduced by GCC for pointer-to-member.
  // these have a first field named __pfn.
  if (!*field_csu && !name) {
    tree field_name = DECL_NAME(first_field);
    if (field_name && !strcmp(IDENTIFIER_POINTER(field_name), "__pfn"))
      *field_csu = XIL_TypeCSU("__ptr_member", NULL);
  }

  if (!*field_csu && name) {
    // this is the first time we have tried to assign a name to this
    // structure, so do the assign.
    *field_csu = XIL_TypeCSU(name, NULL);
  }

  if (*field_csu)
    return XIL_GetTypeCSUName(*field_csu);
  return NULL;
}

struct XIL_VirtualFunction* XIL_GetFunctionFields(tree type)
{
  tree decl = TYPE_FIELDS(type);
  if (!decl) return NULL;

  // keep a flag of the types we are currently getting the function fields for.
  // can't have reentrancy for this computation on the same type.
  bool *pworking = (bool*) XIL_Associate(XIL_AscGlobal, "VTableWork", decl);
  gcc_assert(!*pworking);

  struct XIL_VirtualFunction *virt = NULL;
  struct XIL_VirtualFunction **pvirt = (struct XIL_VirtualFunction**)
    XIL_Associate(XIL_AscGlobal, "VTable", decl);
  if (*pvirt) return *pvirt;

  *pworking = true;

  // get all virtual functions from base classes first. this will get the
  // original declarations which methods in type might be overriding.

  while (decl) {
    if (TREE_CODE(decl) != FIELD_DECL) {
      decl = TREE_CHAIN(decl);
      continue;
    }

    bool offset_zero;
    if (XIL_IsBaseField(decl, &offset_zero)) {
      XIL_Field base = XIL_TranslateField(decl);

      // get the function fields for this base class.
      struct XIL_VirtualFunction *bvirt =
        XIL_GetFunctionFields(TREE_TYPE(decl));

      for (; bvirt; bvirt = bvirt->next) {
        virt = xcalloc(1, sizeof(struct XIL_VirtualFunction));
        virt->next = *pvirt;
        *pvirt = virt;

        virt->base = base;
        virt->field = bvirt->field;
        virt->decl = bvirt->decl;

        // if the base is at offset zero, any entries in its vtable are at
        // the same indexes in the vtable for this class. methods from other
        // bases do not have entries in the vtable for this class unless
        // this class overrides them.
        if (offset_zero)
          virt->index = bvirt->index;
        else
          virt->index = -1;
      }
    }

    decl = TREE_CHAIN(decl);
  }

  // go through all the virtual functions from base classes and look
  // for overrides in this class, updating the entries.

  for (virt = *pvirt; virt; virt = virt->next) {
    gcc_assert(virt->decl);
    tree decl = look_for_overrides_here(type, virt->decl);
    if (!decl) continue;

    virt->decl = decl;

    // update the entry with a new vtable index, if this is overriding
    // a method from a base class not at offset zero.
    int index = TREE_UINT(DECL_VINDEX(decl));

    if (virt->index == -1)
      virt->index = index;
    else
      gcc_assert(virt->index == index);
  }

  // add entries for any virtual functions in this class that aren't inherited.

  VEC(tree,gc) *methods = CLASSTYPE_METHOD_VEC(type);
  int method_ind = 2;
  tree node = NULL;
  for (; VEC_iterate(tree,methods,method_ind,node); method_ind++) {
    while (node) {
      // the node may or may not be an overload. these handle both cases.
      tree method = OVL_CURRENT(node);
      if (TREE_CODE(method) != FUNCTION_DECL) {
        node = OVL_NEXT(node);
        continue;
      }

      if (!DECL_VIRTUAL_P(method)) {
        node = OVL_NEXT(node);
        continue;
      }

      // check if this method overrides a base class method, in which case
      // there is already an entry for it.
      bool excluded = false;
      for (virt = *pvirt; virt; virt = virt->next) {
        if (method == virt->decl)
          excluded = true;
      }
      if (excluded) {
        node = OVL_NEXT(node);
        continue;
      }

      // make an entry for this function.
      virt = xcalloc(1, sizeof(struct XIL_VirtualFunction));
      virt->next = *pvirt;
      *pvirt = virt;

      virt->field = XIL_TranslateField(method);
      virt->decl = method;
      virt->index = TREE_UINT(DECL_VINDEX(method));
      node = OVL_NEXT(node);
    }
  }

  *pworking = false;

  return *pvirt;
}

// add all data fields in the specified type to the active CSU.
void XIL_AddDataFields(tree type)
{
  tree decl = TYPE_FIELDS(type);

  while (decl) {
    if (TREE_CODE(decl) != FIELD_DECL) {
      decl = TREE_CHAIN(decl);
      continue;
    }

    // ignore the vptr field, we will need special handling for these.
    if (DECL_VIRTUAL_P(decl)) {
      decl = TREE_CHAIN(decl);
      continue;
    }

    // mark any annotation attributes on the field as needing processing once
    // we are done with the block.
    tree attr = DECL_ATTRIBUTES(decl);
    while (attr) {
      struct XIL_PendingAnnotation *pending = xcalloc(1, sizeof(struct XIL_PendingAnnotation));
      pending->type = type;
      pending->attr = attr;
      pending->next = xil_active_env.annots;
      xil_active_env.annots = pending;
      attr = TREE_CHAIN(attr);
    }

    // compute the byte offset of the field into the structure.
    tree offset = DECL_FIELD_OFFSET(decl);
    tree bit_offset = DECL_FIELD_BIT_OFFSET(decl);
    int byte_offset = TREE_UINT(offset) + (TREE_UINT(bit_offset) / 8);

    XIL_Field field = XIL_TranslateField(decl);
    XIL_CSUAddDataField(field, byte_offset);

    decl = TREE_CHAIN(decl);
  }
}

int xil_generate_record_types = 1;

XIL_Type XIL_TranslateRecordType(tree type)
{
  static XIL_Type error_csu;
  if (!error_csu) error_csu = XIL_TypeCSU("error", NULL);

  // get the name to use for the CSU.
  const char *name = XIL_CSUName(type, NULL);

  if (!name) {
    // no name we know of for this type. we can still get here in cp if we
    // see methods for the structure before the finish_type for the structure.
    // pick up the name at this point.
    tree idnode = TYPE_NAME(type);
    if (idnode && TREE_CODE(idnode) == TYPE_DECL) {
      tree decl_idnode = DECL_NAME(idnode);
      name = IDENTIFIER_POINTER(decl_idnode);
      XIL_CSUName(type, name);
    }

    if (!name) {
      TREE_UNEXPECTED(type);
      return error_csu;
    }
  }

  // figure out whether we will want to try to fill in this CSU.
  int generate = 0;
  int *pgenerate = &generate;

  // don't generate CSU types from annotation files.
  if (xil_has_annotation)
    pgenerate = NULL;

  // don't generate CSU types if we already had unrecognized trees, so we don't
  // confuse errors arising in different CSUs or functions.
  if (xil_active_env.dropped)
    pgenerate = NULL;

  // don't generate the CSU if its type is incomplete, no known size.
  // wait until the size has been filled in and the complete type is there.
  tree size = TYPE_SIZE_UNIT(type);
  if (size == NULL)
    pgenerate = NULL;

  if (!xil_generate_record_types)
    pgenerate = NULL;

  // don't try to generate CSU types for fake type structures used for
  // structures containing virtual functions. there doesn't seem to be a better
  // way to identify these.
  static const char *bad_prefix_list[] = {
    "const __class_type_info_pseudo",
    "const __si_class_type_info_pseudo",
    "const __vmi_class_type_info_pseudo",
    "__type_info_pseudo",
    NULL
  };
  int ind;
  for (ind = 0; bad_prefix_list[ind]; ind++) {
    const char *bad_prefix = bad_prefix_list[ind];
    if (!strncmp(name, bad_prefix, strlen(bad_prefix)))
      pgenerate = NULL;
  }

  XIL_Type xil_csu_type = XIL_TypeCSU(name, pgenerate);

  if (!generate)
    return xil_csu_type;

  XIL_PushActiveCSU(name);

  // fill in the fields and other information about the CSU.

  switch (TREE_CODE(type)) {
  case RECORD_TYPE:
    XIL_CSUSetKind(XIL_CSU_Struct); break;
  case UNION_TYPE:
  case QUAL_UNION_TYPE:
    XIL_CSUSetKind(XIL_CSU_Union); break;
  default:
    TREE_UNEXPECTED(type);
    return xil_csu_type;
  }

  if (xil_command)
    XIL_CSUSetCommand(xil_command);

  // we don't have location information for CSUs yet, use an empty one.
  XIL_Location empty_loc = XIL_MakeLocation("<empty>", 0);
  XIL_CSUSetBeginLocation(empty_loc);
  XIL_CSUSetEndLocation(empty_loc);
  XIL_CSUSetWidth(TREE_UINT(size));

  XIL_AddDataFields(type);

  // add any virtual functions to the type.
  if (c_dialect_cxx()) {
    // first generate types for all virtual methods in this class.
    // the function fields need to be able to get types for these methods
    // without triggering a reentrant generation for a record type.
    VEC(tree,gc) *methods = CLASSTYPE_METHOD_VEC(type);
    int method_ind = 2;
    tree node = NULL;
    for (; VEC_iterate(tree,methods,method_ind,node); method_ind++) {
      while (node) {
        // the node may or may not be an overload. these handle both cases.
        tree method = OVL_CURRENT(node);
        if (TREE_CODE(method) == FUNCTION_DECL && DECL_VIRTUAL_P(method))
          XIL_TranslateType(TREE_TYPE(method));
        node = OVL_NEXT(node);
      }
    }

    // add function fields for each virtual method in the type.
    struct XIL_VirtualFunction *virt = XIL_GetFunctionFields(type);

    for (; virt; virt = virt->next) {
      XIL_Var var = NULL;
      if (!DECL_PURE_VIRTUAL_P(virt->decl))
        var = XIL_TranslateVar(virt->decl);

      XIL_CSUAddFunctionField(virt->field, virt->base, var);
    }
  }

  // process any annotation attributes on the type.
  tree attr = TYPE_ATTRIBUTES(type);
  while (attr) {
    XIL_ProcessAnnotationAttr(type, attr, NULL, NULL);
    attr = TREE_CHAIN(attr);
  }

  // process any annotations read in from file for the type.
  int count = XIL_GetAnnotationCount(name, false, true);
  for (ind = 0; ind < count; ind++) {
    const char *where;
    const char *point_text, *annot_text;
    int trusted;
    XIL_GetAnnotation(name, false, true, ind, &where,
                      &point_text, &annot_text, &trusted);
    XIL_ProcessAnnotationRead(type, where, point_text, annot_text, trusted);
  }

  XIL_PopActiveCSU(xil_active_env.dropped);

  // if we had trouble processing this type then don't let that leak back
  // into the function which this was generated from.
  xil_active_env.dropped = 0;

  return xil_csu_type;
}

XIL_Type XIL_TranslateFunctionType(tree type)
{
  tree return_type = TREE_TYPE(type);
  XIL_Type xil_return_type = XIL_TranslateType(return_type);

  // method types have a 'this' type, which also appears as the first
  // entry in the arguments list.
  const char *this_csu = NULL;
  bool skip_argument = false;

  if (TREE_CODE(type) == METHOD_TYPE) {
    tree base_type = TYPE_METHOD_BASETYPE(type);
    XIL_Type xil_base_type = XIL_TranslateType(base_type);
    this_csu = XIL_GetTypeCSUName(xil_base_type);
    if (!this_csu) {
      TREE_UNEXPECTED(type);
      return XIL_TypeError();
    }
    skip_argument = true;
  }

  XIL_Type *arg_array = NULL;
  int arg_capacity = 0;
  int arg_count = 0;
  tree arg_types = TYPE_ARG_TYPES(type);

  // get all the argument types.
  while (arg_types) {
    gcc_assert(TREE_CODE(arg_types) == TREE_LIST);

    tree arg_type = TREE_VALUE(arg_types);
    arg_types = TREE_CHAIN(arg_types);

    // make sure we skip the first argument for method types.
    if (skip_argument) {
      skip_argument = false;
      continue;
    }

    if (TREE_CODE(arg_type) == VOID_TYPE) {
      // for functions in C the last element in the tree seems to be a fake
      // argument of type void. just ignore this.
      gcc_assert(arg_types == NULL);
      break;
    }

    if (arg_count == arg_capacity) {
      arg_capacity += 4;
      arg_array = xrealloc(arg_array, sizeof(XIL_Type) * arg_capacity);
    }

    XIL_Type xil_arg_type = XIL_TranslateType(arg_type);
    arg_array[arg_count++] = xil_arg_type;
  }

  return XIL_TypeFunction(xil_return_type, this_csu, 0, arg_array, arg_count);
}

XIL_Type generate_TranslateType(tree type)
{
  switch (TREE_CODE(type)) {

  case VOID_TYPE:
    return XIL_TypeVoid();

  case BOOLEAN_TYPE:
  case INTEGER_TYPE:
  case ENUMERAL_TYPE:
    return XIL_TranslateIntType(type);

  case REAL_TYPE:
    return XIL_TranslateRealType(type);

  case POINTER_TYPE:
  case REFERENCE_TYPE:
    return XIL_TranslatePointerType(type);

  case NULLPTR_TYPE:
    return XIL_TranslateNullptrType(type);

  case ARRAY_TYPE:
    return XIL_TranslateArrayType(type);

  case RECORD_TYPE:
  case UNION_TYPE:
  case QUAL_UNION_TYPE:
    return XIL_TranslateRecordType(type);

  case FUNCTION_TYPE:
  case METHOD_TYPE:
    return XIL_TranslateFunctionType(type);

  // type used for pointer-to-member.
  case OFFSET_TYPE:
    TREE_BOGUS();
    return XIL_TypeError();

  // vectors of primitive types.
  case VECTOR_TYPE:
    TREE_BOGUS();
    return XIL_TypeError();

  // complex numbers.
  case COMPLEX_TYPE:
    TREE_BOGUS();
    return XIL_TypeError();

  default:
    TREE_UNEXPECTED(type);
    return XIL_TypeError();
  }
}

XIL_Field generate_TranslateField(tree decl)
{
  static XIL_Field error_field = NULL;
  if (!error_field)
    error_field = XIL_MakeField("error", "error", "error", XIL_TypeError(), 0);

  bool is_func;
  if (TREE_CODE(decl) == FIELD_DECL)
    is_func = false;
  else if (TREE_CODE(decl) == FUNCTION_DECL)
    is_func = true;
  else
    gcc_unreachable();

  // get the CSU this field belongs to.

  tree csu_type = DECL_CONTEXT(decl);
  XIL_Type xil_csu_type = XIL_TranslateType(csu_type);

  const char *csu_name = XIL_GetTypeCSUName(xil_csu_type);
  if (!csu_name) {
    TREE_UNEXPECTED(decl);
    return error_field;
  }

  // figure the index into the containing CSU of this field.
  // the index is zero for function fields.

  int index = 0;

  if (!is_func) {
    tree chk_decl = TYPE_FIELDS(csu_type);
    while (chk_decl) {
      if (TREE_CODE(chk_decl) != FIELD_DECL) {
        chk_decl = TREE_CHAIN(chk_decl);
        continue;
      }

      if (chk_decl == decl)
        break;

      index++;
      chk_decl = TREE_CHAIN(chk_decl);
    }
    gcc_assert(chk_decl);
  }

  // get the name of this field.

  tree idnode = DECL_NAME(decl);
  const char *name = NULL;

  if (idnode) {
    name = IDENTIFIER_POINTER(idnode);
  }
  else {
    // anonymous field. use the name 'field:index'.
    gcc_assert(!is_func);
    name = xmalloc(50);
    sprintf((char*)name, "field:%d", index);
  }

  tree type = TREE_TYPE(decl);

  // if the field's type is anonymous then use the name 'csu_name:field_name'.
  if (XIL_IsAnonymous(type)) {
    char *anon_name = xmalloc(strlen(csu_name) + strlen(name) + 2);
    sprintf(anon_name, "%s:%s", csu_name, name);
    XIL_CSUName(type, anon_name);
  }

  XIL_Type xil_type = XIL_TranslateType(type);
  return XIL_MakeField(name, name, csu_name, xil_type, is_func);
}
