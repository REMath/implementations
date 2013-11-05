// xgill.cc            see license.txt for copyright and terms of use
// utility and higher level code for xgill frontend.

#include "xgill.h"
#include "xgill_file.h"
#include <imlang/loopsplit.h>
#include <imlang/storage.h>
#include <memory/block.h>
#include <memory/summary.h>

BlockEnv *benv = NULL;

SymbolDataTable csu_symbol_table;
SymbolDataTable var_symbol_table;

static Xgill::Buffer scratch_buf;

Xgill::ConfigOption print_generated(Xgill::CK_Flag, "print-generated", NULL,
  "print out all generated types and CFGs");

Xgill::ConfigOption annotate(Xgill::CK_Flag, "annotate", NULL,
  "input file lists annotation functions for src_annotate.xdb");

Xgill::Location* GetLocation(SourceLoc loc)
{
  char const *fname = NULL;
  int line = 0, col = 0;
  sourceLocManager->decodeLineCol(loc, fname, line, col);

  Assert(fname);
  Assert(line);

  Xgill::String *file_string = Xgill::String::Make(fname);
  return Xgill::Location::Make(file_string, line);
}

// get a unique identifying string for the specified variable.
// if check_symbol_table is specified then the base file of the variable will
// be added for static variables and CSUs with duplicate definitions.
Xgill::String* GetVariableName(LocalVariableTable *local_table,
                               Variable *var, bool check_symbol_table = true)
{
  bool is_static = var->hasFlag(DF_STATIC);
  bool is_member = var->hasFlag(DF_MEMBER);
  bool is_global = IsGlobalVariable(var);
  bool is_class = var->isClass();

  // prepend static locals with 'func:' to uniquify. do this first because
  // it is reentrant and would otherwise trash the stream we create below.
  Xgill::String *base_func_name = NULL;
  if (is_static && !is_member && !is_global) {
    Assert(benv && benv->func);
    Variable *func_var = benv->func->nameAndParams->var;
    base_func_name = GetVariableName(local_table, func_var);
  }

  scratch_buf.Reset();
  Xgill::BufferOutStream out(&scratch_buf);

  if (base_func_name) {
    out << base_func_name->Value() << ":";
    base_func_name->DecRef();
  }

  // prepend non-member static functions and other globals with the filename,
  // as these names may overlap between different files or functions.
  if (is_static && !is_member && is_global) {
    Xgill::Location *loc = GetLocation(var->loc);
    out << loc->ShortFileName() << ":";
    loc->DecRef();
  }

  // same issue if there are definitions of variables with the same name in
  // other compilation units that we need to avoid conflict with.
  if (check_symbol_table && !is_static && (is_global || is_class)) {
    SymbolDataTable &table = is_class ? csu_symbol_table : var_symbol_table;
    Xgill::Vector<SymbolData> *entries = table.Lookup(var, false);

    if (entries) {
      Assert(entries->Size() == 1);
      const SymbolData &data = entries->At(0);

      if (data.duplicate_analyzed) {
        Xgill::Location *loc = GetLocation(var->loc);
        out << loc->ShortFileName() << ":";
        loc->DecRef();
      }
    }
  }

  out << var->fullyQualifiedName();

  // add an index string at the end to uniquify the variable if
  // it is local and there are other local variables with the same name
  // (but different scopes).
  if (local_table != NULL) {
    Xgill::Vector<Variable*> *entries = local_table->Lookup(var->name, false);
    if (entries != NULL) {
      for (size_t ind = 0; ind < entries->Size(); ind++) {
        if (var == entries->At(ind)) {
          if (ind != 0)
            out << "$" << ind;
          break;
        }
      }
    }
  }

  // add the argument types if the variable is a function to account
  // for overloading.
  if (var->type->isFunctionType()) {
    FunctionType *type = var->type->asFunctionType();

    out << "(";
    for (int ind = 0; ind < type->params.count(); ind++) {
      if (ind)
        out << ",";
      Variable *arg = type->params.nth(ind);
      out << arg->type->toString();
    }
    out << ")";
  }

  out << '\0';

  const char *cstr = (const char*) scratch_buf.base;
  return Xgill::String::Make(cstr);
}

Xgill::String* GetVariableBaseName(Variable *var)
{
  // watch for constructors.
  if (var->name && strcmp(var->name, "constructor-special") == 0) {
    if (var->scope->curCompound)
      return Xgill::String::Make(var->scope->curCompound->name);
    return NULL;
  }

  if (var->name)
    return Xgill::String::Make(var->name);
  else
    return NULL;
}

Xgill::Variable* GetVariable(Variable *var, PQName *name)
{
  if (var == NULL) {
    Assert(name);

    // this should only show up if there were some parse or type errors and
    // we could not figure out which variable is being referred to.
    // make a global variable with the name.

    Xgill::String *var_name = Xgill::String::Make(name->getName());
    return Xgill::Variable::Make(NULL, Xgill::VK_Glob, var_name, 0, NULL);
  }

  if (IsGlobalVariable(var) || var->hasFlag(DF_STATIC)) {
    Xgill::String *var_name = GetVariableName(NULL, var);
    Xgill::String *base_name = GetVariableBaseName(var);

    Xgill::VarKind var_kind;
    if (var->type->isFunctionType())
      var_kind = Xgill::VK_Func;
    else
      var_kind = Xgill::VK_Glob;

    Xgill::Variable *res =
      Xgill::Variable::Make(NULL, var_kind, var_name, 0, base_name);

    // add the definition to the CFG if we are producing the initializer
    // or CFG for the variable.
    if (benv->cfg) {
      bool add_variable = false;

      if (benv->init == var)
        add_variable = true;
      else if (benv->func && benv->func->nameAndParams->var == var)
        add_variable = true;

      if (add_variable) {
        res->IncRef();
        benv->cfg->AddVariable(res, GetType(var->type));
      }
    }

    return res;
  }

  if (var->hasFlag(DF_PARAMETER)) {
    Assert(benv->func);

    FunctionType *funcType = benv->func->funcType;
    Assert(funcType);

    int init_ind = 0;
    if (funcType->isMethod()) {
      // check for implicit 'this' parameter.
      Variable *this_arg = funcType->params.nth(0);
      if (this_arg == var) {
        Xgill::Variable *res =
          Xgill::Variable::Make(benv->GetVariableId(),
                                Xgill::VK_This, NULL, 0, NULL);

        res->IncRef();
        benv->cfg->AddVariable(res, GetType(var->type));
        return res;
      }

      init_ind = 1;
    }

    for (int ind = init_ind; ind < funcType->params.count(); ind++) {
      Variable *arg = funcType->params.nth(ind);
      if (arg == var) {
        int new_ind = ind - init_ind;

        Xgill::String *var_name = GetVariableName(NULL, var);
        Xgill::Variable *res =
          Xgill::Variable::Make(benv->GetVariableId(),
                                Xgill::VK_Arg, var_name, new_ind, NULL);

        res->IncRef();
        benv->cfg->AddVariable(res, GetType(var->type));
        return res;
      }
    }

    // we could not find the parameter. fall through and treat as a local.
    // cout << "ERROR: Could not find parameter: " << var->name << endl;
  }

  // assume this is a local variable, though there isn't a flag to check this.

  Xgill::String *var_name = GetVariableName(&benv->local_table, var);
  Xgill::Variable *res =
    Xgill::Variable::Make(benv->GetVariableId(),
                          Xgill::VK_Local, var_name, 0, NULL);

  res->IncRef();
  benv->cfg->AddVariable(res, GetType(var->type));
  return res;
}

Xgill::Type* GetType(Type *type)
{
  Assert(type);

  int bytes = 0;
  if (type->isReference()) {
    // Env::sizeofType skips over any reference, so gets the underlying
    // width which we don't want.
    bytes = POINTER_WIDTH;
  }
  else {
    benv->base_env.sizeofType(type, bytes, NULL);
  }

  switch (type->getTag()) {
  case BaseType::T_ATOMIC: {
    CVAtomicType *atype = type->asCVAtomicType();

    switch (atype->atomic->getTag()) {
    case AtomicType::T_SIMPLE: {
      SimpleType *ntype = atype->atomic->asSimpleType();

      if (ntype->type == ST_VOID)
        return Xgill::Type::MakeVoid();

      if (isFloatType(ntype->type))
        return Xgill::Type::MakeFloat(bytes);

      if (isIntegerType(ntype->type)) {
        bool sign = !isExplicitlyUnsigned(ntype->type);
        return Xgill::Type::MakeInt(bytes, sign);
      }

      return Xgill::Type::MakeError();
    }

    case AtomicType::T_COMPOUND: {
      CompoundType *ntype = atype->atomic->asCompoundType();

      Xgill::String *csu_name = GetVariableName(NULL, ntype->getTypedefVar());
      return Xgill::Type::MakeCSU(csu_name);
    }

    // TODO: assuming signed enum type.
    case AtomicType::T_ENUM:
      return Xgill::Type::MakeInt(bytes, true);

    default:
      // there was a parse/tcheck error.
      return Xgill::Type::MakeError();
    }

    Assert(false);
  }

  // pointer types.
  case BaseType::T_POINTER: {
    PointerType *ntype = type->asPointerType();
    Assert((size_t)bytes == POINTER_WIDTH);

    Xgill::Type *target_type = GetType(ntype->atType);
    return Xgill::Type::MakePointer(target_type, bytes);
  }

  case BaseType::T_REFERENCE: {
    ReferenceType *ntype = type->asReferenceType();
    Assert((size_t)bytes == POINTER_WIDTH);

    Xgill::Type *target_type = GetType(ntype->atType);
    return Xgill::Type::MakePointer(target_type, bytes);
  }

  case BaseType::T_POINTERTOMEMBER: {
    PointerToMemberType *ntype = type->asPointerToMemberType();
    Assert((size_t)bytes == POINTER_WIDTH);

    Xgill::Type *target_type = GetType(ntype->atType);
    return Xgill::Type::MakePointer(target_type, bytes);
  }

  case BaseType::T_FUNCTION: {
    FunctionType *ntype = type->asFunctionType();

    Xgill::Type *return_type = GetType(ntype->retType);
    bool varargs = ntype->acceptsVarargs();

    Xgill::Vector<Xgill::Type*> arg_types;
    Xgill::TypeCSU *csu_type = NULL;

    int ind = 0;

    if (ntype->hasFlag(FF_METHOD | FF_DTOR) && ntype->params.count() > 0) {
      // the first argument of method/dtor function types is the receiver class.
      ind++;

      Type *receiver_type = ntype->params.nth(0)->type;
      Type *base_csu_type = receiver_type->asReferenceType()->atType;

      // this might not actually be a CSU if there was a tcheck error.
      Xgill::Type *try_csu_type = GetType(base_csu_type);

      if ((csu_type = try_csu_type->IfCSU()) == NULL)
        try_csu_type->DecRef();
    }
    else if (ntype->hasFlag(FF_CTOR)) {
      // the return type is the receiver class. we are also going to use
      // void instead for the return type.

      csu_type = return_type->IfCSU();
      return_type = Xgill::Type::MakeVoid();
    }

    for (; ind < ntype->params.count(); ind++) {
      Variable *arg = ntype->params.nth(ind);
      Xgill::Type *arg_type = GetType(arg->type);
      arg_types.PushBack(arg_type);
    }

    return Xgill::Type::MakeFunction(return_type, csu_type,
                                     varargs, arg_types);
  }

  case BaseType::T_ARRAY: {
    ArrayType *ntype = type->asArrayType();
    Xgill::Type *element_type = GetType(ntype->eltType);

    if (ntype->size == ArrayType::DYN_SIZE) {
      // dynamically sized arrays are special cased and converted to
      // a pointer to the element type. when these arrays are declared
      // a call to alloca() is inserted.
      return Xgill::Type::MakePointer(element_type, POINTER_WIDTH);
    }

    size_t element_count;
    if (ntype->size == ArrayType::NO_SIZE) {
      element_count = 0;
    }
    else {
      element_count = (size_t) ntype->size;
    }

    return Xgill::Type::MakeArray(element_type, element_count);
  }

  default:
    break;
  }

  Assert(false);
  return NULL;
}

void GetTypeBits(Type *type, size_t *bits, bool *sign)
{
  Assert(type);

  switch (type->getTag()) {
  case BaseType::T_ATOMIC: {
    CVAtomicType *atype = type->asCVAtomicType();

    switch (atype->atomic->getTag()) {
    case AtomicType::T_SIMPLE: {
      SimpleType *ntype = atype->atomic->asSimpleType();

      if (isFloatType(ntype->type)) {
        *bits = simpleTypeReprSize(ntype->type) * 8;
        *sign = true;
        return;
      }

      if (isIntegerType(ntype->type)) {
        *bits = simpleTypeReprSize(ntype->type) * 8;
        *sign = !isExplicitlyUnsigned(ntype->type);
        return;
      }

      break;
    }

    case AtomicType::T_COMPOUND:
      break;

    // TODO: assuming signed enum type.
    case AtomicType::T_ENUM:
      *bits = type->reprSize() * 8;
      *sign = true;
      return;

    case AtomicType::T_TYPEVAR:
    case AtomicType::T_PSEUDOINSTANTIATION:
    case AtomicType::T_DEPENDENTQTYPE:
      // there was a parse/tcheck error.
      break;

    default:
      Assert(false);
    }

    break;
  }

  // pointer types.
  case BaseType::T_POINTER:
  case BaseType::T_REFERENCE:
  case BaseType::T_POINTERTOMEMBER:
    Assert(type->reprSize() == (int) POINTER_WIDTH);
    *bits = type->reprSize() * 8;
    *sign = false;
    return;

  case BaseType::T_FUNCTION:
  case BaseType::T_ARRAY:
    break;

  default:
    Assert(false);
  }

  // fall through for types without meaningful bits/sign.
  *bits = 0;
  *sign = true;
}

// for cases where we get confused (probably because of earlier
// parse/check errors). TODO: fix kludge.
Xgill::Field* MakeErrorField(PQName *name)
{
  Xgill::String *csu_name = Xgill::String::Make("<error>");
  Xgill::TypeCSU *csu_type = Xgill::Type::MakeCSU(csu_name);

  Xgill::String *field_name;
  if (name)
    field_name = Xgill::String::Make(name->getName());
  else
    field_name = Xgill::String::Make("<unknown>");

  Xgill::Type *field_type = Xgill::Type::MakeError();
  return Xgill::Field::Make(field_name, NULL,
                            csu_type, field_type, 0, 0, false, NULL);
}

// field is a virtual instance function. get the parent field it
// inherits from, or return itself if it is at the root of the inheritance.
Variable* GetInheritedField(Variable *field, CompoundType *type)
{
  // just get the first one we find.
  for (int base_ind = 0; base_ind < type->bases.count(); base_ind++) {
    const BaseClass *base = type->bases.nthC(base_ind);

    for (int ind = 0; ind < base->ct->functionMembers.count(); ind++) {
      Variable *parent_field = base->ct->functionMembers.nth(ind);

      // needs to be non-virtual.
      if (!parent_field->hasFlag(DF_VIRTUAL))
        continue;

      // need to have the same name.
      if (parent_field->name != field->name)
        continue;

      // need to have the same signature, except the receiver parameter
      // can have a different type with the same CV info.

      MatchFlags mflags = MF_IGNORE_RETURN | MF_IGNORE_IMPLICIT;

      FunctionType *field_type = field->type->asFunctionType();
      FunctionType *parent_type = parent_field->type->asFunctionType();

      if (field_type->equals(parent_type, mflags))
        return GetInheritedField(parent_field, base->ct);
    }

    Variable *parent_field = GetInheritedField(field, base->ct);

    if (parent_field != field)
      return parent_field;
  }

  return field;
}

Xgill::Field* GetVariableField(Variable *field, PQName *name)
{
  if (field == NULL ||
      field->scope == NULL ||
      field->scope->curCompound == NULL ||
      !field->hasFlag(DF_MEMBER)) {
    return MakeErrorField(name);
  }

  // for virtual functions we will get the field from the parent class.
  // when we fill the fields in for the type this field was redefined
  // in then we will get the name for the inherited function.
  if (field->hasFlag(DF_VIRTUAL))
    field = GetInheritedField(field, field->scope->curCompound);

  Assert(field->hasFlag(DF_MEMBER));
  CompoundType *ntype = field->scope->curCompound;

  bool is_function = false;

  // look for this field in the data members of the type.
  int index;
  for (index = 0; index < ntype->dataMembers.count(); index++) {
    if (field == ntype->dataMembers.nth(index))
      break;
  }

  if (index == ntype->dataMembers.count()) {
    is_function = true;
    index = 0;
  }

  if (is_function && field->hasFlag(DF_VIRTUAL)) {
    for (; index < ntype->functionMembers.count(); index++) {
      if (field == ntype->functionMembers.nth(index))
        break;
    }

    if (index == ntype->functionMembers.count()) {
      cout << "ERROR: Could not find member " << field->toString()
           << " within CSU " << ntype->toString() << endl;

      // cout << "Data members:" << endl;
      // for (index = 0; index < ntype->dataMembers.count(); index++)
      //   cout << ntype->dataMembers.nth(index)->toString() << endl;
      // cout << "Function members:" << endl;
      // for (index = 0; index < ntype->functionMembers.count(); index++)
      //   cout << ntype->functionMembers.nth(index)->toString() << endl;
      // cout << flush;

      return MakeErrorField(name);
    }
  }

  // TODO: not computing field offset into type.
  size_t offset = 0;

  Xgill::String *csu_name = GetVariableName(NULL, ntype->getTypedefVar());
  Xgill::TypeCSU *csu_type = Xgill::Type::MakeCSU(csu_name);

  // get the name of the field.
  Xgill::String *field_name = NULL;

  // get the appropriate name for a constructor.
  if (field->name && strcmp(field->name, "constructor-special") == 0)
    field_name = Xgill::String::Make(ntype->name);

  // special name for all destructors.
  if (field->type->isFunctionType()) {
    if (field->type->asFunctionType()->flags & FF_DTOR)
      field_name = Xgill::String::Make("~dtor");
  }

  Xgill::String *source_name = NULL;

  if (!field_name) {
    if (field->name)
      source_name = Xgill::String::Make(field->name);

    field_name = GetVariableName(NULL, field);
  }

  Xgill::Type *field_type;

  // watch for fields that are uninstantiated templates. this should only
  // occur for non-virtual methods; the best thing to do is probably leave
  // out *all* non-virtual methods from the CompositeCSU, as these are
  // not really part of the class at runtime anyways.
  TemplateInfo *ti = field->templateInfo();

  if (ti && !ti->instantiationOf) {
    field_type = Xgill::Type::MakeError();
  }
  else {
    field_type = GetType(field->type);
  }

  // get the target for non-virtual instance functions.
  Xgill::Variable *non_virtual_function = NULL;
  if (is_function && !field->hasFlag(DF_VIRTUAL))
    non_virtual_function = GetVariable(field);

  return Xgill::Field::Make(field_name, source_name, csu_type, field_type,
                            (size_t) index, offset, is_function,
                            non_virtual_function);
}

Xgill::Exp* GetNewTemporary(Xgill::Type *type)
{
  benv->temp_count++;

  scratch_buf.Reset();
  Xgill::BufferOutStream out(&scratch_buf);
  out << "__temp_" << benv->temp_count << '\0';
  const char *name_cstr = (const char*) scratch_buf.base;

  Xgill::String *name = Xgill::String::Make(name_cstr);
  Xgill::Variable *var = Xgill::Variable::Make(benv->GetVariableId(),
                                               Xgill::VK_Temp, name, 0, NULL);

  var->IncRef();
  benv->cfg->AddVariable(var, type);

  return Xgill::Exp::MakeVar(var);
}

Xgill::Exp* GetFunctionLval(const char *function)
{
  Xgill::String *func_name = Xgill::String::Make(function);
  return Xgill::Exp::MakeVar(NULL, Xgill::VK_Glob, func_name, 0, NULL);
}

// fill in data_fields and function_fields with fields from type and its
// base classes. is_base is true iff type is a base class of the type we
// are generating fields for, rather than that type itself.
void FillFields(Env &env, CompoundType *type, bool is_base,
                Xgill::Vector<Xgill::Field*> *data_fields,
                Xgill::Vector<Xgill::FunctionField> *function_fields)
{
  for (int ind = 0; ind < type->dataMembers.count(); ind++) {
    Xgill::Field *field = GetVariableField(type->dataMembers.nth(ind));

    // check for duplicate data fields. these will only show up if
    // there is diamond inheritance, which we don't really handle currently.

    bool duplicate = false;
    for (size_t dind = 0; dind < data_fields->Size(); dind++) {
      if (field == data_fields->At(dind)) {
        duplicate = true;
        break;
      }
    }
    if (duplicate) {
      field->DecRef();
      continue;
    }

    data_fields->PushBack(field);
  }

  for (int ind = 0; ind < type->functionMembers.count(); ind++) {
    Variable *field_var = type->functionMembers.nth(ind);

    if (field_var->isBuiltin)
      continue;

    // skip non-virtual functions.
    if (!field_var->hasFlag(DF_VIRTUAL))
      continue;

    FunctionType *field_type = field_var->type->asFunctionType();

    // functions we are excluding if this is a base class.
    // these are not inherited by the subclass.
    if (is_base) {
      // exclude ctors and operators for base classes.
      // TODO: is this correct for operators?
      if (field_type->flags & (FF_CTOR | FF_BUILTINOP))
        continue;

      // exclude non-virtual dtors.
      if (!field_var->hasFlag(DF_VIRTUAL) && field_type->flags & FF_DTOR)
        continue;

      // exclude assignment operator for base classes.
      if (field_var == getAssignOperator(env.str, type))
        continue;
    }

    // get any parent this field inherited from.
    Variable *parent_field_var = GetInheritedField(field_var, type);

    // TODO: is there a way to detect pure virtual functions? currently we
    // fill in the function field with a function name that will not
    // be implemented anywhere.

    // get the field from the base field and the function name from the
    // inherited field.
    Xgill::FunctionField ff;
    ff.field = GetVariableField(parent_field_var);
    ff.function = GetVariable(field_var);

    Assert(ff.field->NonVirtualFunction() == NULL);

    // check to see if the field is already in the function_fields list.
    // since we process the class from the bottom up, we will see the
    // inherited version first. TODO: same problems with diamond inheritance
    // as data members.

    bool duplicate = false;
    for (size_t find = 0; find < function_fields->Size(); find++) {
      Xgill::FunctionField &off = function_fields->At(find);

      if (ff.field == off.field) {
        duplicate = true;
        break;
      }
    }

    if (duplicate) {
      ff.field->DecRef();
      ff.function->DecRef();
    }
    else {
      function_fields->PushBack(ff);
    }
  }

  for (int ind = 0; ind < type->bases.count(); ind++) {
    const BaseClass *base = type->bases.nthC(ind);
    FillFields(env, base->ct, true, data_fields, function_fields);
  }
}

/////////////////////////////////////////////////////////////////////
// XgillSymbolVisitor
/////////////////////////////////////////////////////////////////////

bool XgillSymbolVisitor::visitTypeSpecifier(TypeSpecifier *spec)
{
  if (TS_classSpec *nspec = spec->ifTS_classSpec()) {
    CompoundType *type = nspec->ctype;

    if (!type) {
      // got confused by parse/tcheck errors.
      return false;
    }

    Variable *var = type->getTypedefVar();

    TemplateInfo *ti = var->templateInfo();
    if (ti && !ti->instantiationOf) {
      // look for instantiations of the class.
      Restorer<bool> r(inTemplate, false);

      SFOREACH_OBJLIST(Variable, ti->instantiations, iter) {
        Variable const *inst = iter.data();

        CompoundType *instCT = inst->type->asCompoundType();
        if (instCT->syntax)
          instCT->syntax->traverse(*this);
      }

      // do not traverse the uninstantiated template body.
      return false;
    }

    // note: it may be that function_depth > 0 here, it is possible to
    // declare struct/unions local to a function.

    csu_depth++;

    Xgill::Vector<SymbolData> *entries = csu_symbol_table.Lookup(var, true);

    if (entries->Empty()) {
      entries->PushBack(SymbolData());
      SymbolData &data = entries->Back();
      data.dspec = nspec;
      data.loc = spec->loc;
    }
  }

  return true;
}

void XgillSymbolVisitor::postvisitTypeSpecifier(TypeSpecifier *spec)
{
  if (spec->isTS_classSpec()) {
    Assert(csu_depth > 0);
    csu_depth--;
  }
}

bool XgillSymbolVisitor::visitFunction(Function *func)
{
  Variable *var = func->nameAndParams->var;

  // watch for unknown functions from parse/tcheck errors.
  if (!var)
    return false;

  TemplateInfo *ti = var->templateInfo();

  if (ti && !ti->instantiationOf) {
    // look for instantiations of the function.
    Restorer<bool> r(inTemplate, false);

    SFOREACH_OBJLIST(Variable, ti->instantiations, iter) {
      Variable const *inst = iter.data();
      if (inst->templateInfo()->instantiatedFunctionBody())
        inst->funcDefn->traverse(*this);
    }

    // do not traverse the uninstantiated template body.
    return false;
  }

  if (func->body == NULL) {
    // filter out functions without bodies, this can show up when
    // traversing instantiated template bodies. TODO: make sure we
    // eventually see the actual function body itself later on.
    return false;
  }

  function_depth++;

  if (benv != NULL)
    env_stack.PushBack(benv);
  benv = new BlockEnv(base_env);
  benv->func = func;

  // skip builtin functions capturing the default behavior.
  if (var->isBuiltin)
    return true;

  Xgill::Vector<SymbolData> *entries = var_symbol_table.Lookup(var, true);

  if (entries->Empty()) {
    entries->PushBack(SymbolData());
    SymbolData &data = entries->Back();
    data.dfunc = func;
    data.loc = func->getLoc();
  }

  return true;
}

void XgillSymbolVisitor::postvisitFunction(Function *func)
{
  Assert(function_depth > 0);
  function_depth--;

  Assert(benv != NULL);
  delete benv;

  if (env_stack.Empty()) {
    benv = NULL;
  }
  else {
    benv = env_stack.Back();
    env_stack.PopBack();
  }
}

bool XgillSymbolVisitor::visitDeclaration(Declaration *decl)
{
  if (decl->dflags & DF_EXTERN) {
    // mark all the variables as globals (externs inside a function body
    // are not treated as global variables. TODO: fix this inside Elsa).

    FakeList<Declarator> *decl_list = decl->decllist;
    while (decl_list != NULL) {
      Declarator *d = decl_list->first();
      decl_list = decl_list->butFirst();

      if (d->var)
        d->var->setFlag(DF_GLOBAL);
    }

    // this is a declaration so there is no more processing to do.
    return true;
  }

  FakeList<Declarator> *decl_list = decl->decllist;
  while (decl_list != NULL) {
    Declarator *d = decl_list->first();
    decl_list = decl_list->butFirst();

    Variable *var = d->var;

    // watch for missing variables or types from a parse/tcheck error.
    if (!var || !d->type)
      continue;

    // only handling global variables.
    if (!IsGlobalVariable(var) && !var->hasFlag(DF_STATIC))
      continue;

    // exclude all functions.
    if (d->type->isFunctionType())
      continue;

    // exclude typedef'ed symbols.
    if (var->hasFlag(DF_TYPEDEF))
      continue;

    // not handling variables appearing inside a class/struct definition.
    // these are declarations, not definitions.
    if (csu_depth > 0) {
      Assert(var->hasAllFlags(DF_STATIC));

      // two exceptions to consider:
      // 1. static const fields can have initializers and no later definition.
      // 2. static variables within a function definition.
      if (!d->init && function_depth == 0)
        continue;
    }

    Xgill::Vector<SymbolData> *entries = var_symbol_table.Lookup(var, true);

    if (entries->Empty()) {
      entries->PushBack(SymbolData());
      SymbolData &data = entries->Back();

      if (benv && benv->func)
        data.dfunc = benv->func;
      data.ddecl = d;
      data.loc = d->getLoc();
    }
  }

  return true;
}

/////////////////////////////////////////////////////////////////////
// SymbolDataFillTransaction
/////////////////////////////////////////////////////////////////////

void SymbolDataFillTransaction::Visit(Variable *&var,
                                      Xgill::Vector<SymbolData> &data_list)
{
  Assert(data_list.Size() == 1);
  SymbolData &data = data_list[0];
  Assert(!data.transaction_result);

  data.location_buf = new Xgill::Buffer(100);
  Xgill::BufferOutStream out(data.location_buf);

  Xgill::Location *loc = GetLocation(data.loc);
  out << loc->ShortFileName() << ":" << loc->Line() << '\0';
  loc->DecRef();

  const char *loc_str = (const char*) data.location_buf->base;

  Xgill::Buffer *name_buf = new Xgill::Buffer(100);
  t->AddBuffer(name_buf);

  Xgill::BufferOutStream name_out(name_buf);
  Xgill::String *var_name = GetVariableName(NULL, var, false);
  name_out << var_name->Value() << '\0';
  var_name->DecRef();

  const char *name_str = (const char*) name_buf->base;

  TOperand *key_op = new TOperandString(t, name_str);
  TOperand *value_op = new TOperandString(t, loc_str);

  data.transaction_result = t->MakeVariable(true);

  t->PushAction(
    Xgill::Backend::HashInsertCheck(t, hash_name, key_op, value_op,
                                    data.transaction_result));
}

/////////////////////////////////////////////////////////////////////
// SymbolDataCheckTransaction
/////////////////////////////////////////////////////////////////////

void SymbolDataCheckTransaction::Visit(Variable *&var,
                                       Xgill::Vector<SymbolData> &data_list)
{
  Assert(data_list.Size() == 1);
  SymbolData &data = data_list[0];

  TOperandList *list_res = t->LookupList(data.transaction_result);
  TOperandBoolean *exist_val = list_res->GetOperandBoolean(0);

  size_t found_index;
  for (found_index = 1; found_index < list_res->GetCount(); found_index++) {
    TOperandString *entry = list_res->GetOperandString(found_index);
    if (strcmp((const char*) data.location_buf->base,
               (const char*) entry->GetData()) == 0) {
      // found a matching index.
      break;
    }
  }

  // the entry we inserted has to be somewhere in the list.
  Assert(found_index != list_res->GetCount());

  data.previous_analyzed = exist_val->IsTrue();

  if (found_index > 1) {
    // there are multiple definitions for this name in different
    // compilation units.
    data.duplicate_analyzed = true;

    Xgill::String *var_name = GetVariableName(NULL, var, false);

    cout << "WARNING: Multiple definitions for symbol: "
         << var_name->Value() << ":";
    for (size_t index = 1; index < list_res->GetCount(); index++) {
      TOperandString *entry = list_res->GetOperandString(index);
      cout << " " << (const char*) entry->GetData();
    }
    cout << endl;

    var_name->DecRef();
  }

  // don't need the transaction data anymore.
  delete data.location_buf;
  data.location_buf = NULL;
  data.transaction_result = 0;
}

/////////////////////////////////////////////////////////////////////
// SymbolDataProcess
/////////////////////////////////////////////////////////////////////

void SymbolDataProcess::Visit(Variable *&var,
                              Xgill::Vector<SymbolData> &data_list)
{
  Assert(data_list.Size() == 1);
  SymbolData &data = data_list[0];

  if (data.previous_analyzed)
    return;

  Assert(benv == NULL);
  benv = new BlockEnv(base_env);

  const char *db_name = NULL;
  if (data.dspec != NULL) {
    Assert(!annotate.IsSpecified());
    DoTypeSpecifier(&scratch_buf, data.dspec);
    db_name = COMP_DATABASE;
  }
  else if (data.ddecl != NULL) {
    DoDeclarator(&scratch_buf, data.ddecl, data.dfunc);
    db_name = RAW_INIT_DATABASE;
  }
  else if (data.dfunc != NULL) {
    Assert(!annotate.IsSpecified());
    DoFunction(&scratch_buf, data.dfunc);
    db_name = RAW_BODY_DATABASE;
  }
  else {
    Assert(false);
  }

  delete benv;
  benv = NULL;

  if (annotate.IsSpecified()) {
    // bail out, don't update the databases directly when we're annotating.
    return;
  }

  Xgill::Buffer *name_buf = new Xgill::Buffer(100);
  t->AddBuffer(name_buf);

  Xgill::BufferOutStream name_out(name_buf);
  Xgill::String *var_name = GetVariableName(NULL, var);
  name_out << var_name->Value() << '\0';
  var_name->DecRef();

  const char *name_str = (const char*) name_buf->base;

  TOperand *key_op = new TOperandString(t, name_str);
  TOperand *value_op = TOperandString::Compress(t, &scratch_buf);
  scratch_buf.Reset();

  t->PushAction(Xgill::Backend::XdbReplace(t, db_name, key_op, value_op));

  // check the number of inserts that have been performed. if this hits the
  // threshold then submit the transaction and start fresh.

  if (t->GetActionCount() >= TRANSACTION_ADD_THRESHOLD) {
    SubmitTransaction(t);
    t->Clear();
  }
}

void SymbolDataProcess::DoTypeSpecifier(Xgill::Buffer *buf,
                                        TS_classSpec *spec)
{
  CompoundType *type = spec->ctype;

  Xgill::CSUKind kind;
  switch (type->keyword) {
  case CompoundType::K_STRUCT: kind = Xgill::CSU_Struct; break;
  case CompoundType::K_CLASS:  kind = Xgill::CSU_Class;  break;
  case CompoundType::K_UNION:  kind = Xgill::CSU_Union;  break;
  default: Assert(false);
  }

  Xgill::String *name = GetVariableName(NULL, type->getTypedefVar());
  int width = 0;

  // reprSize can throw if it gets confused.
  try {
    width = type->reprSize();
  }
  catch (xBase&) {
    cout << "ERROR: Unable to compute type width for " << name << endl;
  }

  Xgill::Location *begin_location = GetLocation(spec->loc);
  Xgill::Location *end_location = GetLocation(spec->end_loc);

  Xgill::Vector<Xgill::String*> base_classes;
  for (int ind = 0; ind < type->bases.count(); ind++) {
    const BaseClass *base = type->bases.nthC(ind);
    Xgill::String *base_name = GetVariableName(NULL, base->ct->getTypedefVar());
    base_classes.PushBack(base_name);
  }

  Xgill::Vector<Xgill::Field*> data_fields;
  Xgill::Vector<Xgill::FunctionField> function_fields;
  FillFields(base_env, type, false, &data_fields, &function_fields);

  Xgill::CompositeCSU *csu =
    Xgill::CompositeCSU::Make(kind, name, width,
                              begin_location, end_location,
                              base_classes, data_fields, function_fields);
  Xgill::CompositeCSU::Write(buf, csu);

  if (print_generated.IsSpecified()) {
    cout << "Generated CSU:" << endl;
    cout << csu << endl;
  }

  csu->DecRef();
}

void SymbolDataProcess::DoFunction(Xgill::Buffer *buf, Function *func)
{
  Xgill::Variable *function_var = GetVariable(func->nameAndParams->var);

  Xgill::BlockKind kind = Xgill::B_FunctionWhole;
  Xgill::BlockId *function_id = Xgill::BlockId::Make(kind, function_var);

  Xgill::Location *begin_location = GetLocation(func->getLoc());
  Xgill::Location *end_location = GetLocation(func->body->end_loc);

  Xgill::BlockCFG *cfg = Xgill::BlockCFG::Make(function_id);
  cfg->SetBeginLocation(begin_location);
  cfg->SetEndLocation(end_location);

  begin_location->IncRef();
  PPoint entry_point = cfg->AddPoint(begin_location);
  cfg->SetEntryPoint(entry_point);

  end_location->IncRef();
  PPoint exit_point = cfg->AddPoint(end_location);
  cfg->SetExitPoint(exit_point);

  benv->func = func;
  benv->cfg = cfg;

  // we need to ensure the CFG's definition contains variables for
  // the function itself, all its arguments and the 'this' parameter
  // (if present). make and discard a variable for each of these to
  // force the insertion.

  Xgill::Variable *decl_var = GetVariable(func->nameAndParams->var);
  decl_var->DecRef();

  FunctionType *funcType = func->funcType;
  Assert(funcType);

  // this will capture both the parameters and any 'this' if there is one.
  for (int ind = 0; ind < funcType->params.count(); ind++) {
    Variable *arg = funcType->params.nth(ind);
    Xgill::Variable *arg_var = GetVariable(arg);
    arg_var->DecRef();
  }

  // fill in the CFG from the function body itself.

  ProcessFunctionBody(func);

  Xgill::BlockCFG::Write(buf, cfg);

  if (print_generated.IsSpecified()) {
    cout << "Generated CFG:" << endl;
    cout << cfg << endl;
  }

  cfg->DecRef();
}

// when handling annotations, store the annotation name string and annotated
// expression as retrieved during parsing.
Xgill::DataString *g_annot_name = NULL;
Xgill::Bit *g_annot_bit = NULL;

void SymbolDataProcess::DoDeclarator(Xgill::Buffer *buf,
                                     Declarator *decl, Function *func)
{
  benv->func = func;
  benv->init = decl->var;

  Xgill::Variable *init_var = GetVariable(decl->var);
  Xgill::BlockId *init_id =
    Xgill::BlockId::Make(Xgill::B_Initializer, init_var);

  Xgill::Location *begin_location = GetLocation(decl->getLoc());
  Xgill::Location *end_location;
  if (decl->init != NULL) {
    end_location = GetLocation(decl->init->end_loc);
  }
  else {
    begin_location->IncRef();
    end_location = begin_location;
  }

  Xgill::BlockCFG *cfg = Xgill::BlockCFG::Make(init_id);
  cfg->SetBeginLocation(begin_location);
  cfg->SetEndLocation(end_location);

  begin_location->IncRef();
  PPoint entry_point = cfg->AddPoint(begin_location);
  cfg->SetEntryPoint(entry_point);

  benv->cfg = cfg;

  // force insertion of the variable into the CFG's definitions.
  Xgill::Variable *decl_var = GetVariable(decl->var);
  decl_var->DecRef();

  PPoint exit_point = entry_point;
  ProcessDeclarator(&exit_point, decl);

  end_location->IncRef();
  cfg->SetPointLocation(exit_point, end_location);
  cfg->SetExitPoint(exit_point);

  if (annotate.IsSpecified()) {
    const char *name = init_var->GetName()->Value();
    if (strcmp(name, "__name__") == 0) {
      Assert(g_annot_name == NULL);

      // the CFG should be a single assignment of a constant string.
      Assert(cfg->GetEdgeCount() == 1);
      Xgill::PEdgeAssign *edge = cfg->GetEdge(0)->AsAssign();

      Xgill::Exp *rhs = edge->GetRightSide();

      // skip any coercion
      if (Xgill::ExpUnop *nrhs = rhs->IfUnop())
        rhs = nrhs->GetOperand();

      g_annot_name = rhs->AsString()->GetString();
      g_annot_name->IncRef(&g_annot_name);
    }
    else if (strcmp(name, "__value__") == 0) {
      Assert(g_annot_bit == NULL);

      // translation of the annotated expression may introduce temporaries if,
      // for example, the '?', '||' or '&&' operators are used. make a
      // BlockMemory for the CFG so we can fold all these assigns together.

      // first cleanup the CFG to remove skips and get a topo order on points.
      Xgill::Vector<Xgill::BlockCFG*> split_cfgs;
      SplitLoops(cfg, &split_cfgs);
      Assert(split_cfgs.Size() == 1 && split_cfgs[0] == cfg);

      init_id->IncRef();
      Xgill::BlockMemory *mcfg = Xgill::BlockMemory::Make(init_id,
        Xgill::MSIMP_Default, Xgill::MALIAS_Default, Xgill::MCLB_Default);

      mcfg->SetCFG(cfg);
      mcfg->ComputeTables();

      init_var->IncRef();
      Xgill::Exp *value_exp = Xgill::Exp::MakeVar(init_var);
      Xgill::Exp *value_drf = Xgill::Exp::MakeDrf(value_exp);
      Xgill::Bit *value_bit = Xgill::Exp::MakeNonZeroBit(value_drf);

      mcfg->TranslateBit(Xgill::TRK_Point, exit_point, value_bit, &g_annot_bit);
      Assert(g_annot_bit);

      value_drf->DecRef();
      value_bit->DecRef();
      mcfg->DecRef();
    }
    else {
      Assert(false);
    }
  }
  else {
    Xgill::BlockCFG::Write(buf, cfg);

    if (print_generated.IsSpecified()) {
      cout << "Generated initializer CFG:" << endl;
      cout << cfg << endl;
    }
  }

  cfg->DecRef();
}

void ProcessAnnotation()
{
  if (!g_annot_name || !g_annot_bit) {
    // we should have already reported errors when trying to generate these.
    return;
  }

  const char *name = (const char*) g_annot_name->Value();
  size_t name_len = g_annot_name->ValueLength();

  // make sure we got a NULL terminated string.
  Assert(name_len && name[name_len - 1] == '\0');

  Xgill::BlockSummary::ProcessAnnotation(name, g_annot_bit);
}
