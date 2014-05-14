// variable.cc            see license.txt for copyright and terms of use
// code for variable.h

#include "variable.h"      // this module
#include "template.h"      // Type, TemplateInfo, etc.
#include "trace.h"         // tracingSys


string toXml_Variable_intData(unsigned id) {
  return stringc << static_cast<int>(id);
}

void fromXml_Variable_intData(unsigned &out, rostring str) {
  out = static_cast<DeclFlags>(atoi(str));
}


// ---------------------- SomeTypeVarNotInTemplParams_Pred --------------------

// existential search for a type variable that is not in the template
// parameters
class SomeTypeVarNotInTemplParams_Pred : public TypePred {
  TemplateInfo *ti;
  public:
  SomeTypeVarNotInTemplParams_Pred(TemplateInfo *ti0) : ti(ti0) {}
  virtual bool operator() (Type const *t);
  virtual ~SomeTypeVarNotInTemplParams_Pred() {}
};

bool SomeTypeVarNotInTemplParams_Pred::operator() (Type const *t)
{
  if (!t->isCVAtomicType()) return false;
  CVAtomicType const *cv = t->asCVAtomicTypeC();

  if (cv->isCompoundType()) {
    CompoundType const *cpd = cv->asCompoundTypeC();
    // recurse on all of the arugments of the template instantiation
    // if any
    if (cpd->templateInfo()) {
      FOREACH_OBJLIST_NC(STemplateArgument, cpd->templateInfo()->arguments, iter) {
        STemplateArgument *sta = iter.data();
        if (sta->isType()) {
          if (sta->getType()->anyCtorSatisfies(*this)) return true;
        }
      }
    }
    return false;
  }

  if (cv->isTypeVariable()) {
    // check that this tvar occurs in the parameters list of the
    // template info
    Variable *tvar = cv->asTypeVariableC()->typedefVar;
    if (ti->hasSpecificParameter(tvar)) {
      return false;
    }
    return true;
  }

  return false;                 // some other type of compound type
};


// ---------------------- Variable --------------------
Variable::Variable(SourceLoc L, StringRef n, Type *t, DeclFlags f)
  : loc(L),
    name(n),
    type(t),
    isBuiltin(false),
    isBuiltinCopy(false),
    flags(f),
    value(NULL),
    defaultParamType(NULL),
    funcDefn(NULL),
    overload(NULL),
    scope(NULL),
    intData(0),
    usingAlias_or_parameterizedEntity(NULL),
    templInfo(NULL)
{
  // the first time through, do some quick tests of the
  // encodings of 'intData'
  static int didSelfTest = false;
  if (!didSelfTest) {
    didSelfTest = true;

    setAccess(AK_PRIVATE);
    setScopeKind(SK_NAMESPACE);
    setParameterOrdinal(1000);
    
    xassert(getAccess() == AK_PRIVATE);
    xassert(getScopeKind() == SK_NAMESPACE);
    xassert(getParameterOrdinal() == 1000);

    // opposite order
    setParameterOrdinal(88);
    setScopeKind(SK_CLASS);
    setAccess(AK_PROTECTED);

    xassert(getAccess() == AK_PROTECTED);
    xassert(getScopeKind() == SK_CLASS);
    xassert(getParameterOrdinal() == 88);
  }

  setAccess(AK_PUBLIC);
  setScopeKind(SK_UNKNOWN);
  setParameterOrdinal(0);

  if (!type && !isNamespace()) {
    xassert(type);
  }
}

// ctor for de-serialization
Variable::Variable(ReadXML&)
  : loc(SL_UNKNOWN),
    name(NULL),
    type(NULL),
    flags(DF_NONE),
    value(NULL),
    defaultParamType(NULL),
    funcDefn(NULL),
    overload(NULL),
    scope(NULL),
    intData(0),
    usingAlias_or_parameterizedEntity(NULL),
    templInfo(NULL)
{}

Variable::~Variable()
{}


void Variable::setFlagsTo(DeclFlags f)
{
  // this method is the one that gets to modify 'flags'
  const_cast<DeclFlags&>(flags) = f;
}


// 2005-08-15: Previously, this would return false for unions because
// I misunderstood the standard.  However, 9p4 is clear that unions
// are classes, and can have destructors, etc. (in/t0571.cc)
bool Variable::isClass() const
{
  return hasFlag(DF_TYPEDEF) && type->isCompoundType();
}


AccessKeyword Variable::getAccess() const
{
  return (AccessKeyword)(intData & 0xFF);
}

void Variable::setAccess(AccessKeyword k)
{
  intData = (intData & ~0xFF) | (k & 0xFF);
}


ScopeKind Variable::getScopeKind() const
{
  return (ScopeKind)((intData & 0xFF00) >> 8);
}

void Variable::setScopeKind(ScopeKind k)
{
  intData = (intData & ~0xFF00) | ((k << 8) & 0xFF00);
}


int Variable::getParameterOrdinal() const
{
  return (intData >> 16) & 0xFFFF;
}

void Variable::setParameterOrdinal(int ord)
{
  // this imposes a limit of 0xFFFF template parameters; but that is
  // probably ok, as the standard's recommended minimum limit is 1024
  // (annex B, para 2, near the end of the list)
  xassert(0 <= ord && ord <= 0xFFFF);

  intData = (intData & ~0xFFFF0000) | ((ord << 16) & 0xFFFF0000);
}


bool Variable::isUninstTemplateMember() const
{
  if (isTemplate() &&
      !templateInfo()->isCompleteSpecOrInstantiation()) {
    return true;
  }
  return scope && scope->isWithinUninstTemplate();
}


bool Variable::isTemplate(bool considerInherited) const
{
  return templateInfo() &&
         templateInfo()->hasParametersEx(considerInherited);
}

bool Variable::isTemplateFunction(bool considerInherited) const
{
  return type &&
         type->isFunctionType() &&
         isTemplate(considerInherited) &&
         !hasFlag(DF_TYPEDEF);
}

bool Variable::isTemplateClass(bool considerInherited) const
{
  return hasFlag(DF_TYPEDEF) &&
         type->isCompoundType() &&
         isTemplate(considerInherited);
}


bool Variable::isInstantiation() const
{
  return templInfo && templInfo->isInstantiation();
}


TemplateInfo *Variable::templateInfo() const
{                  
  // 2005-02-23: experiment: alias share's referent's template info
  return skipAliasC()->templInfo;
}

void Variable::setTemplateInfo(TemplateInfo *templInfo0)
{
  templInfo = templInfo0;
  
  // 2005-03-07: this assertion fails in some error cases (e.g., error
  // 1 of in/t0434.cc); I tried a few hacks but am now giving up on it
  // entirely
  //xassert(!(templInfo && notQuantifiedOut()));
  
  // complete the association
  if (templInfo) {
    // I am the method allowed to change TemplateInfo::var
    const_cast<Variable*&>(templInfo->var) = this;
  }
  else {
    // this happens when we're not in a template at all, but the
    // parser just takes the pending template info (which is NULL)
    // and passes it in here anyway
  }
}


bool Variable::notQuantifiedOut()
{
  TemplateInfo *ti = templateInfo();
  if (!ti) return false;
  SomeTypeVarNotInTemplParams_Pred pred(ti);
  return type->anyCtorSatisfies(pred);
}


void Variable::gdb() const
{
  cout << toString() << endl;
}

string Variable::toString() const
{
  if (Type::printAsML) {
    return toMLString();
  }
  else {
    return toCString();
  }
}


string Variable::toCString() const
{
  // as an experiment, I'm saying public(field) in the .ast file
  // in a place where the Variable* might be NULL, so I will
  // tolerate a NULL 'this'
  if (this == NULL) {
    return "NULL";
  }

  // The purpose of this method is to print the name and type
  // of this Variable object, in a debugging context.  It is
  // not necessarily intended to print them in a way consistent
  // with the C syntax that might give rise to the Variable.
  // If more specialized printing is desired, do that specialized
  // printing from outside (by directly accessing 'name', 'type',
  // 'flags', etc.).
  if (type == NULL)
    return stringc << (name? name : "/*anon*/") << " NULL type";
  else
    return type->toCString(stringc << (name? name : "/*anon*/")
                                   << namePrintSuffix());
}


string Variable::toQualifiedString() const
{                             
  string qname;
  if (name) {
    qname = fullyQualifiedName();
  }
  else {
    qname = "/*anon*/";
  }
  return type->toCString(stringc << qname << namePrintSuffix());
}


string Variable::toCStringAsParameter() const
{
  if (!global_mayUseTypeAndVarToCString) xfailure("suspended during TypePrinterC::print");
  stringBuilder sb;
  if (type->isTypeVariable()) {
    // type variable's name, then the parameter's name (if any)
    sb << type->asTypeVariable()->name;
    if (name) {
      sb << " " << name;
    }
  }
  else {
    sb << type->toCString(name);
  }

  if (value) {
    sb << renderExpressionAsString(" = ", value);
  }
  return sb;
}


string Variable::toMLString() const
{
  stringBuilder sb;
  #if USE_SERIAL_NUMBERS
    sb << printSerialNo("v", serialNumber, "-");
  #endif
  char const *name0 = "<no_name>";
  if (name) {
    name0 = name;
  }
  sb << "'" << name0 << "'->" << type->toMLString();
  return sb;
}


string Variable::fullyQualifiedName() const
{
  stringBuilder tmp;
  if (scope && !scope->isGlobalScope()) {
    tmp << scope->fullyQualifiedCName();
  }
  if (hasFlag(DF_SELFNAME)) {
    // don't need another "::name", since my 'scope' is the same
  }
  else {
    if (!tmp.isempty()) {
      tmp << "::";
    }
    
    if (name) {
      if (strcmp(name, "constructor-special") == 0) {
        // get the type name for the constructor.
        xassert(scope);
        tmp << scope->getScopeVariable()->name;
      }
      else {
        tmp << name;        // NOTE: not mangled
      }

      TemplateInfo *ti = templateInfo();
      if (ti) {
        // only print arguments that do not correspond to inherited params
        // of the thing of which this is an instance
        int numInh = 0;
        if (ti->instantiationOf) {
          numInh = ti->instantiationOf->templateInfo()->countInheritedParameters();
        }
        SObjList<STemplateArgument> const &allArgs = objToSObjListC(ti->arguments);
        SObjListIter<STemplateArgument> iter(allArgs);
        while (numInh && !iter.isDone()) {
          numInh--;
          iter.adv();
        }

        // any args left to print?
        if (!iter.isDone()) {
          tmp << sargsToString(iter);
        }
      }
    }
    else {
      tmp << "/*anon*/";
    }
  }
  return tmp;
}


string Variable::namePrintSuffix() const
{
  return "";
}


OverloadSet *Variable::getOrCreateOverloadSet()
{
  xassert(type);
  xassert(type->isFunctionType());
  if (!overload) {
    overload = new OverloadSet;
    overload->addMember(this);
  }
  return overload;
}


void Variable::getOverloadList(SObjList<Variable> &set)
{
  if (overload) {
    set = overload->set;     // copy the elements
  }
  else {
    set.prepend(this);       // just put me into it
  }
}


int Variable::overloadSetSize() const
{
  return overload? overload->count() : 1;
}


bool Variable::isMemberOfTemplate() const
{
  if (!scope) { return false; }
  if (!scope->curCompound) { return false; }

  if (scope->curCompound->isTemplate()) {
    return true;
  }

  // member of non-template class; ask if that class is itself
  // a member of a template
  return scope->curCompound->typedefVar->isMemberOfTemplate();
}


bool Variable::isTemplateTypeParam() const
{
  // The second part of this test is how we can distinguish type
  // parameters from non-type parameters whose type happens to be a
  // previous type parameter.  For example, in
  //   template <class T, T i>      // in/t0505.cc
  // 'T' is a type parameter, while 'i' is a non-type parameter but
  // its type is a type parameter.
  return hasFlag(DF_TYPEDEF) &&              // true only of 'T'
         type->isTypeVariable();             // true of both 'T' and 'i'
}


Variable *Variable::getUsingAlias() const
{
  if (!isTemplateParam()) {
    return usingAlias_or_parameterizedEntity;
  }
  else {
    return NULL;
  }
}

void Variable::setUsingAlias(Variable *target)
{
  xassert(!isTemplateParam());
  usingAlias_or_parameterizedEntity = target;
}


Variable *Variable::getParameterizedEntity() const
{
  if (isTemplateParam()) {
    return usingAlias_or_parameterizedEntity;
  }
  else {
    return NULL;
  }
}

void Variable::setParameterizedEntity(Variable *templ)
{
  xassert(isTemplateParam());
  usingAlias_or_parameterizedEntity = templ;
}


bool Variable::sameTemplateParameter(Variable const *other) const
{
  if (getParameterizedEntity() == NULL) {
    // I haven't been associated with a template yet, so don't
    // claim to be the same as anything else
    return false;
  }

  if (getParameterOrdinal() == other->getParameterOrdinal() &&
      getParameterizedEntity() == other->getParameterizedEntity()) {
    // same!
    return true;
  }
  
  return false;
}


// I'm not sure what analyses' disposition towards usingAlias ought to
// be.  One possibility is to just say they should sprinkle calls to
// skipAlias all over the place, but that's obviously not very nice.
// However, I can't just make the lookup functions call skipAlias,
// since the access control for the *alias* is what's relevant for
// implementing access control restrictions.  Perhaps there should be
// a pass that replaces all Variables in the AST with their skipAlias
// versions?  I don't know yet.  Aliasing is often convenient for the
// programmer but a pain for the analysis.

Variable const *Variable::skipAliasC() const
{
  // tolerate NULL 'this' so I don't have to conditionalize usage
  if (this && getUsingAlias()) {
    return getUsingAlias()->skipAliasC();
  }
  else {
    return this;
  }
}


// this isn't right if either is a set of overloaded functions...
bool sameEntity(Variable const *v1, Variable const *v2)
{
  v1 = v1->skipAliasC();
  v2 = v2->skipAliasC();
  
  if (v1 == v2) {
    return true;
  }
  
  if (v1 && v2 &&                   // both non-NULL
      v1->name == v2->name &&       // same simple name
      v1->hasFlag(DF_EXTERN_C) &&   // both are extern "C"
      v2->hasFlag(DF_EXTERN_C)) {
    // They are the same entity.. unfortunately, outside this
    // rather oblique test, there's no good way for the analysis
    // to know this in advance.  Ideally the tchecker should be
    // maintaining some symbol table of extern "C" names so that
    // it could use the *same* Variable object for multiple
    // occurrences in different namespaces, but I'm too lazy to
    // implement that now.
    return true;
  }
  
  return false;
}


static bool namesTemplateFunction_one(Variable const *v)
{
  // we are using this to compare template arguments to the
  // preceding name, so we are only interested in the
  // template-ness of the name itself, not any parent scopes
  bool const considerInherited = false;

  return v->isTemplate(considerInherited) || 
         v->isInstantiation();     // 2005-08-11: in/t0545.cc
}

bool Variable::namesTemplateFunction() const
{
  if (isOverloaded()) {
    // check amongst all overloaded names; 14.2 is not terribly
    // clear about that, but 14.8.1 para 2 example 2 seems to
    // imply this behavior
    SFOREACH_OBJLIST(Variable, overload->set, iter) {
      if (namesTemplateFunction_one(iter.data())) {
        return true;
      }
    }
  }

  else if (namesTemplateFunction_one(this)) {
    return true;
  }

  return false;
}


int Variable::getEnumeratorValue() const
{
  EnumType *et = type->asCVAtomicType()->atomic->asEnumType();
  EnumType::Value const *val = et->getValue(name);
  xassert(val);    // otherwise the type information is wrong..
  return val->value;
}


void Variable::setBitfieldSize(int bits)
{
  xassert(isBitfield());

  setParameterOrdinal(bits);
}

int Variable::getBitfieldSize() const
{
  xassert(isBitfield());

  return getParameterOrdinal();
}


Scope *Variable::getDenotedScope() const
{
  if (isNamespace()) {
    return scope;
  }
  
  if (type->isCompoundType()) {
    CompoundType *ct = type->asCompoundType();
    return ct;
  }

  xfailure(stringc << "expected `" << name << "' to name a scope");
  return NULL;    // silence warning
}


void Variable::traverse(TypeVisitor &vis) {
  if (!vis.visitVariable(this)) {
    return;
  }
  if (type) {
    type->traverse(vis);
  }
  vis.postvisitVariable(this);
}


// --------------------- OverloadSet -------------------
OverloadSet::OverloadSet()
  : set()
{}

OverloadSet::~OverloadSet()
{}


void OverloadSet::addMember(Variable *v)
{
  // dsw: wow, this can happen when you import two names into a
  // namespace.  So the idea is we allow ambiguity and then only
  // report an error at lookup, which is The C++ Way.
//    xassert(!findByType(v->type->asFunctionType()));
  xassert(v->type->isFunctionType());
  set.prepend(v);
}


// The problem with these is they don't work for templatized types
// because they call 'equals', not MatchType.
//
// But I've re-enabled them for Oink ....
#if 1     // obsolete; see Env::findInOverloadSet

Variable *OverloadSet::findByType(FunctionType const *ft, CVFlags receiverCV)
{
  SFOREACH_OBJLIST_NC(Variable, set, iter) {
    FunctionType *iterft = iter.data()->type->asFunctionType();

    // check the parameters other than '__receiver'
    if (!iterft->equalOmittingReceiver(ft)) continue;

    // if 'this' exists, it must match 'receiverCV'
    if (iterft->getReceiverCV() != receiverCV) continue;

    // ok, this is the right one
    return iter.data();
  }
  return NULL;    // not found
}


Variable *OverloadSet::findByType(FunctionType const *ft) {
  return findByType(ft, ft->getReceiverCV());
}
#endif // obsolete; see Env::findInOverloadSet


// EOF
