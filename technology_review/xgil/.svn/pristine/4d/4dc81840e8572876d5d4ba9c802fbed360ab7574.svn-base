// template.cc
// template stuff implementation; code for template.h, and for
// the template section of cc_env.h at the end of Env

#include "template.h"      // this module
#include "cc_env.h"        // also kind of this module
#include "trace.h"         // tracingSys
#include "strtable.h"      // StringTable
#include "cc_lang.h"       // CCLang
#include "strutil.h"       // pluraln
#include "overload.h"      // selectBestCandidate_templCompoundType
#include "typelistiter.h"  // TypeListIter
#include "cc_ast_aux.h"    // LoweredASTVisitor
#include "mtype.h"         // MType
#include "pair.h"          // pair


void copyTemplateArgs(ObjList<STemplateArgument> &dest,
                      ObjList<STemplateArgument> const &src)
{
  copyTemplateArgs(dest, objToSObjListC(src));
}

void copyTemplateArgs(ObjList<STemplateArgument> &dest,
                      SObjList<STemplateArgument> const &src)
{
  if (dest.isEmpty()) {
    // use prepend/reverse
    SFOREACH_OBJLIST(STemplateArgument, src, iter) {
      dest.prepend(new STemplateArgument(*(iter.data())));
    }
    dest.reverse();
  }
  else {
    // just do the normal thing..
    SFOREACH_OBJLIST(STemplateArgument, src, iter) {
      dest.append(new STemplateArgument(*(iter.data())));
    }
  }
}


// Is it ok to call into these routines right now?  This is
// part of a migration scheme, where dsw wants to ensure that
// these routines aren't used in some contexts.
static void checkOkToBeHere()
{
  if (!global_mayUseTypeAndVarToCString) {
    xfailure("suspended during TypePrinterC::print");
  }
}


// ------------------ TypeVariable ----------------
TypeVariable::~TypeVariable()
{}


string TypeVariable::toCString() const
{
  checkOkToBeHere();

  if (!name) {
    return "/""*anon*/";
  }

  // use the "typename" syntax instead of "class", to distinguish
  // this from an ordinary class, and because it's syntax which
  // more properly suggests the ability to take on *any* type,
  // not just those of classes
  //
  // but, the 'typename' syntax can only be used in some specialized
  // circumstances.. so I'll suppress it in the general case and add
  // it explicitly when printing the few constructs that allow it
  //
  // 8/09/04: sm: truncated down to just the name, since the extra
  // clutter was annoying and not that helpful
  return stringc //<< "/""*typevar"
//                   << "typedefVar->serialNumber:"
//                   << (typedefVar ? typedefVar->serialNumber : -1)
                 //<< "*/"
                 << name;
}

int TypeVariable::reprSize() const
{
  //xfailure("you can't ask a type variable for its size");

  // this happens when we're typechecking a template class, without
  // instantiating it, and we want to verify that some size expression
  // is constant.. so make up a number
  return 4;
}


void TypeVariable::traverse(TypeVisitor &vis)
{
  if (!vis.visitAtomicType(this)) {
    return;
  }
  vis.postvisitAtomicType(this);
}


bool TypeVariable::isAssociated() const
{
  return typedefVar->getParameterizedEntity() != NULL;
}


// -------------------- PseudoInstantiation ------------------
PseudoInstantiation::PseudoInstantiation(CompoundType *p)
  : NamedAtomicType(p? p->name : NULL),
    primary(p),
    args()        // empty initially
{}

PseudoInstantiation::~PseudoInstantiation()
{}


string PseudoInstantiation::toCString() const
{
  checkOkToBeHere();
  return stringc << name << sargsToString(args);
}

int PseudoInstantiation::reprSize() const
{
  // it shouldn't matter what we say here, since the query will only
  // be made in the context of checking (but not instantiating) a
  // template definition body
  return 4;
}


void PseudoInstantiation::traverse(TypeVisitor &vis)
{
  if (!vis.visitAtomicType(this)) {
    return;
  }

  primary->traverse(vis);
  
  if (vis.visitPseudoInstantiation_args(args)) {
    FOREACH_OBJLIST_NC(STemplateArgument, args, iter) {
      STemplateArgument *arg = iter.data();
      if (vis.visitPseudoInstantiation_args_item(arg)) {
        arg->traverse(vis);
        vis.postvisitPseudoInstantiation_args_item(arg);
      }
    }
    vis.postvisitPseudoInstantiation_args(args);
  }

  vis.postvisitAtomicType(this);
}


// -------------------- DependentQType ------------------
DependentQType::DependentQType(AtomicType *f)
  : NamedAtomicType(NULL /*name*/),    // gets changed later
    first(f),
    rest()
{}

DependentQType::~DependentQType()
{}


string DependentQType::toCString() const
{
  checkOkToBeHere();
  return stringc << first->toCString() << "::" << rest->toString();
}

string DependentQType::toMLString() const
{
  return stringc << "dependentqtype-" << toCString();
}

int DependentQType::reprSize() const
{
  return 4;    // should not matter
}

  
void traverseTargs(TypeVisitor &vis, ObjList<STemplateArgument> &list)
{
  if (vis.visitDependentQTypePQTArgsList(list)) {
    FOREACH_OBJLIST_NC(STemplateArgument, list, iter) {
      STemplateArgument *sta = iter.data();
      if (vis.visitDependentQTypePQTArgsList_item(sta)) {
        sta->traverse(vis);
        vis.postvisitDependentQTypePQTArgsList_item(sta);
      }
    }
    vis.postvisitDependentQTypePQTArgsList(list);
  }
}

void DependentQType::traverse(TypeVisitor &vis)
{
  if (!vis.visitAtomicType(this)) {
    return;
  }

  first->traverse(vis);

  PQName *name = rest;
  while (name->isPQ_qualifier()) {
    PQ_qualifier *qual = name->asPQ_qualifier();

    traverseTargs(vis, qual->sargs);
    name = qual->rest;
  }

  if (name->isPQ_template()) {
    traverseTargs(vis, name->asPQ_template()->sargs);
  }

  vis.postvisitAtomicType(this);
}


// ------------------ TemplateParams ---------------
TemplateParams::TemplateParams(TemplateParams const &obj)
  : params(obj.params)
{}

TemplateParams::~TemplateParams()
{}


string TemplateParams::paramsToCString() const
{
  return ::paramsToCString(params);
}

string paramsToCString(SObjList<Variable> const &params)
{
  stringBuilder sb;
  sb << "template <";
  int ct=0;
  SFOREACH_OBJLIST(Variable, params, iter) {
    Variable const *p = iter.data();
    if (ct++ > 0) {
      sb << ", ";
    }

    if (p->isTemplateTypeParam()) {
      if (p->name) {
        sb << "class " << p->name;
        StringRef tvName = p->type->asTypeVariable()->name;
        if (tvName && tvName != p->name) {
          // this should never happen, but if it does then I just want
          // it to be visible, not (directly) cause a crash
          sb << " /""* but type name is " << tvName << "! */";
        }
      }
      else {
        sb << "class /""*anon*/";
      }
    }
    else {
      // non-type parameter
      sb << p->toCStringAsParameter();
    }
  }
  sb << ">";
  return sb;
}

    
string TemplateParams::paramsLikeArgsToString() const
{
  stringBuilder sb;
  sb << "<";
  int ct=0;
  SFOREACH_OBJLIST(Variable, params, iter) {
    if (ct++) { sb << ", "; }
    StringRef n = iter.data()->name;
    
    if (n) {
      sb << n;
    }
    else {
      sb << "/""*anon*/";
    }
  }
  sb << ">";
  return sb;
}


// defined in cc_type.cc
bool parameterListCtorSatisfies(TypePred &pred,
                                SObjList<Variable> const &params);

bool TemplateParams::anyParamCtorSatisfies(TypePred &pred) const
{
  return parameterListCtorSatisfies(pred, params);
}


// --------------- InheritedTemplateParams ---------------
InheritedTemplateParams::InheritedTemplateParams(InheritedTemplateParams const &obj)
  : TemplateParams(obj),
    enclosing(obj.enclosing)
{}

InheritedTemplateParams::~InheritedTemplateParams()
{}


// ------------------ TemplateInfo -------------
TemplateInfo::TemplateInfo(SourceLoc il, Variable *v)
  : TemplateParams(),
    var(NULL),
    instantiationOf(NULL),
    instantiations(),
    specializationOf(NULL),
    specializations(),
    arguments(),
    instLoc(il),
    partialInstantiationOf(NULL),
    partialInstantiations(),
    argumentsToPrimary(),
    defnScope(NULL),
    definitionTemplateInfo(NULL),
    instantiateBody(false),
    instantiationDisallowed(false),
    uninstantiatedDefaultArgs(0),
    dependentBases()
{
  if (v) {
    // this sets 'this->var' too
    v->setTemplateInfo(this);
  }
}


// this is called by Env::makeUsingAliasFor ..
TemplateInfo::TemplateInfo(TemplateInfo const &obj)
  : TemplateParams(obj),
    var(NULL),                // caller must call Variable::setTemplateInfo
    instantiationOf(NULL),
    instantiations(obj.instantiations),      // suspicious... oh well
    specializationOf(NULL),
    specializations(obj.specializations),    // also suspicious
    arguments(),                             // copied below
    instLoc(obj.instLoc),
    partialInstantiationOf(NULL),
    partialInstantiations(),
    argumentsToPrimary(),                    // copied below
    defnScope(NULL),
    definitionTemplateInfo(NULL),
    instantiateBody(false),
    uninstantiatedDefaultArgs(obj.uninstantiatedDefaultArgs),
    dependentBases(obj.dependentBases)
{
  // inheritedParams
  FOREACH_OBJLIST(InheritedTemplateParams, obj.inheritedParams, iter2) {
    inheritedParams.prepend(new InheritedTemplateParams(*(iter2.data())));
  }
  inheritedParams.reverse();

  // arguments
  copyArguments(obj.arguments);

  // argumentsToPrimary
  copyTemplateArgs(argumentsToPrimary, objToSObjListC(obj.argumentsToPrimary));
}


TemplateInfo::~TemplateInfo()
{
  if (definitionTemplateInfo) {
    delete definitionTemplateInfo;
  }
}


TemplateThingKind TemplateInfo::getKind() const
{
  if (!instantiationOf && !specializationOf) {
    if (!isPartialInstantiation()) {
      xassert(arguments.isEmpty());
    }

    // bhackett: disable
    // xassert(hasMainOrInheritedParameters());

    return TTK_PRIMARY;
  }

  // specialization or instantiation
  // bhackett: disable
  // xassert(arguments.isNotEmpty());

  if (specializationOf) {
    return TTK_SPECIALIZATION;
  }
  else {     
    xassert(instantiationOf);
    return TTK_INSTANTIATION;
  }
}


bool TemplateInfo::isPartialSpec() const
{
  return isSpecialization() &&
         hasParameters();
}

bool TemplateInfo::isCompleteSpec() const
{
  return isSpecialization() &&
         !hasMainOrInheritedParameters();
}


bool TemplateInfo::isCompleteSpecOrInstantiation() const
{
  return isNotPrimary() &&
         !hasMainOrInheritedParameters();
}


bool TemplateInfo::isInstOfPartialSpec() const
{
  return isInstantiation() &&
         instantiationOf->templateInfo()->isPartialSpec();
}


// this is idempotent
TemplateInfo const *TemplateInfo::getPrimaryC() const
{
  if (instantiationOf) {
    return instantiationOf->templateInfo()->getPrimaryC();
  }
  else if (specializationOf) {
    return specializationOf->templateInfo();     // always only one level
  }
  else {
    return this;
  }
}


void TemplateInfo::addToList(Variable *elt, SObjList<Variable> &children,
                             Variable * const &parentPtr)
{
  // the key to this routine is casting away the constness of
  // 'parentPtr'; it's the one routine entitled to do so
  Variable * &parent = const_cast<Variable*&>(parentPtr);

  // add to list, ensuring (if in debug mode) it isn't already there
  xassertdb(!children.contains(elt));
  children.append(elt);             // could use 'prepend' for performance..

  // backpointer, ensuring we don't overwrite one
  xassert(!parent);
  xassert(this->var);
  parent = this->var;
}

void TemplateInfo::addInstantiation(Variable *inst)
{
  addToList(inst, instantiations,
            inst->templateInfo()->instantiationOf);
}

void TemplateInfo::addSpecialization(Variable *inst)
{
  addToList(inst, specializations,
            inst->templateInfo()->specializationOf);
}

void TemplateInfo::addPartialInstantiation(Variable *pinst)
{
  addToList(pinst, partialInstantiations,
            pinst->templateInfo()->partialInstantiationOf);
}


void TemplateInfo::changeToExplicitSpec()
{
  xassert(isInstantiation());
  
  TemplateInfo *primary = getPrimary();
  
  // remove myself from the primary's list of instantiations
  primary->instantiations.removeItem(this->var);
  const_cast<Variable*&>(instantiationOf) = NULL;

  // add myself to the primary's list of explicit specs
  primary->addSpecialization(this->var);
  
  xassert(isCompleteSpec());
}


ObjList<STemplateArgument> &TemplateInfo::getArgumentsToPrimary()
{
  if (isInstOfPartialSpec()) {
    return argumentsToPrimary;
  }
  else {
    return arguments;
  }
}


bool isomorphicArgumentLists(ObjList<STemplateArgument> const &list1,
                             ObjList<STemplateArgument> const &list2)
{
  MType mtype;
  return mtype.matchSTemplateArguments(list1, list2, MF_ISOMORPHIC|MF_MATCH);
}

bool TemplateInfo::isomorphicArguments(ObjList<STemplateArgument> const &list) const
{
  return isomorphicArgumentLists(arguments, list);
}


bool equalArgumentLists(ObjList<STemplateArgument> const &list1,
                        ObjList<STemplateArgument> const &list2,
                        MatchFlags mflags)
{
  MType mtype;
  return mtype.matchSTemplateArguments(list1, list2, mflags);
}

bool TemplateInfo::equalArguments(ObjList<STemplateArgument> const &list,
                                  MatchFlags mflags) const
{
  return equalArgumentLists(arguments, list, mflags);
}


bool TemplateInfo::argumentsContainTypeVariables() const
{
  FOREACH_OBJLIST(STemplateArgument, arguments, iter) {
    STemplateArgument const *sta = iter.data();
    if (sta->kind == STemplateArgument::STA_TYPE) {
      if (sta->value.t->containsTypeVariables()) return true;
    }
    // FIX: do other kinds
  }
  return false;
}


bool TemplateInfo::argumentsContainVariables() const
{
  FOREACH_OBJLIST(STemplateArgument, arguments, iter) {
    if (iter.data()->containsVariables()) return true;
  }
  return false;
}


bool TemplateInfo::hasParameters() const
{
  if (isPartialInstantiation()) {
    return true;
  }

  // check params attached directly to this object
  if (params.isNotEmpty()) {
    return true;
  }

  return false;
}

int TemplateInfo::countInheritedParameters() const
{                      
  int ct=0;
  FOREACH_OBJLIST(InheritedTemplateParams, inheritedParams, iter) {
    ct += iter.data()->params.count();
  }
  return ct;
}

bool TemplateInfo::hasMainOrInheritedParameters() const
{
  return hasParameters() ||
         hasInheritedParameters();
}

bool TemplateInfo::hasParametersEx(bool considerInherited) const
{
  return considerInherited?
           hasMainOrInheritedParameters() :
           hasParameters();
}


Variable *TemplateInfo::getSpecialization(ObjList<STemplateArgument> const &sargs)
{
  SFOREACH_OBJLIST_NC(Variable, specializations, iter) {     
    TemplateInfo *specTI = iter.data()->templateInfo();
    if (isomorphicArgumentLists(specTI->arguments, sargs)) {
      return iter.data();
    }
  }
  return NULL;     // not found
}


bool TemplateInfo::hasSpecificParameter(Variable const *v) const
{
  // 'params'?
  if (params.contains(v)) { return true; }
  
  // inherited?
  FOREACH_OBJLIST(InheritedTemplateParams, inheritedParams, iter) {
    if (iter.data()->params.contains(v)) { 
      return true; 
    }
  }

  return false;     // 'v' does not appear in any parameter list
}


void TemplateInfo::copyArguments(ObjList<STemplateArgument> const &sargs)
{
  copyTemplateArgs(arguments, objToSObjListC(sargs));
}

void TemplateInfo::copyArguments(SObjList<STemplateArgument> const &sargs)
{
  copyTemplateArgs(arguments, sargs);
}


void TemplateInfo::prependArguments(ObjList<STemplateArgument> const &sargs)
{
  // save the existing arguments (if any)
  ObjList<STemplateArgument> existing;
  existing.concat(arguments);
  
  // put the new ones in
  copyTemplateArgs(arguments, objToSObjListC(sargs));
  
  // put the old ones at the end
  arguments.concat(existing);
}


string TemplateInfo::templateName() const
{
  if (isPrimary()) {
    return stringc << var->fullyQualifiedName()
                   << paramsLikeArgsToString();
  }

  if (isSpecialization()) {
    return stringc << var->fullyQualifiedName()
                   << sargsToString(arguments);
  }

  #if 0    // seems like this isn't needed anymore
  // instantiation; but of the primary or of a specialization?
  TemplateInfo *parentTI = instantiationOf->templateInfo();
  if (parentTI->isPrimary()) {
    return stringc << var->fullyQualifiedName()
                   << sargsToString(arguments);
  }
  else {
    // spec params + inst args, e.g. "A<T*><int>" to mean that
    // this is an instantiation of spec "A<T*>" with args "<int>",
    // i.e. original arguments "<int*>"
    return stringc << var->fullyQualifiedName()
                   << sargsToString(parentTI->arguments)
                   << sargsToString(arguments);
  }
  #endif // 0
  
  return var->fullyQualifiedName();
}


void TemplateInfo::traverseArguments(TypeVisitor &vis)
{
  FOREACH_OBJLIST_NC(STemplateArgument, arguments, iter) {
    iter.data()->traverse(vis);
  }
}


void TemplateInfo::gdb()
{
  debugPrint(0);
}


void TemplateInfo::debugPrint(int depth, bool printPartialInsts)
{
  ind(cout, depth*2) << "TemplateInfo for "
                     << (var? var->name : "(null var)") << " {" << endl;

  depth++;

  if (isPartialInstantiation()) {
    // the template we are a partial instantiation of has all the
    // parameter info, so print it; but then *it* better not turn
    // around and print its partial instantiation list, otherwise we
    // get an infinite loop!  (discovered the hard way...)
    ind(cout, depth*2) << "partialInstantiatedFrom:\n";
    partialInstantiationOf->templateInfo()->
      debugPrint(depth+1, false /*printPartialInsts*/);
  }

  // inherited params
  FOREACH_OBJLIST(InheritedTemplateParams, inheritedParams, iter) {
    ind(cout, depth*2) << "inherited from " << iter.data()->enclosing->name
                       << ": " << iter.data()->paramsToCString() << endl;
  }

  // my params
  ind(cout, depth*2) << "params: " << paramsToCString() << endl;

  ind(cout, depth*2) << "arguments:" << endl;
  FOREACH_OBJLIST_NC(STemplateArgument, arguments, iter) {
    iter.data()->debugPrint(depth+1);
  }

  ind(cout, depth*2) << "instantiations:" << endl;
  depth++;
  SFOREACH_OBJLIST_NC(Variable, instantiations, iter) {
    Variable *var = iter.data();
    ind(cout, depth*2) << var->type->toString() << endl;
    var->templateInfo()->debugPrint(depth+1);
  }
  depth--;

  if (printPartialInsts) {
    ind(cout, depth*2) << "partial instantiations:" << endl;
    depth++;
    SFOREACH_OBJLIST_NC(Variable, partialInstantiations, iter) {
      Variable *var = iter.data();
      ind(cout, depth*2) << var->toString() << endl;
      var->templateInfo()->debugPrint(depth+1);
    }
    depth--;
  }

  depth--;

  ind(cout, depth*2) << "}" << endl;
}


// ------------------- STemplateArgument ---------------
STemplateArgument::STemplateArgument(STemplateArgument const &obj)
  : kind(obj.kind)
{
  if (kind == STA_TYPE) {
    value.t = obj.value.t;
  }
  else if (kind == STA_INT) {
    value.i = obj.value.i;
  }
  else {
    value.v = obj.value.v;
  }
}


STemplateArgument *STemplateArgument::shallowClone() const
{
  return new STemplateArgument(*this);
}


bool STemplateArgument::isObject() const
{
  switch (kind) {
    // bhackett
    //  default:
    //    xfailure("illegal STemplateArgument kind"); break;
  default: return false;

  case STA_TYPE:                // type argument
    return false;

  case STA_INT:                 // int
  case STA_ENUMERATOR:          // enumerator
  case STA_REFERENCE:           // reference to global object
  case STA_POINTER:             // pointer to global object
  case STA_MEMBER:              // pointer to class member
  case STA_DEPEXPR:             // value-dependent expr
    return true;

  case STA_TEMPLATE:            // template argument (not implemented)
    return false;
  }
}
    

bool STemplateArgument::isDependent() const
{
  if (isType()) {
    // we don't (or shouldn't...) stack constructors on top of
    // ST_DEPENDENT, so just check at the top level
    //
    // 8/10/04: I had simply been calling Type::isDependent, but that
    // answers yes for type variables.  In the context in which I'm
    // calling this, I am only interested in '<dependent>'.  I realize
    // this is a bit of a non-orthogonality, but the fix isn't clear
    // at the moment.
    return getType()->isSimple(ST_DEPENDENT);
  }
  else if (kind == STA_DEPEXPR) {
    return true;
  }
  else {
    return false;
  }
}


bool STemplateArgument::equals(STemplateArgument const *obj,
                               MatchFlags mflags) const
{
  MType mtype;
  return mtype.matchSTemplateArgument(this, obj, mflags);
}


bool STemplateArgument::containsVariables(MType *map) const
{
  if (kind == STemplateArgument::STA_TYPE) {
    if (value.t->containsVariables(map)) {
      return true;
    }
  }
  else if (kind == STA_DEPEXPR) {
    // TODO: This is wrong because the variables might be bound
    // in 'map'.  I think a reasonable solution would be to
    // rehabilitate the TypeVisitor, and design a nice way for
    // a TypeVisitor and an ASTVisitor to talk to each other.
    return true;
  }

  return false;
}


bool STemplateArgument::isomorphic(STemplateArgument const *obj) const
{
  return equals(obj, MF_ISOMORPHIC|MF_MATCH);
}


void STemplateArgument::traverse(TypeVisitor &vis)
{
  if (!vis.visitSTemplateArgument(this)) {
    return;
  }

  // dsw: WARNING: This partial implementation is a problem.  The
  // cases that are not handled here are handled manually in
  // cc_type_xml.cc.  If you add cases here you have to take them out
  // there.
  switch (kind) {
    case STA_TYPE:
      value.t->traverse(vis);
      break;

    case STA_DEPEXPR:
      // TODO: at some point I will have to store actual expressions,
      // and then I should traverse the expr
      break;

    default:
      break;
  }

  vis.postvisitSTemplateArgument(this);
}


// NOTE: if you change this function, also change
// printSTemplateArgument() in cc_print.cc
string STemplateArgument::toString() const
{
  switch (kind) {
    // bhackett
    // default: xfailure("bad kind");
    default:            return string("UNKNOWN");
    case STA_NONE:      return string("STA_NONE");
    case STA_TYPE:      return value.t->toString();   // assume 'type' if no comment
    case STA_INT:       return stringc << "/*int*/ " << value.i;
    case STA_ENUMERATOR:return stringc << "/*enum*/ " << value.v->name;
    case STA_REFERENCE: return stringc << "/*ref*/ " << value.v->name;
    case STA_POINTER:   return stringc << "/*ptr*/ &" << value.v->name;
    case STA_MEMBER:    return stringc
      << "/*member*/ &" << value.v->scope->curCompound->name
      << "::" << value.v->name;
    case STA_DEPEXPR:   return getDepExpr()->exprToString();
    case STA_TEMPLATE:  return string("template (?)");
    case STA_ATOMIC:    return value.at->toString();
  }
}


void STemplateArgument::gdb()
{
  debugPrint(0);
}


void STemplateArgument::debugPrint(int depth)
{
  for (int i=0; i<depth; ++i) cout << "  ";
  cout << "STemplateArgument: " << toString() << endl;
}


SObjList<STemplateArgument> *cloneSArgs(SObjList<STemplateArgument> &sargs)
{
  SObjList<STemplateArgument> *ret = new SObjList<STemplateArgument>();
  SFOREACH_OBJLIST_NC(STemplateArgument, sargs, iter) {
    ret->append(iter.data());
  }
  return ret;
}


string sargsToString(SObjList<STemplateArgument> const &list)
{
  SObjListIter<STemplateArgument> iter(list);
  return sargsToString(iter);
}

string sargsToString(SObjListIter<STemplateArgument> &iter)
{
  stringBuilder sb;
  sb << "<";

  int ct=0;
  for (; !iter.isDone(); iter.adv()) {
    if (ct++ > 0) {
      sb << ", ";
    }
    sb << iter.data()->toString();
  }

  if (sb[sb.length()-1] == '>') {
    sb << " ";    // avoid creating ">>"
  }
  sb << ">";
  return sb;
}


// return true if the semantic template arguments in 'args' are not
// all concrete
bool containsVariables(SObjList<STemplateArgument> const &args, MType *map)
{
  SFOREACH_OBJLIST(STemplateArgument, args, iter) {
    if (iter.data()->containsVariables(map)) {
      return true;
    }
  }
  return false;     // all are concrete
}

bool containsVariables(ObjList<STemplateArgument> const &args, MType *map)
{
  return containsVariables(objToSObjListC(args), map);
}


bool hasDependentArgs(SObjList<STemplateArgument> const &args)
{
  SFOREACH_OBJLIST(STemplateArgument, args, iter) {
    if (iter.data()->isDependent()) {
      return true;
    }
  }
  return false;
}


char const *toString(STemplateArgument::Kind k)
{
  static char const * const map[] = {
    "STA_NONE",
    "STA_TYPE",
    "STA_INT",
    "STA_ENUMERATOR",
    "STA_REFERENCE",
    "STA_POINTER",
    "STA_MEMBER",
    "STA_DEPEXPR",
    "STA_TEMPLATE",
    "STA_ATOMIC",
  };
  STATIC_ASSERT(TABLESIZE(map) == STemplateArgument::NUM_STA_KINDS);
  xassert((unsigned)k < (unsigned)STemplateArgument::NUM_STA_KINDS);
  return map[k];
}


// ---------------------- TemplCandidates ------------------------
STATICDEF
TemplCandidates::STemplateArgsCmp TemplCandidates::compareSTemplateArgs
  (STemplateArgument const *larg, STemplateArgument const *rarg)
{
  if (larg->kind != rarg->kind)
    return STAC_INCOMPARABLE;

  switch(larg->kind) {
  default:
    // bhackett
    // xfailure("bad/unexpected/unimplemented TemplateArgument kind");
    return STAC_EQUAL;
    break;

  case STemplateArgument::STA_TYPE: // type argument
    {
    // check if left is at least as specific as right
    bool leftAtLeastAsSpec;
    {
      MType match;
      if (match.matchType(larg->value.t, rarg->value.t, MF_MATCH)) {
        leftAtLeastAsSpec = true;
      } else {
        leftAtLeastAsSpec = false;
      }
    }
    // check if right is at least as specific as left
    bool rightAtLeastAsSpec;
    {
      MType match;
      if (match.matchType(rarg->value.t, larg->value.t, MF_MATCH)) {
        rightAtLeastAsSpec = true;
      } else {
        rightAtLeastAsSpec = false;
      }
    }

    // change of basis matrix
    if (leftAtLeastAsSpec) {
      if (rightAtLeastAsSpec) {
        return STAC_EQUAL;
      } else {
        return STAC_LEFT_MORE_SPEC;
      }
    } else {
      if (rightAtLeastAsSpec) {
        return STAC_RIGHT_MORE_SPEC;
      } else {
        return STAC_INCOMPARABLE;
      }
    }

    }
    break;

  case STemplateArgument::STA_INT: // int or enum argument
    if (larg->value.i == rarg->value.i) {
      return STAC_EQUAL;
    }
    return STAC_INCOMPARABLE;
    break;

  case STemplateArgument::STA_ENUMERATOR: // reference to enumerator
  case STemplateArgument::STA_REFERENCE: // reference to global object
  case STemplateArgument::STA_POINTER: // pointer to global object
  case STemplateArgument::STA_MEMBER: // pointer to class member
    if (larg->value.v == rarg->value.v) {
      return STAC_EQUAL;
    }
    return STAC_INCOMPARABLE;
    break;
  }
}


STATICDEF int TemplCandidates::compareCandidatesStatic
  (TemplateInfo const *lti, TemplateInfo const *rti)
{
  // I do not even put the primary into the set so it should never
  // show up.
  xassert(lti->isNotPrimary());
  xassert(rti->isNotPrimary());

  // they should have the same primary
  xassert(lti->getPrimaryC() == rti->getPrimaryC());

  // they should always have the same number of arguments; the number
  // of parameters is irrelevant
  xassert(lti->arguments.count() == rti->arguments.count());

  STemplateArgsCmp leaning = STAC_EQUAL;// which direction are we leaning?
  // for each argument pairwise
  ObjListIter<STemplateArgument> lIter(lti->arguments);
  ObjListIter<STemplateArgument> rIter(rti->arguments);
  for(;
      !lIter.isDone();
      lIter.adv(), rIter.adv()) {
    STemplateArgument const *larg = lIter.data();
    STemplateArgument const *rarg = rIter.data();
    STemplateArgsCmp cmp = compareSTemplateArgs(larg, rarg);
    switch(cmp) {
    default: xfailure("illegal STemplateArgsCmp"); break;
    case STAC_LEFT_MORE_SPEC:
      if (leaning == STAC_EQUAL) {
        leaning = STAC_LEFT_MORE_SPEC;
      } else if (leaning == STAC_RIGHT_MORE_SPEC) {
        leaning = STAC_INCOMPARABLE;
      }
      // left stays left and incomparable stays incomparable
      break;
    case STAC_RIGHT_MORE_SPEC:
      if (leaning == STAC_EQUAL) {
        leaning = STAC_RIGHT_MORE_SPEC;
      } else if (leaning == STAC_LEFT_MORE_SPEC) {
        leaning = STAC_INCOMPARABLE;
      }
      // right stays right and incomparable stays incomparable
      break;
    case STAC_EQUAL:
      // all stay same
      break;
    case STAC_INCOMPARABLE:
      leaning = STAC_INCOMPARABLE; // incomparable is an absorbing state
    }
  }
  xassert(rIter.isDone());      // we checked they had the same number of arguments earlier

  switch(leaning) {
  default: xfailure("illegal STemplateArgsCmp"); break;
  case STAC_LEFT_MORE_SPEC: return -1; break;
  case STAC_RIGHT_MORE_SPEC: return 1; break;
  case STAC_EQUAL:
    // FIX: perhaps this should be a user error?
    xfailure("Two template argument tuples are identical");
    break;
  case STAC_INCOMPARABLE: return 0; break;
  }

  xassert(false);
  return 0;
}


int TemplCandidates::compareCandidates(Variable const *left, Variable const *right)
{
  TemplateInfo *lti = left->templateInfo();
  xassert(lti);
  TemplateInfo *rti = right->templateInfo();
  xassert(rti);

  return compareCandidatesStatic(lti, rti);
}


// ----------------------- Env ----------------------------
// These are not all of Env's methods, just the ones declared in the
// section for templates.


bool Env::loadBindingsWithExplTemplArgs(Variable *var, ObjList<STemplateArgument> const &args,
                                        MType &match, InferArgFlags iflags)
{
  xassert(var->templateInfo());
  xassert(var->templateInfo()->isPrimary());

  ObjListIter<STemplateArgument> argIter(args);
  SObjListIterNC<Variable> paramIter(var->templateInfo()->params);
  for (; !paramIter.isDone() && !argIter.isDone();
       paramIter.adv(), argIter.adv()) {
    Variable *param = paramIter.data();
    STemplateArgument const *arg = argIter.data();

    // is the parameter already bound?  this happens e.g. during
    // explicit function instantiation, when the type of the function
    // can be used to infer some/all of the template parameters
    STemplateArgument existing = match.getBoundValue(param->name, tfac);

    // if so, it should agree with the explicitly provided argument
    if (existing.hasValue()) {
      if (!existing.equals(*arg)) {
        if (iflags & IA_REPORT_ERRORS) {
          error(stringc << "for parameter `" << param->name
                        << "', inferred argument `" << existing.toString()
                        << "' does not match supplied argument `" << arg->toString()
                        << "'");
        }
        return false;
      }
      else {
        // no need to get down into the (rather messy...) binding code
        // below
        continue;
      }
    }

    match.setBoundValue(param->name, *arg);
  }
  return true;
}


bool Env::inferTemplArgsFromFuncArgs
  (Variable *var,
   TypeListIter &argListIter,
   MType &match,
   InferArgFlags iflags)
{
  xassert(var->templateInfo());
  xassert(var->templateInfo()->isPrimary());

  // matching flags for this routine
  MatchFlags mflags = MF_DEDUCTION | MF_MATCH;

  TRACE("template", "deducing template arguments from function arguments");

  // make a copy of the original bindings; this way I can tell if a
  // parameter was made concrete just from the explicitly-provided
  // arguments, as opposed to by additional deduced arguments
  MType origMatch(match);

  // if the caller has passed in information about the receiver object
  // (so this function can work for nonstatic members), but the
  // function here is not a method, we need to skip the receiver
  FunctionType *funcType = var->type->asFunctionType();
  if ((iflags & IA_RECEIVER) &&          // receiver passed
      !funcType->isMethod()) {           // not a method
    argListIter.adv();                   // skip receiver argument
  }

  // similarly, if the caller did *not* pass a receiver but this
  // function has a receiver param, skip the param
  SObjListIterNC<Variable> paramIter(funcType->params);
  if (!(iflags & IA_RECEIVER) &&         // no receiver passed
      funcType->isMethod()) {            // but is a method
    paramIter.adv();                     // skip receiver parameter
  }

  // 2005-08-15: Previously, deduction was done by processing
  // corresponding arguments and parameters from left to right,
  // stopping on the first match failure.  However, 14.8.2.1 does not
  // explicitly give an order, which suggests that implementations are
  // required to (in effect) try all orders, and in fact 14.8.2.4p14
  // example 2 requires an order other than left-to-right.
  //
  // So, I will do the following:
  //   - Collect arg/param pairs in a worklist, initially in
  //     left-to-right order.
  //   - Draw pairs from the worklist and attempt to match.  If this
  //     fails due to DQT problems, put the pair back in the list and
  //     keep going.
  //   - Keep trying until all worklist elements have been tried
  //     without any intervening match successes.
  //
  // Tests: in/t0488.cc, in/t0570.cc.

  // first, seed the worklist with arg/param pairs
  typedef pair<Type* /*type*/, Variable* /*param*/> TypeParamPair;
  ArrayStack<TypeParamPair> worklist(funcType->params.count());
  for (; !paramIter.isDone() && !argListIter.isDone();
       paramIter.adv(), argListIter.adv()) {
    // 2005-08-09: If the parameter does not have any template
    // parameters, after substitution of explicitly-provided
    // arguments, then strict matching is not required so we skip it
    // during template argument deduction.  [cppstd 14.8.1p4]
    // (in/t0324.cc, in/t0534.cc)
    Variable *param = paramIter.data();

    if (!param->type->containsVariables(&origMatch)) {
      // skip it; no deduction can occur, and any convertibility errors
      // will be detected later
      continue;
    }

    worklist.push(make_pair(argListIter.data(), param));
  }

  // worklist for next iteration
  ArrayStack<TypeParamPair> nextWorklist(worklist.size());

  // process it until fixpoint
  while (worklist.length() != nextWorklist.length()) {
    nextWorklist.empty();

    for (int i=0; i < worklist.length(); i++) {
      Variable *param = worklist[i].second;

      Type *argType = worklist[i].first;
      Type *paramType = param->type;

      // deduction does not take into account whether the argument
      // is an lvalue, which in my system would mean it has
      // reference type, so strip that
      argType = argType->asRval();

      // prior to calling into matchtype, normalize the parameter
      // and argument types according to 14.8.2.1p2
      if (!paramType->isReference()) {
        if (argType->isArrayType()) {
          // synthesize a pointer type to be used instead
          ArrayType *at = argType->asArrayType();
          argType = tfac.makePointerType(CV_NONE, at->eltType);
        }
        else if (argType->isFunctionType()) {
          // use pointer type instead
          argType = tfac.makePointerType(CV_NONE, argType);
        }
        else {
          // final bullet says to ignore cv qualifications, but I think
          // match_Type is already doing that (probably too liberally,
          // but fixing match_Type is not on the agenda right now)
        }
      }

      // final sentence of 14.8.2.1p2
      paramType = paramType->asRval();

      // "find template argument values that will make the deduced
      // [parameter type] identical to ['argType']"
      match.failedDueToDQT = false;
      bool argUnifies = match.matchTypeNC(argType, paramType, mflags);

      if (!argUnifies && match.failedDueToDQT) {
        // this is the case where we put it back in the worklist
        // to try again later
        nextWorklist.push(worklist[i]);
        continue;
      }

      if (!argUnifies) {
        // cppstd 14.8.2.1 para 3 bullet 3: if 'paramType' is a
        // template-id, then 'argType' can be derived from
        // 'paramType'; assume that 'containsVariables' is
        // sufficient evidence that 'paramType' is a template-id

        // push past one level of pointerness too (part of bullet 3)
        if (argType->isPointer() && paramType->isPointer()) {
          argType = argType->getAtType();
          paramType = paramType->getAtType();
        }

        if (argType->isCompoundType()) {
          // get all the base classes
          CompoundType *ct = argType->asCompoundType();
          SObjList<BaseClassSubobj const> bases;
          getSubobjects(bases, ct);
          SFOREACH_OBJLIST(BaseClassSubobj const, bases, iter) {
            BaseClassSubobj const *sub = iter.data();
            if (sub->ct == ct) { continue; }      // already tried 'ct'

            // attempt to match 'sub->ct' with 'paramType'
            //
            // TODO: There are two bugs here, due to allowing the
            // effect of one match attempt to contaminate the next.
            // First, if there are two base classes and the first
            // does not match but the second does, when the first
            // fails to match it may change the bindings in 'match'
            // in such a way as to cause the second match to
            // spuriously fail.  Second, cppstd says that we must
            // report an error if more than one base class matches,
            // but we will not be able to, since one successful
            // match will (in all likelihood) modify the bindings so
            // as to prevent the second match.  The solution is to
            // save the current bindings before attempting a match,
            // but MType does not currently support the needed
            // push and pop of bindings.  Therefore I will just note
            // the bugs and ignore them for now.
            Type *t = env.makeType(sub->ct);    // leaked
            if (match.matchTypeNC(t, paramType, mflags)) {
              argUnifies = true;
              break;
            }
          }
        }

        // did we find a match in the second attempt?
        if (!argUnifies) {
          if (iflags & IA_REPORT_ERRORS) {
            // TODO: Somehow propagate this up to the user even during
            // overload resolution (where IA_REPORT_ERRORS is not set)
            // if resolution ultimately fails.
            error(stringc << "during function template argument deduction: "
                  << "argument `" << argType->toString() << "'"
                  << " is incompatible with parameter `"
                  << paramType->toString() << "'");
          }
          return false;
        }
      }
    } // for(worklist)

    // swap worklists
    worklist.swapWith(nextWorklist);

  } // while(changed)

  return true;
}


bool Env::getFuncTemplArgs
  (MType &match,
   ObjList<STemplateArgument> &sargs,
   PQName const *final,
   Variable *var,
   TypeListIter &argListIter,
   InferArgFlags iflags)
{
  // 'final' might be NULL in the case of doing overload resolution
  // for templatized ctors (that is, the ctor is templatized, but not
  // necessarily the class)
  if (final && final->isPQ_template()) {
    if (!loadBindingsWithExplTemplArgs(var, final->asPQ_templateC()->sargs, match,
                                       iflags)) {
      return false;
    }
  }

  if (!inferTemplArgsFromFuncArgs(var, argListIter, match, iflags)) {
    return false;
  }

  // match -> sargs
  return getArgumentsFromMatch(match, sargs, iflags, var);
}

bool Env::getArgumentsFromMatch
  (MType &match, ObjList<STemplateArgument> &sargs,
   InferArgFlags iflags, Variable *primary)
{
  TemplateInfo *ti = primary->templateInfo();
  xassert(ti->isPrimary());

  // put the bindings in a list in the right order
  bool haveAllArgs = true;

  // inherited params first
  FOREACH_OBJLIST(InheritedTemplateParams, ti->inheritedParams, iter) {
    getFuncTemplArgs_oneParamList(match, sargs, iflags, haveAllArgs,
                                  iter.data()->params);
  }

  // then main params
  getFuncTemplArgs_oneParamList(match, sargs, iflags, haveAllArgs,
                                ti->params);

  return haveAllArgs;
}

void Env::getFuncTemplArgs_oneParamList
  (MType &match,
   ObjList<STemplateArgument> &sargs,
   InferArgFlags iflags,
   bool &haveAllArgs,
   //ObjListIter<STemplateArgument> &piArgIter,
   SObjList<Variable> const &paramList)
{
  SFOREACH_OBJLIST(Variable, paramList, templPIter) {
    Variable const *param = templPIter.data();

    STemplateArgument sta = match.getBoundValue(param->name, tfac);

    if (!sta.hasValue()) {
      if (iflags & IA_REPORT_ERRORS) {
        error(stringc << "arguments do not bind template parameter `"
                      << templPIter.data()->name << "'");
      }
      haveAllArgs = false;
    }
    else {
      // the 'sta' we have is owned by 'match' and will go away when
      // it does; make a copy that 'sargs' can own
      sargs.append(new STemplateArgument(sta));
    }
  }
}


Variable *Env::instantiateFunctionTemplate
  (SourceLoc loc, Variable *primary, MType &match)
{
  // map 'match' to a list of semantic arguments
  ObjList<STemplateArgument> sargs;
  if (!getArgumentsFromMatch(match, sargs, IA_NO_ERRORS, primary)) {
    return NULL;
  }

  // apply them to instantiate the template
  return instantiateFunctionTemplate(loc, primary, sargs);
}


// this could be a template...
void removeElementRange(SObjList<STemplateArgument> &list, int start, int num)
{
  SObjListMutator<STemplateArgument> mut(list);
  while (start--) {
    mut.adv();
  }
  while (num--) {
    mut.remove();
  }
}


// insert bindings into SK_TEMPLATE_ARG scopes, from template
// parameters to concrete template arguments
void Env::insertTemplateArgBindings
  (Variable *baseV, SObjList<STemplateArgument> const &sargs)
{
  xassert(baseV);
  TemplateInfo *baseVTI = baseV->templateInfo();

  // begin iterating over arguments
  SObjListIter<STemplateArgument> argIter(sargs);

  // if 'baseV' is a partial instantiation, then it provides
  // a block of arguments at the beginning, and then we use 'sargs'
  SObjList<STemplateArgument> expandedSargs;
  if (baseVTI->isPartialInstantiation()) {
    // put 'sargs' in initially
    expandedSargs = sargs;

    // in/t0438a.cc: the partial instantiation chain may be longer
    // than one element, so need a loop here

    // bhackett: horrible hack to limit the number of times we will follow
    // these instantiation chains, because we can apparently get into
    // an infinite loop here.
    size_t instantiations = 0;

    while (baseVTI->isPartialInstantiation()) {

      if (++instantiations == 5) {
        error("threshold reached in partial instantiation chain");
        break;
      }

      // put partial inst args first
      SObjList<STemplateArgument> const &piArgs =
        objToSObjListC(baseVTI->arguments);
      expandedSargs.prependAll(piArgs);

      if (baseVTI->isPartialSpec()) {
        // (in/t0504.cc) Oy, partial inst of partial spec.  I only
        // want some of the args I just prepended, namely the ones
        // that are *not* partial spec args.  So, remove the ones that
        // are; they come after the partial inst args in 'piArgs'.
        // (Disgusting hack.  It's a miracle it works at all.)
        TemplateInfo *origTI = baseVTI->partialInstantiationOf->templateInfo();
        int numPartialSpecArgs = origTI->arguments.count();
        removeElementRange(expandedSargs, piArgs.count() - numPartialSpecArgs,
                           numPartialSpecArgs);
      }

      // finally, set 'baseVTI' to point at the original template,
      // since it has the parameter list for the definition
      baseVTI = baseVTI->partialInstantiationOf->templateInfo();
    }

    // now, reset the iterator to walk the expanded list instead
    argIter.reset(expandedSargs);
  }

  // does the definition parameter list differ from the declaration
  // parameter list?
  if (baseVTI->definitionTemplateInfo) {
    // use the params from the definition instead
    baseVTI = baseVTI->definitionTemplateInfo;
  }

  // first, apply them to the inherited parameters
  FOREACH_OBJLIST(InheritedTemplateParams, baseVTI->inheritedParams, iter) {
    InheritedTemplateParams const *inh = iter.data();

    // create a scope to hold the bindings
    Scope *s = enterScope(SK_TEMPLATE_ARGS, "inherited template argument bindings");

    // insert them
    insertTemplateArgBindings_oneParamList(s, baseV, argIter, inh->params);
  }

  // make a scope for the main template arguments; this one will be at
  // the very top, though it will then be covered by the scope of the
  // entity being instantiated (the caller does this)
  Scope *argScope = enterScope(SK_TEMPLATE_ARGS, "main template argument bindings");

  // then, bind "my" parameters
  insertTemplateArgBindings_oneParamList(argScope, baseV, argIter, baseVTI->params);

  if (!argIter.isDone()) {
    error(stringc
          << "too many template arguments to `" << baseV->name << "'", EF_STRONG);
  }
}

// returns false if an error is detected
bool Env::insertTemplateArgBindings_oneParamList
  (Scope *scope, Variable *baseV, SObjListIter<STemplateArgument> &argIter,
   SObjList<Variable> const &params)
{
  SObjListIter<Variable> paramIter(params);
  while (!paramIter.isDone()) {
    Variable const *param = paramIter.data();

    // if we have exhaused the explicit arguments, use a NULL 'sarg'
    // to indicate that we need to use the default arguments from
    // 'param' (if available)
    //
    // 8/10/04: Default arguments are now handled elsewhere
    // TODO: fully collapse this code to reflect that

    // bhackett: disable
    // xassert(!argIter.isDone());       // should not get here with too few args

    if (argIter.isDone())
      return false;

    STemplateArgument const *sarg = argIter.data();

    if (sarg && sarg->isTemplate()) {
      xfailure("Template template parameters are not implemented");
    }


    if (param->hasFlag(DF_TYPEDEF) &&
        (!sarg || sarg->isType())) {
      if (!sarg && !param->defaultParamType) {
        error(stringc
          << "too few template arguments to `" << baseV->name << "'");
        return false;
      }

      // bind the type parameter to the type argument
      Type *t = sarg? sarg->getType() : param->defaultParamType;
      Variable *binding = makeVariable(param->loc, param->name, t, 
                                       DF_TYPEDEF | DF_TEMPL_PARAM | DF_BOUND_TPARAM);
      addVariableToScope(scope, binding);
    }
    else if (!param->hasFlag(DF_TYPEDEF) &&
             (!sarg || sarg->isObject())) {
      if (!sarg && !param->value) {
        error(stringc
          << "too few template arguments to `" << baseV->name << "'");
        return false;
      }

      // TODO: verify that the argument in fact matches the parameter type

      // bind the nontype parameter directly to the nontype expression;
      // this will suffice for checking the template body, because I
      // can const-eval the expression whenever it participates in
      // type determination; the type must be made 'const' so that
      // E_variable::constEval will believe it can evaluate it
      Type *bindType = param->type->isReference()? 
        param->type :                 // reference: no need/desire to apply 'const'
        tfac.applyCVToType(param->loc, CV_CONST,    // non-reference: apply 'const'
                           param->type, NULL /*syntax*/);
      Variable *binding = makeVariable(param->loc, param->name,
                                       bindType, DF_TEMPL_PARAM | DF_BOUND_TPARAM);

      // set 'bindings->value', in some cases creating AST
      if (!sarg) {
        binding->value = param->value;

        // sm: the statement above seems reasonable, but I'm not at
        // all convinced it's really right... has it been tcheck'd?
        // has it been normalized?  are these things necessary?  so
        // I'll wait for a testcase to remove this assertion... before
        // this assertion *is* removed, someone should read over the
        // applicable parts of cppstd
        xfailure("unimplemented: default non-type argument");
      }
      switch (sarg->kind) {
        // The following cases get progressively more difficult for
        // an analysis to "see" what the actual template argument is.
        // For example, in the first case, it sees something like:
        //   int const I = 3;
        // and const-eval'ing variables like 'I' is pretty routine.
        // But for a pointer to member, it sees:
        //   int A::*p const = &A::foo;
        // and such constructs are unusual in ordinary code.  At some
        // point I may need to implement a more aggressive
        // substitution transformation, rather than relying on the
        // indirection through the 'binding' variable.

        case STemplateArgument::STA_INT: {
          binding->value = build_E_intLit(sarg->getInt());
          break;
        }
        case STemplateArgument::STA_ENUMERATOR: {
          binding->value = build_E_variable(sarg->getEnumerator());
          break;
        }
        case STemplateArgument::STA_REFERENCE: {
          binding->value = build_E_variable(sarg->getReference());
          break;
        }
        case STemplateArgument::STA_POINTER: {
          binding->value = build_E_addrOf(build_E_variable(sarg->getPointer()));
          break;
        }
        case STemplateArgument::STA_MEMBER: {
          binding->value = build_E_addrOf(build_E_variable(sarg->getMember()));
          break;
        }
        case STemplateArgument::STA_DEPEXPR: {
          binding->value = sarg->getDepExpr();
          break;
        }
        default: {
          xunimp("template template parameters");
        }
      }
      xassert(binding->value);

      if (param->type->containsGeneralizedDependent()) {
        // (in/t0505.cc) the parameter type probably depends on 
        // parameters that have been bound earlier in the parameter
        // list; but refining 'param->type' appropriately is not
        // very convenient, so I'm just going to forego the check
        //
        // TODO: do it right, by building an MType
        // and using applyArgumentMap
      }
      else if (binding->value->type->containsGeneralizedDependent()) {
        // originally I added this to parallel the above case, but
        // that was wrong, and now I have fixed default argument
        // generation so this should never happen
        xfailure("template argument is not concrete");
      }
      else {
        // check that this argument is compatible with the parameter
        // (TODO: this isn't exactly what 14.3.2p5 says)
        string errorMsg;
        if (SC_ERROR == getStandardConversion(&errorMsg,
                                              binding->value->getSpecial(lang),
                                              binding->value->type,
                                              param->type,
                                              false /*destIsReceiver*/)) {
          error(errorMsg);
        }
      }

      addVariableToScope(scope, binding);
    }
    else {
      // mismatch between argument kind and parameter kind
      char const *paramKind = param->hasFlag(DF_TYPEDEF)? "type" : "non-type";
      // FIX: make a provision for template template parameters here
      char const *argKind = sarg->isType()? "type" : "non-type";
      error(stringc
            << "`" << param->name << "' is a " << paramKind
            << " parameter, but `" << sarg->toString() << "' is a "
            << argKind << " argument", EF_STRONG);
    }

    paramIter.adv();
    if (!argIter.isDone()) {
      argIter.adv();
    }
  }

  // having added the bindings, turn off name acceptance
  scope->canAcceptNames = false;

  xassert(paramIter.isDone());
  return true;
}

void Env::insertTemplateArgBindings
  (Variable *baseV, ObjList<STemplateArgument> const &sargs)
{
  insertTemplateArgBindings(baseV, objToSObjListC(sargs));
}

                                                   
// reverse the effects of 'insertTemplateArgBindings'
void Env::deleteTemplateArgBindings(Scope *limit)
{
  // just blow away template argument scopes on top
  while (scope()->scopeKind == SK_TEMPLATE_ARGS &&
         scope() != limit) {
    exitScope(scope());
  }
}


// The situation here is we have a partial specialization, for
// example
//
//   template <class T, class U>
//   class A<int, T*, U**> { ... }
//
// and we'd like to instantiate it with some concrete arguments.  What
// we have is arguments that apply to the *primary*, for example
//
//   <int, float*, char***>
//
// and we want to derive the proper arguments to the partial spec,
// namely
//
//   <float, char*>
//
// so we can pass these on to the instantiation routines.  
//
// It's a bit odd to be doing this matching again, since to even
// discover that the partial spec applied we would have already done
// it once.  For now I'll let that be...
void Env::mapPrimaryArgsToSpecArgs(
  Variable *baseV,         // partial specialization
  ObjList<STemplateArgument> &partialSpecArgs,       // dest. list
  ObjList<STemplateArgument> &primaryArgs)           // source list
{
  // similar to Env::findMostSpecific, we need to match against the
  // original's args if this is a partial instantiation (in/t0504.cc)
  TemplateInfo *baseVTI = baseV->templateInfo();
  TemplateInfo *matchTI = baseVTI;
  if (baseVTI->isPartialInstantiation()) {
    matchTI = baseVTI->partialInstantiationOf->templateInfo();
  }

  // execute the match to derive the bindings; we should not have
  // gotten here if they do not unify
  MType match(env);
  bool matches = match.matchSTemplateArgumentsNC(primaryArgs, matchTI->arguments, 
                                                 MF_MATCH);
  xassert(matches);

  // Now the arguments are bound in 'bindings', for example
  //
  //   T |-> float
  //   U |-> char
  //
  // We just need to run over the partial spec's parameters and
  // build an argument corresponding to each parameter.

  // first get args corresp. to inherited params
  FOREACH_OBJLIST(InheritedTemplateParams, baseVTI->inheritedParams, iter) {
    mapPrimaryArgsToSpecArgs_oneParamList(iter.data()->params, match, partialSpecArgs);
  }

  // then the main params
  mapPrimaryArgsToSpecArgs_oneParamList(baseVTI->params, match, partialSpecArgs);
}

void Env::mapPrimaryArgsToSpecArgs_oneParamList(
  SObjList<Variable> const &params,     // one arg per parameter
  MType &match,                         // carries bindingsto use
  ObjList<STemplateArgument> &partialSpecArgs)      // dest. list
{
  SFOREACH_OBJLIST(Variable, params, iter) {
    Variable const *param = iter.data();

    STemplateArgument arg = match.getBoundValue(param->name, tfac);
    if (!arg.hasValue()) {
      error(stringc
            << "during partial specialization parameter `" << param->name
            << "' not bound in inferred bindings", EF_STRONG);
      return;
    }

    partialSpecArgs.append(new STemplateArgument(arg));
  }
}


// find most specific specialization that matches the given arguments
Variable *Env::findMostSpecific
  (Variable *baseV, ObjList<STemplateArgument> const &sargs)
{
  // baseV should be a template primary
  TemplateInfo *baseVTI = baseV->templateInfo();
  xassert(baseVTI->isPrimary());

  // iterate through all of the specializations and build up a set of
  // candidates
  TemplCandidates templCandidates;
  SFOREACH_OBJLIST_NC(Variable, baseVTI->specializations, iter) {
    Variable *spec = iter.data();
    TemplateInfo *specTI = spec->templateInfo();
    xassert(specTI);        // should have templateness

    // if 'specTI' is a partial instantiation, we want to match
    // against the original argument list (in/t0504.cc)
    TemplateInfo *matchTI = specTI;
    if (specTI->isPartialInstantiation()) {
      matchTI = specTI->partialInstantiationOf->templateInfo();
    }

    // see if this candidate matches
    MType match;
    if (match.matchSTemplateArguments(sargs, matchTI->arguments, MF_MATCH)) {
      templCandidates.add(spec);
    }
  }

  // there are no candidates so we just use the primary
  if (templCandidates.candidates.isEmpty()) {
    return baseV;
  }

  // there are candidates to try; select the best
  Variable *bestV = selectBestCandidate_templCompoundType(templCandidates);

  // if there is not best candidate, then the call is ambiguous and
  // we should deal with that error
  if (!bestV) {
    // TODO: expand this error message
    error(stringc << "ambiguous attempt to instantiate template", EF_STRONG);
    return baseV;      // recovery: use the primary
  }

  // otherwise, use the best one
  return bestV;
}


// remove scopes from the environment until the innermost
// scope on the scope stack is the same one that the template
// definition appeared in; template definitions can see names
// visible from their defining scope only [cppstd 14.6 para 1]
//
// update: (e.g. t0188.cc) pop scopes until we reach one that
// *contains* (or equals) the defining scope
//
// 4/20/04: Even more (e.g. t0204.cc), we need to push scopes
// to dig back down to the defining scope.  So the picture now
// looks like this:
//
//       global                   /---- this is "foundScope"
//         |                     /
//         namespace1           /   }
//         | |                 /    }- 2. push these: "pushedScopes"
//         | namespace11  <---/     }
//         |   |
//         |   template definition
//         |
//         namespace2               }
//           |                      }- 1. pop these: "poppedScopes"
//           namespace21            }
//             |
//             point of instantiation
//
// actually, it's *still* not right, because
//   - this allows the instantiation to see names declared in
//     'namespace11' that are below the template definition, and
//   - it's entirely wrong for dependent names, a concept I
//     largely ignore at this time
// however, I await more examples before continuing to refine
// my approximation to the extremely complex lookup rules
void Env::prepArgScopeForTemlCloneTcheck
  (ObjList<SavedScopePair> &poppedScopes, SObjList<Scope> &pushedScopes, 
   Scope *foundScope)
{
  xassert(foundScope);

  // pop scope scopes
  while (!scopes.firstC()->enclosesOrEq(foundScope)) {
    Scope *s = scopes.first();
    TRACE("scope", "prepArgScope: removing " << s->desc());
    retractScope(s);

    // do I need to save a delegation pointer?
    SavedScopePair *ssp = new SavedScopePair(s);
    if (s->hasDelegationPointer()) {
      ssp->parameterizingScope = s->getAndNullifyDelegationPointer();
      TRACE("scope", "prepArgScope: ... and saved delegation ptr " <<
                     ssp->parameterizingScope->desc());
    }

    poppedScopes.prepend(ssp);
    if (scopes.isEmpty()) {
      xfailure("emptied scope stack searching for defining scope");
    }
  }

  // make a list of the scopes to push; these form a path from our
  // current scope to the 'foundScope'
  Scope *s = foundScope;
  while (s != scopes.firstC()) {
    pushedScopes.prepend(s);
    s = s->parentScope;
    if (!s) {
      if (scopes.firstC()->isGlobalScope()) {
        // ok, hit the global scope in the traversal
        break;
      }
      else {
        xfailure("missed the current scope while searching up "
                 "from the defining scope");
      }
    }
  }

  // now push them in list order, which means that 'foundScope'
  // will be the last one to be pushed, and hence the innermost
  // (I waited until now b/c this is the opposite order from the
  // loop above that fills in 'pushedScopes')
  SFOREACH_OBJLIST_NC(Scope, pushedScopes, iter) {
    // Scope 'iter.data()' is now on both lists, but neither owns
    // it; 'scopes' does not own Scopes that are named, as explained
    // in the comments near its declaration (cc_env.h)
    TRACE("scope", "prepArgScope: adding " << iter.data()->desc());
    extendScope(iter.data());
  }
}


void Env::unPrepArgScopeForTemlCloneTcheck
  (ObjList<SavedScopePair> &poppedScopes, SObjList<Scope> &pushedScopes)
{
  // restore the original scope structure
  pushedScopes.reverse();
  while (pushedScopes.isNotEmpty()) {
    Scope *s = pushedScopes.removeFirst();
    TRACE("scope", "unPrepArgScope: removing " << s->desc());
    retractScope(s);
  }

  // re-add the inner scopes removed above
  while (poppedScopes.isNotEmpty()) {
    SavedScopePair *ssp = poppedScopes.removeFirst();

    // take out the scope and nullify it, effectively transferring ownership
    Scope *s = ssp->scope;
    ssp->scope = NULL;
    TRACE("scope", "unPrepArgScope: adding " << s->desc());

    // replace the parameterizingScope if needed
    if (ssp->parameterizingScope) {
      s->setDelegationPointer(ssp->parameterizingScope);
      TRACE("scope", "... and restored delegation ptr " <<
                     ssp->parameterizingScope->desc());
    }

    extendScope(s);
    delete ssp;
  }
}


// ---------------- default argument instantiation ----------------
// find the D_func with parameters for 'func'
D_func *getD_func(Function *func)
{
  // find innermost D_func
  D_func *dfunc = NULL;
  for (IDeclarator *d = func->nameAndParams->decl;
       !d->isD_name();
       d = d->getBase()) {
    if (d->isD_func()) {
      dfunc = d->asD_func();
    }
  }
  xassert(dfunc);

  return dfunc;
}


// Remove any default argument expressions from the parameters in
// 'func'.  Later, as the default arguments are instantiated, we
// will re-insert them.  That way we maintain the invariants that
// (1) only tcheck'd syntax hangs off of a Function, and (2) the
// Variable::value for a parameter is equal to the initializing
// expression hanging off the associated Declarator.
void removeDefaultArgs(Function *func)
{
  D_func *dfunc = getD_func(func);

  // clean the default arguments (just leak them)
  FAKELIST_FOREACH(ASTTypeId, dfunc->params, iter) {
    iter->decl->init = NULL;
  }
}


// Take all of the default argument expressions in 'primary', and
// attach clones of them to 'inst'.  Also, take note in 'instTI' of
// how many there are, so we know which ones are instantiated and
// which ones are uninstantiated (initially, they are all
// uninstantiated).
void cloneDefaultArguments(Variable *inst, TemplateInfo *instTI,
                           Variable *primary)
{
  FunctionType *instFt = inst->type->asFunctionType();
  FunctionType *primaryFt = primary->type->asFunctionType();

  SObjListIterNC<Variable> instParam(instFt->params);
  SObjListIterNC<Variable> primaryParam(primaryFt->params);

  for (; !instParam.isDone() && !primaryParam.isDone();
       instParam.adv(), primaryParam.adv()) {
    if (primaryParam.data()->value) {
      instParam.data()->value = primaryParam.data()->value->clone();
      instTI->uninstantiatedDefaultArgs++;
    }
    else {
      // they are supposed to be contiguous at the end of the list, and
      // prior tchecking should have ensured this
      //
      // actually, even if we reported the error, we might have
      // continued to get here... what then?  not sure yet
      xassert(instTI->uninstantiatedDefaultArgs == 0);
    }
  }

  xassert(instParam.isDone() && primaryParam.isDone());
}


int countParamsWithDefaults(FunctionType *ft)
{
  int ret = 0;
  SFOREACH_OBJLIST(Variable, ft->params, iter) {
    if (iter.data()->value) {
      ret++;
    }
  }
  return ret;
}


// Given that all but 'instTI->uninstantiatedDefaultArgs' default args
// have been instantiated, attach them to the function definition, if
// there is one.
void syncDefaultArgsWithDefinition(Variable *instV, TemplateInfo *instTI)
{
  if (!instV->funcDefn || !instTI->instantiateBody) {
    return;
  }

  D_func *dfunc = getD_func(instV->funcDefn);

  // iterate over both parameter lists (syntactic and semantic)
  FakeList<ASTTypeId> *syntactic(dfunc->params);
  SObjListIterNC<Variable> semantic(instV->type->asFunctionType()->params);
  if (instV->type->asFunctionType()->isMethod()) {
    semantic.adv();   // the receiver is never syntactically present
  }

  int skipped = 0;
  for (; syntactic && !semantic.isDone();
       syntactic = syntactic->butFirst(), semantic.adv()) {
    Variable *sem = semantic.data();
    if (!sem->value) {
      continue;
    }

    if (skipped < instTI->uninstantiatedDefaultArgs) {
      skipped++;
      continue;
    }

    Declarator *d = syntactic->first()->decl;
    if (d->init) {
      continue;       // already transferred
    }

    d->init = new IN_expr(sem->loc /* not perfect, but it will do */,
                          sem->loc,
                          sem->value);
  }

  // should end at the same time, except for possibly a trailing 
  // (singleton, really) 'void'-typed parameter
  //
  // could also be ST_ELLIPSIS (in/t0559.cc)
  if (syntactic && 
      (syntactic->first()->getType()->isVoid() ||
       syntactic->first()->getType()->isSimple(ST_ELLIPSIS))) {
    syntactic = syntactic->butFirst();
  }
  xassert(!syntactic && semantic.isDone());
}


// cppstd 14.7.1 para 11
//
// 'neededDefaults' says how many default arguments were needed at
// some call site.  We will use that to determine how many default
// arguments need to be instantiated (which may be 0).
void Env::instantiateDefaultArgs(Variable *instV, int neededDefaults)
{
  if (!instV->isInstantiation()) {
    return;
  }
  TemplateInfo *instTI = instV->templateInfo();

  if (instTI->uninstantiatedDefaultArgs == 0) {
    return;       // nothing more we could instantiate anyway
  }

  // which parameters have default args?
  FunctionType *ft = instV->type->asFunctionType();
  int haveDefaults = 0;
  int noDefaults = 0;
  {
    SFOREACH_OBJLIST(Variable, ft->params, iter) {
      if (iter.data()->value) {
        haveDefaults++;
      }
      else {
        noDefaults++;
      }
    }
  }
  xassert(instTI->uninstantiatedDefaultArgs <= haveDefaults);

  // expected scenario:
  //                           <-- m ---><-- n --->
  //                           <---uninstDefaults->
  //                                     <--neededDefaults->
  //   params:  0-------------|-----------------------------|
  //            <-noDefaults-> <--------haveDefaults------->
  //
  // 'n' is the number of defaults to instantiate
  int m = haveDefaults - neededDefaults;
  int n = instTI->uninstantiatedDefaultArgs - m;
  if (m < 0 || n <= 0) {
    return;
  }
  
  TRACE("template", "instantiating " << pluraln(n, "argument") <<
                    ", starting at arg " << (noDefaults+m) << ", in func decl: " <<
                    instV->toQualifiedString());
  
  // declScope: the scope where the function declaration appeared
  Variable *baseV = instTI->instantiationOf;
  Scope *declScope = baseV->scope;
  xassert(declScope);

  // ------- BEGIN: duplicated from below -------
  // isolate context
  InstantiationContextIsolator isolator(*this, loc());

  // set up the scopes in a way similar to how it was when the
  // template definition was first seen
  ObjList<SavedScopePair> poppedScopes;
  SObjList<Scope> pushedScopes;
  prepArgScopeForTemlCloneTcheck(poppedScopes, pushedScopes, declScope);

  // bind the template arguments in scopes so that when we tcheck the
  // body, lookup will find them
  insertTemplateArgBindings(baseV, instTI->arguments);

  // push the declaration scopes for inline definitions, since
  // we don't get those from the declarator (that is in fact a
  // mistake of the current implementation; eventually, we should
  // 'pushDeclarationScopes' regardless of DF_INLINE_DEFN)
  bool inlineDefn = instV->funcDefn &&
                    (instV->funcDefn->dflags & DF_INLINE_DEFN);
  if (inlineDefn) {
    pushDeclarationScopes(instV, declScope);
  }
  // ------- END: duplicated from below -------

  // tcheck some of the args
  for (int i = noDefaults+m; i < noDefaults+n+m; i++) {
    Variable *param = ft->params.nth(i);
    if (param->value) {
      param->value->tcheck(*this, param->value);
      instTI->uninstantiatedDefaultArgs--;
    }
    else {
      // program is in error (e.g., default args not contiguous at the
      // end), hopefully this has already been reported and we just
      // skip it
    }
  }

  // if there is an instantiated definition, attach the newly tcheck'd
  // default arg exprs to it
  syncDefaultArgsWithDefinition(instV, instTI);

  // ------- BEGIN: duplicated from below -------
  // remove the template argument scopes
  deleteTemplateArgBindings();

  if (inlineDefn) {
    popDeclarationScopes(instV, declScope);
  }

  unPrepArgScopeForTemlCloneTcheck(poppedScopes, pushedScopes);
  xassert(poppedScopes.isEmpty() && pushedScopes.isEmpty());
  // ------- END: duplicated from below -------
}


// --------------- function template instantiation ------------
// Get or create an instantiation Variable for a function template.
// Note that this does *not* instantiate the function body; instead,
// instantiateFunctionBody() has that responsibility.
Variable *Env::instantiateFunctionTemplate
  (SourceLoc loc,                              // location of instantiation request
   Variable *primary,                          // template primary to instantiate
   ObjList<STemplateArgument> const &sargs)    // arguments to apply to 'primary'
{
  // t0424.cc: if 'primary' is an alias, skip past it; aliases 
  // get to participate in overload resolution (i.e., *selecting*
  // the function to invoke), but instantiation is always done
  // with the real thing
  primary = primary->skipAlias();

  TemplateInfo *primaryTI = primary->templateInfo();
  xassert(primaryTI->isPrimary());

  // the arguments should be concrete. bhackett: comes up with some parse/tcheck errors.
  // xassert(!containsVariables(sargs));
  if (containsVariables(sargs))
    return NULL;

  // look for a (complete) specialization that matches
  Variable *spec = findCompleteSpecialization(primaryTI, sargs);
  if (spec) {
    return spec;      // use it
  }

  // look for an existing instantiation that has the right arguments
  Variable *inst = findInstantiation(primaryTI, sargs);
  if (inst) {
    return inst;      // found it; that's all we need
  }

  // since we didn't find an existing instantiation, we have to make
  // one from scratch
  TRACE("template", "instantiating func decl: " <<
                    primary->fullyQualifiedName() << sargsToString(sargs));

  // I don't need this, right?
  // isolate context
  //InstantiationContextIsolator isolator(*this, loc);

  // bind the parameters in an STemplateArgumentMap
  MType map(env);
  bindParametersInMap(map, primaryTI, objToSObjListC(sargs));

  // compute the type of the instantiation by applying 'map' to
  // the templatized type
  Type *instType = applyArgumentMapToType_helper(map, primary->type);
  if (!instType) {
    // caught XTypeDeduction

    // unfortunately, the trace message gets split into two because
    // neither place has all the context
    TRACE("template", "^^^ failed to instantiate " <<
                      primary->fullyQualifiedName() << sargsToString(sargs));
    return NULL;
  }

  // create the representative Variable
  inst = makeInstantiationVariable(primary, instType);

  // TODO: fold the following three activities into
  // 'makeInstantiationVariable'

  // annotate it with information about its templateness
  TemplateInfo *instTI = new TemplateInfo(loc, inst);
  instTI->copyArguments(sargs);

  // insert into the instantiation list of the primary
  primaryTI->addInstantiation(inst);

  // this is an instantiation
  xassert(instTI->isInstantiation());

  // clone default argument expressions from the primary
  cloneDefaultArguments(inst, instTI, primary);

  return inst;
}


void Env::ensureFuncBodyTChecked(Variable *instV)
{
  if (!instV) {
    return;      // error recovery
  }
  if (!instV->type->isFunctionType()) {
    // I'm not sure what circumstances can cause this, but it used
    // to be that all call sites to this function were guarded by
    // this 'isFunctionType' check, so I pushed it inside
    return;
  }

  TemplateInfo *instTI = instV->templateInfo();
  if (!instTI) {
    // not a template instantiation
    return;
  }
  if (!instTI->isCompleteSpecOrInstantiation()) {
    // not an instantiation; this might be because we're in
    // the middle of tchecking a template definition, so we
    // just used a function template primary sort of like
    // a PseudoInstantiation; skip checking it
    return;
  }
  if (instTI->instantiationDisallowed) {
    // someone told us not to instantiate
    return;
  }
  if (instTI->instantiateBody) {
    // we've already seen this request, so either the function has
    // already been instantiated, or else we haven't seen the
    // definition yet so there's nothing we can do
    return;
  }

  // acknowledge the request
  instTI->instantiateBody = true;

  // what template am I an instance of?
  Variable *baseV = instTI->instantiationOf;
  if (!baseV) {
    // This happens for explicit complete specializations.  It's
    // not clear whether such things should have templateInfos
    // at all, but there seems little harm, so I'll just bail in
    // that case
    return;
  }

  // have we seen a definition of it?
  if (!baseV->funcDefn) {
    // nope, nothing we can do yet
    TRACE("template", "want to instantiate func body: " << 
                      instV->toQualifiedString() << 
                      ", but cannot because have not seen defn");
    return;
  }

  // ok, at this point we're committed to going ahead with
  // instantiating the function body
  instantiateFunctionBody(instV);
}

void Env::instantiateFunctionBody(Variable *instV)
{ 
  if (!doFunctionTemplateBodyInstantiation) {
    TRACE("template", "NOT instantiating func body: " << 
                      instV->toQualifiedString() <<
                      " because body instantiation is disabled");
    return;
  }

  if (delayFunctionInstantiation) {
    TRACE("template", "delaying instantiating of: " << instV->toQualifiedString());
    delayedFuncInsts.prepend(
      new DelayedFuncInst(instV, instantiationLocStack, loc()));
  }
  else {
    instantiateFunctionBodyNow(instV, loc());
  }
}

void Env::instantiateFunctionBodyNow(Variable *instV, SourceLoc loc)
{
  TRACE("template", "instantiating func body: " << instV->toQualifiedString());

  // reconstruct a few variables from above
  TemplateInfo *instTI = instV->templateInfo();
  Variable *baseV = instTI->instantiationOf;

  // someone should have requested this
  xassert(instTI->instantiateBody);

  // isolate context
  InstantiationContextIsolator isolator(*this, loc);

  // defnScope: the scope where the function definition appeared.
  Scope *defnScope;

  // do we have a function definition already?
  if (instV->funcDefn) {
    // inline definition
    defnScope = instTI->defnScope;
  }
  else {
    // out-of-line definition; must clone the primary's definition
    instV->funcDefn = baseV->funcDefn->clone();
    defnScope = baseV->templateInfo()->defnScope;
  }

  // remove default argument expressions from the clone parameters
  removeDefaultArgs(instV->funcDefn);

  // set up the scopes in a way similar to how it was when the
  // template definition was first seen
  ObjList<SavedScopePair> poppedScopes;
  SObjList<Scope> pushedScopes;
  prepArgScopeForTemlCloneTcheck(poppedScopes, pushedScopes, defnScope);

  // bind the template arguments in scopes so that when we tcheck the
  // body, lookup will find them
  insertTemplateArgBindings(baseV, instTI->arguments);

  // push the declaration scopes for inline definitions, since
  // we don't get those from the declarator (that is in fact a
  // mistake of the current implementation; eventually, we should
  // 'pushDeclarationScopes' regardless of DF_INLINE_DEFN)
  if (instV->funcDefn->dflags & DF_INLINE_DEFN) {
    pushDeclarationScopes(instV, defnScope);
  }

  // check the body, forcing it to use 'instV'
  instV->funcDefn->tcheck(*this, instV);
  
  // if we have already tcheck'd some default args, e.g., because we
  // saw uses of the template before seeing the definition, transfer
  // them over now
  syncDefaultArgsWithDefinition(instV, instTI);

  // remove the template argument scopes
  deleteTemplateArgBindings();

  if (instV->funcDefn->dflags & DF_INLINE_DEFN) {
    popDeclarationScopes(instV, defnScope);
  }

  unPrepArgScopeForTemlCloneTcheck(poppedScopes, pushedScopes);
  xassert(poppedScopes.isEmpty() && pushedScopes.isEmpty());
}


void Env::instantiateForwardFunctions(Variable *primary)
{
  if (!primary->templateInfo()) {
    return;      // error recovery (t0275.cc)
  }

  SFOREACH_OBJLIST_NC(Variable, primary->templateInfo()->instantiations, iter) {
    Variable *inst = iter.data();
    
    if (inst->templateInfo()->instantiateBody) {
      instantiateFunctionBody(inst);
    }
  }
}


// ----------------- class template instantiation -------------
bool contains_STA_NONE(SObjList<STemplateArgument> const &args)
{
  SFOREACH_OBJLIST(STemplateArgument, args, iter) {
    if (iter.data()->kind == STemplateArgument::STA_NONE) {
      return true;
    }
  }
  return false;
}


// Get or create an instantiation Variable for a class template.
// Note that this does *not* instantiate the class body; instead,
// instantiateClassBody() has that responsibility.
//
// Return NULL if there is a problem with the arguments.
Variable *Env::instantiateClassTemplate
  (SourceLoc loc,                             // location of instantiation request
   Variable *primary,                         // template primary to instantiate
   SObjList<STemplateArgument> const &origPrimaryArgs)  // arguments to apply to 'primary'
{
  if (contains_STA_NONE(origPrimaryArgs)) {
    return NULL;
  }

  // I really don't know what's the best place to do this, but I
  // need it here so this is a start...
  primary = primary->skipAlias();

  TemplateInfo *primaryTI = primary->templateInfo();
  xassert(primaryTI->isPrimary());

  // the arguments should be concrete
  if (containsVariables(origPrimaryArgs))
    return NULL;

  // Augment the supplied arguments with defaults from the primary
  // (note that defaults on a specialization are not used, and are
  // consequently illegal [14.5.4 para 10]).
  //
  // This also checks whether the arguments match the parameters,
  // and returns false if they do not.
  ObjList<STemplateArgument> owningPrimaryArgs;
  if (!supplyDefaultTemplateArguments(primaryTI, owningPrimaryArgs,
                                      origPrimaryArgs)) {
    return NULL;
  }

  // *still* should be concrete, even after supplying defaults
  if (containsVariables(owningPrimaryArgs))
    return NULL;

  // find the specialization that should be used (might turn
  // out to be the primary; that's fine)
  Variable *spec = findMostSpecific(primary, owningPrimaryArgs);
  TemplateInfo *specTI = spec->templateInfo();
  if (specTI->isCompleteSpec()) {
    return spec;      // complete spec; good to go
  }

  // if this is a partial specialization, we need the arguments
  // to be relative to the partial spec before we can look for
  // the instantiation
  ObjList<STemplateArgument> owningPartialSpecArgs;
  if (spec != primary) {
    xassertdb(specTI->isPartialSpec());
    mapPrimaryArgsToSpecArgs(spec, owningPartialSpecArgs, owningPrimaryArgs);
  }

  // The code below wants to use SObjLists, and since they are happy
  // accepting const versions, this is safe.  An alternative fix would
  // be to push owningness down into those interfaces, but I'm getting
  // tired of doing that ...
  SObjList<STemplateArgument> const &primaryArgs =     // non-owning
    objToSObjListC(owningPrimaryArgs);

  // non-owning version of this too..
  SObjList<STemplateArgument> const &partialSpecArgs =
    objToSObjListC(owningPartialSpecArgs);

  // look for an existing instantiation that has the right arguments
  Variable *inst = spec==primary?
    findInstantiation(specTI, owningPrimaryArgs) :
    findInstantiation(specTI, owningPartialSpecArgs);
  if (inst) {
    return inst;      // found it; that's all we need
  }

  // since we didn't find an existing instantiation, we have to make
  // one from scratch
  if (spec==primary) {
    TRACE("template", "instantiating class decl: " <<
                      primary->fullyQualifiedName() << sargsToString(primaryArgs));
  }
  else {
    TRACE("template", "instantiating partial spec decl: " <<
                      primary->fullyQualifiedName() <<
                      sargsToString(specTI->arguments) <<
                      sargsToString(partialSpecArgs));
  }

  // create the CompoundType
  CompoundType const *specCT = spec->type->asCompoundType();
  CompoundType *instCT = tfac.makeCompoundType(specCT->keyword, specCT->name);
  instCT->forward = true;
  instCT->instName = str(stringc << specCT->name << sargsToString(primaryArgs));
  instCT->parentScope = specCT->parentScope;

  // wrap the compound in a regular type
  Type *instType = makeType(instCT);

  // create the representative Variable
  inst = makeInstantiationVariable(spec, instType);

  // this also functions as the implicit typedef for the class,
  // though it is not entered into any scope
  instCT->typedefVar = inst;

  // also make the self-name, which *does* go into the scope
  // (testcase: t0167.cc)
  if (lang.compoundSelfName) {
    Variable *self = makeVariable(loc, instCT->name, instType,
                                  DF_TYPEDEF | DF_SELFNAME);
    instCT->addUniqueVariable(self);
    addedNewVariable(instCT, self);
  }

  // make a TemplateInfo for this instantiation
  TemplateInfo *instTI = new TemplateInfo(loc, inst);

  // fill in its arguments
  instTI->copyArguments(spec==primary? primaryArgs : partialSpecArgs);
  
  // if it is an instance of a partial spec, keep the primaryArgs too ...
  if (spec!=primary) {
    copyTemplateArgs(instTI->argumentsToPrimary, primaryArgs);
  }

  // attach it as an instance
  specTI->addInstantiation(inst);

  // this is an instantiation
  xassert(instTI->isInstantiation());

  return inst;
}

Variable *Env::instantiateClassTemplate
  (SourceLoc loc,
   Variable *primary,
   ObjList<STemplateArgument> const &sargs)
{
  return instantiateClassTemplate(loc, primary, objToSObjListC(sargs));
}


// defined in cc_tcheck.cc
void tcheckDeclaratorPQName(Env &env, ScopeSeq &qualifierScopes,
                            PQName *name, LookupFlags lflags);


void Env::instantiateClassBody(Variable *inst)
{
  TemplateInfo *instTI = inst->templateInfo();
  CompoundType *instCT = inst->type->asCompoundType();
  xassert(instCT->forward);     // otherwise already instantiated!

  Variable *spec = instTI->instantiationOf;
  TemplateInfo *specTI = spec->templateInfo();
  CompoundType *specCT = spec->type->asCompoundType();
                              
  // used only if it turns out that 'specTI' is a partial instantiation
  CompoundType *origCT = NULL;

  TRACE("template", "instantiating " <<
                    (specTI->isPrimary()? "class" : "partial spec") <<
                    " body: " << instTI->templateName());

  // defnScope: the scope where the class definition appeared
  Scope *defnScope = NULL;

  // do we have a function definition already?
  if (instCT->syntax) {
    // inline definition
    defnScope = instTI->defnScope;
  }
  else if (specCT->syntax) {
    // out-of-line definition; must clone the spec's definition
    instCT->syntax = specCT->syntax->clone();
    defnScope = specTI->defnScope;
  }
  else if (specTI->isPartialInstantiation()) {
    // go look at the thing from which this was partial instantiated,
    // in search of a definition (in/t0548.cc)
    //
    // TODO: This is an unfortunate hack.  I end up treating out-of-line
    // definitions of member template classes quite differently from
    // inline definitions of the same.  However, I didn't think about
    // these issues when designing the template mechanism, and they just
    // don't fit right.  At some point it would be good to reimplement
    // the whole thing, taking this stuff into account.
    TemplateInfo *origTI = specTI->partialInstantiationOf->templateInfo();
    origCT = specTI->partialInstantiationOf->type->asCompoundType();
    if (origCT->syntax) {
      instCT->syntax = origCT->syntax->clone();
      defnScope = origTI->defnScope;
    }
  }

  if (!instCT->syntax) {
    error(stringc << "attempt to instantiate `" << instTI->templateName()
                  << "', but no definition has been provided for `"
                  << specTI->templateName() << "'");
    return;
  }
  xassert(defnScope);

  // isolate context
  InstantiationContextIsolator isolator(*this, loc());

  // bind the template arguments in scopes so that when we tcheck the
  // body, lookup will find them

  // set up the scopes in a way similar to how it was when the
  // template definition was first seen
  ObjList<SavedScopePair> poppedScopes;
  SObjList<Scope> pushedScopes;
  prepArgScopeForTemlCloneTcheck(poppedScopes, pushedScopes, defnScope);

  // bind the template arguments
  insertTemplateArgBindings(spec, instTI->arguments);

  // check the type tag, and push qualifier scopes
  ScopeSeq qualifierScopes;
  tcheckDeclaratorPQName(env, qualifierScopes, instCT->syntax->name, LF_DECLARATOR);

  // the instantiation is will be complete; I think we must do this
  // before checking into the compound to avoid repeatedly attempting
  // to instantiate this class
  instCT->forward = false;
  instCT->syntax->ctype = instCT;

  // bhackett: watch for a template class recursively instantiating itself
  // with different arguments, same as with delayed function instantiation.

  static string enclosing_instantiation;

  if (enclosing_instantiation != inst->name) {
    string old_enclosing = enclosing_instantiation;
    enclosing_instantiation = inst->name;

    // check the class body, forcing it to use 'instCT'; don't check
    // method bodies
    Restorer<bool> r(checkFunctionBodies, false);
    instCT->syntax->tcheckIntoCompound(*this, DF_NONE, instCT);

    enclosing_instantiation = old_enclosing;
  }
  else {
    warning(stringc << "recursive instantiation blocked for: " << inst->name);
  }

  // Now, we've just tchecked the clone in an environment that
  // makes all the type variables map to concrete types, so we
  // now have a nice, ordinary, non-template class with a bunch
  // of members.  But there is information stored in the
  // original AST that needs to be transferred over to the
  // clone, namely information about out-of-line definitions.
  // We need both the Function pointers and the list of template
  // params used at the definition site (since we have arguments
  // but don't know what names to bind them to).  So, walk over
  // both member lists, transferring information as necessary.
  if (!origCT) {
    transferTemplateMemberInfo(loc(), specCT->syntax, instCT->syntax,
                               instTI->arguments);
  }
  else {
    // this is the case above where we bypassed 'specCT', which is a
    // partial instanitation; first combine the arguments from the
    // partial inst with those from 'instTI'
    ObjList<STemplateArgument> combinedArgs;
    copyTemplateArgs(combinedArgs, specTI->arguments /*partial inst args*/);
    copyTemplateArgs(combinedArgs, instTI->arguments);

    // now transfer member info from the original
    transferTemplateMemberInfo(loc(), origCT->syntax, instCT->syntax,
                               combinedArgs);
  }

  // restore the scopes
  env.retractScopeSeq(qualifierScopes);
  deleteTemplateArgBindings();
  unPrepArgScopeForTemlCloneTcheck(poppedScopes, pushedScopes);
  xassert(poppedScopes.isEmpty() && pushedScopes.isEmpty());
}


// this is for 14.7.1 para 4, among other things
void Env::ensureClassBodyInstantiated(CompoundType *ct)
{
  if (!ct->isComplete() && ct->isInstantiation()) {
    Variable *inst = ct->typedefVar;

    // 2005-04-17: in/k0053.cc: we would like to instantiate this
    // template, but if there has not yet been a definition, then skip
    // it (without error)
    TemplateInfo *instTI = inst->templateInfo();
    Variable *spec = instTI->instantiationOf;
    CompoundType *specCT = spec->type->asCompoundType();
    if (specCT->forward) {
      TRACE("template", "would like to instantiate body of " <<
                        instTI->templateName() <<
                        ", but no template defn available");
      return;
    }

    instantiateClassBody(inst);
  }
}

// given a function type whose parameters are about to be considered
// for various conversions, make sure that all relevant template
// classes are instantiated
void Env::instantiateTemplatesInParams(FunctionType *ft)
{
  SFOREACH_OBJLIST(Variable, ft->params, iter) {
    Type *paramType = iter.data()->type;
    if (paramType->asRval()->isCompoundType()) {
      ensureClassBodyInstantiated(paramType->asRval()->asCompoundType());
    }
  }
}


void Env::instantiateForwardClasses(Variable *baseV)
{
  SFOREACH_OBJLIST_NC(Variable, baseV->templateInfo()->instantiations, iter) {
    instantiateClassBody(iter.data());
  }
}


// return false on error
bool Env::supplyDefaultTemplateArguments
  (TemplateInfo *primaryTI,
   ObjList<STemplateArgument> &dest,          // arguments to use for instantiation
   SObjList<STemplateArgument> const &src)    // arguments supplied by user
{
  // since default arguments can refer to earlier parameters,
  // maintain a map of the arguments known so far
  MType map(env);

  // simultanously iterate over arguments and parameters, building
  // 'dest' as we go
  SObjListIter<Variable> paramIter(primaryTI->params);
  SObjListIter<STemplateArgument> argIter(src);
  while (!paramIter.isDone()) {
    Variable const *param = paramIter.data();

    STemplateArgument *arg = NULL;     // (owner)

    // take argument from explicit list?
    if (!argIter.isDone()) {
      arg = argIter.data()->shallowClone();
      argIter.adv();

      // TODO: check that this argument matches the template parameter
    }

    // default?
    else {
      arg = makeDefaultTemplateArgument(paramIter.data(), map);
      if (arg) {
        TRACE("template", "supplied default argument `" <<
                          arg->toString() << "' for param `" <<
                          param->name << "'");
      }
    }

    if (!arg) {
      error(stringc << "no argument supplied for template parameter `"
                    << param->name << "'");
      return false;
    }

    // save this argument
    dest.append(arg);
    if (param->name) {
      map.setBoundValue(param->name, *arg);
    }

    paramIter.adv();
  }

  if (!argIter.isDone()) {
    error(stringc << "too many arguments supplied to template `"
                  << primaryTI->templateName() << "'");
    return false;
  }

  return true;
}


// moved Env::makeDefaultTemplateArgument into notopt.cc


void Env::setSTemplArgFromExpr(STemplateArgument &sarg, Expression *expr)
{
  // see cppstd 14.3.2 para 1

  if (expr->type->containsGeneralizedDependent()) {
    // then certainly the value is dependent too, right?  in/k0003.cc
    sarg.setDepExpr(expr);
    return;
  }

  // TODO/BUG: I am basically saying that if a template argument can
  // be const-eval'd, then it is an integer argument.  But it might be
  // that the user is intending to pass a const-eval'able variable as
  // a reference argument, in which case this code will do the wrong
  // thing.  (in/t0509.cc)
  //
  // In general, this computation must also be told what type the
  // corresponding template *parameter* has.

  // (in/t0552.cc) maybe this is an enumerator?
  if (expr->skipGroups()->isE_variable()) {
    Variable *var = expr->skipGroups()->asE_variable()->var;
    if (var && var->hasFlag(DF_ENUMERATOR)) {
      sarg.setEnumerator(var);
      return;
    }
  }

  Type *rvalType = expr->type->asRval();
  if (rvalType->isIntegerType() ||
      rvalType->isBool() ||
      rvalType->isEnumType()) {
    // attempt to const-eval this expression
    ConstEval cenv(env.dependentVar);
    CValue val = expr->constEval(cenv);
    if (val.isDependent()) {
      sarg.setDepExpr(expr);
    }
    else if (val.isIntegral()) {
      sarg.setInt(val.getIntegralValue());
    }
    else if (val.isError()) {
      if (expr->type->isReference()) {
        goto handle_reference;         // second chance
      }
      else {
        env.error(stringc
          << "cannot evaluate `" << expr->exprToString()
          << "' as a template integer argument: " << *val.getWhy());
        delete val.getWhy();
      }
    }
    else {
      xassert(val.isFloat());
      env.error("cannot use float type as template argument");
    }
  }

  else if (expr->type->isReference()) {
  handle_reference:
    if (expr->isE_variable()) {
      // TODO: 14.3.2p1 says you can only use variables with
      // external linkage
      sarg.setReference(expr->asE_variable()->var);
    }
    else {
      env.error(stringc
        << "`" << expr->exprToString() << "' must be a simple variable "
        << "for it to be a template reference argument");
    }
  }

  else if (expr->type->isPointer()) {
    if (expr->isE_addrOf() &&
        expr->asE_addrOf()->expr->isE_variable()) {
      // TODO: 14.3.2p1 says you can only use variables with
      // external linkage
      sarg.setPointer(expr->asE_addrOf()->expr->asE_variable()->var);
    }
    else if (expr->isE_variable() &&
             expr->asE_variable()->var->isTemplateParam()) {
      sarg.setPointer(expr->asE_variable()->var);
    }
    else {
      // TODO: This is wrong; the '&' is optional for arrays.
      env.error(stringc
        << "`" << expr->exprToString() << " must be the address of a "
        << "simple variable for it to be a template pointer argument");
    }
  }

  else if (expr->type->isFunctionType()) {
    // implicitly take its address [14.3.2p5b4] (in/t0561.cc)
    if (expr->isE_variable()) {
      // TODO: 14.3.2p1 says you can only use functions with
      // external linkage
      sarg.setPointer(expr->asE_variable()->var);
    }
    else {
      env.error(stringc
        << "`" << expr->exprToString() << " must be the name of a "
        << "function for it to be a template pointer argument");
    }
  }

  else if (expr->type->isPointerToMemberType()) {
    // this check is identical to the case above, but combined with
    // the inferred type it checks for a different syntax
    if (expr->isE_addrOf() &&
        expr->asE_addrOf()->expr->isE_variable()) {
      sarg.setMember(expr->asE_addrOf()->expr->asE_variable()->var);
    }
    else {
      env.error(stringc
        << "`" << expr->exprToString() << " must be the address of a "
        << "class member for it to be a template pointer argument");
    }
  }

  else {
    env.error(expr->type, stringc
      << "`" << expr->exprToString() << "' has type `"
      << expr->type->toString() << "' but that's not an allowable "
      << "type for a non-type template argument");
  }
}


// This function is intended to do what the above would do if given
// an E_variable wrapped around this 'var', except it cannot tolerate
// yielding a dependent expression.
STemplateArgument Env::variableToSTemplateArgument(Variable *var)
{
  STemplateArgument ret;

  // try to evaluate to an integer
  ConstEval cenv(env.dependentVar);
  CValue val = cenv.evaluateVariable(var);
  if (val.isIntegral()) {
    ret.setInt(val.getIntegralValue());
  }
  else {
    // just assume it's a reference; this is wrong, like above, because
    // we really should be taking into account the parameter type
    ret.setReference(var);
  }

  return ret;
}


// 2005-08-12: After considerable struggles to get out-of-line defns
// of member template classes to work (and even that is just working
// in some simple cases that I happen to test), I now realize that the
// idea of transferring member info is fundamentally flawed.
//
// Rather than "pushing" information down to the members, I should
// always "pull" it from the container when needed.  That is, rather
// than making the data complicated, I should put the complication
// into the queries.
//
// The reason is (in retrospect) obvious: data is shared across all
// contexts, whereas queries are context-sensitive.  It's easy to make
// adjustments to queries to compensate for this or that wrinkle, but
// anytime I change the data invariants I have to consider all queries
// simultaneously.  In practice, this often means several cycles of
// trying things and running through the regressions to see what
// breaks.  It's inefficient and unsatisfying.
//
// So what I should do at some point is simplify the data design so
// that it records the minimum amount of information needed to support
// the queries.  When I see a definition of something previously
// declared, connect them, but then rely on users of the declaration
// to indirect through it to find the definition, rather than eagerly
// propagating the definition to the users (primarily, members of
// instantiations).


// transfer template info from members of 'source' to corresp.
// members of 'dest'; 'dest' is a clone of 'source'
//
// see comments above
void Env::transferTemplateMemberInfo
  (SourceLoc instLoc, TS_classSpec *source,
   TS_classSpec *dest, ObjList<STemplateArgument> const &sargs)
{
  // simultanous iteration
  ASTListIterNC<Member> srcIter(source->members->list);
  ASTListIterNC<Member> destIter(dest->members->list);

  for (; !srcIter.isDone() && !destIter.isDone();
         srcIter.adv(), destIter.adv()) {
    if (srcIter.data()->isMR_decl()) {
      Declaration *srcDecl = srcIter.data()->asMR_decl()->d;
      Declaration *destDecl = destIter.data()->asMR_decl()->d;

      if (srcDecl->dflags & DF_FRIEND) {
        continue;     // skip whole declaration for friends (t0262.cc)
      }

      // associate the type specifiers
      transferTemplateMemberInfo_typeSpec(instLoc, srcDecl->spec, source->ctype,
                                          destDecl->spec, sargs);

      // simultanously iterate over the declarators
      FakeList<Declarator> *srcDeclarators = srcDecl->decllist;
      FakeList<Declarator> *destDeclarators = destDecl->decllist;

      for (; srcDeclarators->isNotEmpty() && destDeclarators->isNotEmpty();
             srcDeclarators = srcDeclarators->butFirst(),
             destDeclarators = destDeclarators->butFirst()) {
        Variable *srcVar = srcDeclarators->first()->var;
        Variable *destVar = destDeclarators->first()->var;

        // transfer info for member functions and static data
        //
        // 2005-08-13: Ouch!  It turns out I really haven't
        // implemented instantiation of static data members of class
        // templates at all, so the required data structures are
        // simply not present to let me fix in/t0554.cc, which
        // requires (among other things) turning on the 'isStatic'
        // possibility below.
        //
        // TODO: Implement instantiation of static data members.
        if (!srcVar->isType()) {
          if (srcVar->type->isFunctionType() /*|| srcVar->isStatic()*/) {
            // srcVar -> destVar
            transferTemplateMemberInfo_one(instLoc, srcVar, destVar, sargs);
          }
        }
      }
      xassert(srcDeclarators->isEmpty() && destDeclarators->isEmpty());
    }

    else if (srcIter.data()->isMR_func()) {
      if (srcIter.data()->asMR_func()->f->dflags & DF_FRIEND) {
        // skip these.. apparently I do not have TemplateInfos on
        // them, which might itself be a mistake, but since that's the
        // case right now, must do this here (t0558.cc)
        continue;
      }

      Variable *srcVar = srcIter.data()->asMR_func()->f->nameAndParams->var;
      Variable *destVar = destIter.data()->asMR_func()->f->nameAndParams->var;

      transferTemplateMemberInfo_one(instLoc, srcVar, destVar, sargs);

      // the instance 'destVar' needs to have a 'defnScope'; it didn't
      // get set earlier b/c at the time the declaration was tchecked,
      // the Function didn't know it was an instantiation (but why is
      // that?)
      TemplateInfo *destTI = destVar->templateInfo();
      if (!destTI->defnScope) {
        destTI->defnScope = destVar->scope;
        xassert(destTI->defnScope);

        // arg.. I keep pushing this around.. maybe new strategy:
        // set defnScope and funcDefn at same time?
        destVar->funcDefn = destIter.data()->asMR_func()->f;
      }
      else {
        // this happens when 'destVar' is actually a partial instantiation,
        // so the scope was set by transferTemplateMemberInfo_membert
        // when ..._one delegated to it

        // bhackett: disable
        // xassert(destTI->isPartialInstantiation());
      }
    }

    else if (srcIter.data()->isMR_template()) {
      TemplateDeclaration *srcTDecl = srcIter.data()->asMR_template()->d;
      TemplateDeclaration *destTDecl = destIter.data()->asMR_template()->d;

      // I've decided that member templates should just be treated as
      // primaries in their own right, right no relation to the
      // "original" definition, hence no action is needed!
      //
      // ah, but there is still the need to xfer the funcDefn, and to
      // find the instantiations later, for out-of-line defns, plus they
      // need to remember the template arguments.  so, I'm introducing
      // the notion of "partial instantiation"

      if (srcTDecl->isTD_decl()) {
        TypeSpecifier *srcSpec = srcTDecl->asTD_decl()->d->spec;
        if (srcSpec->isTS_classSpec() || srcSpec->isTS_elaborated()) {
          // old TD_class behavior
          transferTemplateMemberInfo_typeSpec(instLoc,
            srcSpec, source->ctype,
            destTDecl->asTD_decl()->d->spec, sargs);
        }
        else if (srcTDecl->asTD_decl()->d->dflags & DF_FRIEND) {
          // (k0056.cc) source declaration is a friend... I *think* I
          // just want to ignore it here... if I don't, then the
          // member transfer logic gets confused by the fact that the
          // presence and checkedness of the definition is independent
          // of this template class's state (because the friend is not
          // actually a memebr)
        }
        else {
          // old TD_proto behavior
          Variable *srcVar = srcTDecl->asTD_decl()->d->decllist->first()->var;
          Variable *destVar = destTDecl->asTD_decl()->d->decllist->first()->var;

          transferTemplateMemberInfo_membert(instLoc, srcVar, destVar, sargs);
        }
      }

      else if (srcTDecl->isTD_func()) {
        Variable *srcVar = srcTDecl->asTD_func()->f->nameAndParams->var;
        Variable *destVar = destTDecl->asTD_func()->f->nameAndParams->var;

        transferTemplateMemberInfo_membert(instLoc, srcVar, destVar, sargs);
      }

      else if (srcTDecl->isTD_tmember()) {
        // not sure if this would even parse... if it does I don't
        // know what it might mean
        error("more than one template <...> declaration inside a class body?");
      }

      else {
        xfailure("unknown TemplateDeclaration kind");
      }
    }

    else {
      // other kinds of member decls: don't need to do anything
    }
  }

  // one is clone of the other, so same length lists
  xassert(srcIter.isDone() && destIter.isDone());
}


// transfer specifier info, particularly for nested class or
// member template classes
void Env::transferTemplateMemberInfo_typeSpec
  (SourceLoc instLoc, TypeSpecifier *srcTS, CompoundType *sourceCT,
   TypeSpecifier *destTS, ObjList<STemplateArgument> const &sargs)
{
  if (srcTS->isTS_elaborated()) {
    Variable *srcVar = srcTS->asTS_elaborated()->atype->typedefVar;
    Variable *destVar = destTS->asTS_elaborated()->atype->typedefVar;

    if (srcVar->scope == sourceCT) {
      // just a forward decl, do the one element
      transferTemplateMemberInfo_one(instLoc, srcVar, destVar, sargs);
    }
    else {
      // this isn't a declaration of a type that is a member of the
      // relevant template, it is just a reference to some other type;
      // ignore it
    }
  }

  else if (srcTS->isTS_classSpec()) {
    TS_classSpec *srcCS = srcTS->asTS_classSpec();
    TS_classSpec *destCS = destTS->asTS_classSpec();

    // connect the classes themselves
    if (srcCS->ctype && destCS->ctype)
      transferTemplateMemberInfo_one(instLoc,
        srcCS->ctype->typedefVar,
        destCS->ctype->typedefVar, sargs);

    // connect their members
    transferTemplateMemberInfo(instLoc, srcCS, destCS, sargs);
  }

  else {
    // other kinds of type specifiers: don't need to do anything
  }
}


// transfer template information from primary 'srcVar' to
// instantiation 'destVar'
void Env::transferTemplateMemberInfo_one
  (SourceLoc instLoc, Variable *srcVar, Variable *destVar,
   ObjList<STemplateArgument> const &sargs)
{
  // bhackett: disable
  // xassert(srcVar != destVar);
  if (srcVar == destVar)
    return;

  // bit of a hack: if 'destVar' already has templateInfo, then it's
  // because it is a member template (or a member of a member
  // template), and we got here by recursively calling
  // 'transferTemplateMemberInfo'; call the member template handler
  // instead
  if (destVar->templateInfo()) {
    transferTemplateMemberInfo_membert(instLoc, srcVar, destVar, sargs);
    return;
  }

  TRACE("templateXfer", "associated primary " << srcVar->toQualifiedString()
                     << " with inst " << destVar->toQualifiedString());

  // make the TemplateInfo for this member instantiation
  TemplateInfo *destTI = new TemplateInfo(instLoc);

  // copy arguments into 'destTI'
  destTI->copyArguments(sargs);

  // attach 'destTI' to 'destVar'
  destVar->setTemplateInfo(destTI);

  // 'destVar' is an instantiation of 'srcVar' with 'sargs'
  TemplateInfo *srcTI = srcVar->templateInfo();
  xassert(srcTI);
  srcTI->addInstantiation(destVar);

  // set 'destTI->uninstantiatedDefaultArgs'
  if (destVar->type->isFunctionType()) {
    destTI->uninstantiatedDefaultArgs =
      countParamsWithDefaults(destVar->type->asFunctionType());
  }
}


// this is for member templates ("membert")
void Env::transferTemplateMemberInfo_membert
  (SourceLoc instLoc, Variable *srcVar, Variable *destVar,
   ObjList<STemplateArgument> const &sargs)
{
  // what follows is a modified version of 'transferTemplateMemberInfo_one'

  // 'destVar' is a partial instantiation of 'srcVar' with 'args'
  TemplateInfo *srcTI = srcVar->templateInfo();
  xassert(srcTI);
  TemplateInfo *destTI = destVar->templateInfo();
  xassert(destTI);

  if (destTI->isInstantiation() || destTI->isPartialInstantiation()) {
    // The relevant info has already been transferred.  This happens
    // for example when an inner class is declared and then defined,
    // when we see it for the second time.
    return;
  }

  // 2005-06-09: (in/t0504.cc) prepend instead of copy, because 'destTI'
  // might be a partial instantiation (and therefore already has some
  // arguments), and we want 'sargs' to be regarded as the arguments to
  // its containing template
  destTI->prependArguments(sargs);

  srcTI->addPartialInstantiation(destVar);

  // should not have already checked this member's body even if
  // it has an inline definition

  // bhackett: disable
  // xassert(!destVar->funcDefn);

  // does the source have a definition?
  if (srcVar->funcDefn) {
    // give the definition to the dest too
    destVar->funcDefn = srcVar->funcDefn;

    // is it inline?
    if (srcVar->scope == srcTI->defnScope) {
      // then the dest's defnScope should be similarly arranged
      destTI->defnScope = destVar->scope;
    }
    else {
      // for out of line, the defn scopes of src and dest are the same
      destTI->defnScope = srcTI->defnScope;
    }
  }

  // 2005-08-12: I started to do some analogous stuff for class
  // templates, including making a copy of CompoundType::syntax, but
  // that isn't right b/c those can't be shared since they are
  // supposed to be tcheck'd before transferring member info.
  //
  // That, and I am *really* confused right now.  How the hell does
  // any of this work?

  // do this last so I have full info to print for 'destVar'
  TRACE("templateXfer", "associated primary " << srcVar->toQualifiedString()
                     << " with partial inst " << destVar->toQualifiedString());
}


// given a name that was found without qualifiers or template arguments,
// see if we're currently inside the scope of a template definition
// with that name
CompoundType *Env::findEnclosingTemplateCalled(StringRef name)
{
  FOREACH_OBJLIST(Scope, scopes, iter) {
    Scope const *s = iter.data();

    if (s->curCompound &&
        s->curCompound->templateInfo() &&
        s->curCompound->name == name) {
      return s->curCompound;
    }
  }
  return NULL;     // not found
}


// we (may) have just encountered some syntax which declares
// some template parameters, but found that the declaration
// matches a prior declaration with (possibly) some other template
// parameters; verify that they match (or complain), and then
// discard the ones stored in the environment (if any)
//
// return false if there is some problem, true if it's all ok
// (however, this value is ignored at the moment)
bool Env::verifyCompatibleTemplateParameters(Scope *scope, CompoundType *prior)
{
  bool hasParams = scope->isTemplateParamScope();
  if (hasParams && scope->parameterizedEntity) {
    // (in/t0191.cc) already parameterized.. let's pretend we didn't
    // see them (I suspect there is a deeper problem here, but maybe
    // this hack will work for the moment)
    hasParams = false;
  }

  if (!hasParams && !prior->isTemplate()) {
    // neither talks about templates, forget the whole thing
    return true;
  }

  // before going further, associate the scope's parameters
  // so that happens regardless of the decision here
  if (hasParams) {
    scope->setParameterizedEntity(prior->typedefVar);
  }

  if (!hasParams && prior->isTemplate()) {
    error(stringc
      << "prior declaration of " << prior->keywordAndName()
      << " at " << prior->typedefVar->loc
      << " was templatized with parameters "
      << prior->templateInfo()->paramsToCString()
      << " but the this one is not templatized",
      EF_DISAMBIGUATES);
    return false;
  }

  if (hasParams &&
      scope->templateParams.isNotEmpty() &&      // t0252.cc
      !prior->isTemplate()) {
    if (prior->isInstantiation()) {
      // in/t0510.cc: 'prior' is an instantiation, so the parameters
      // were referring to the template primary
      prior = prior->templateInfo()->getPrimary()->var->type->asCompoundType();
    }
    else {
      error(stringc
        << "prior declaration of " << prior->keywordAndName()
        << " at " << prior->typedefVar->loc
        << " was not templatized, but this one is, with parameters "
        << paramsToCString(scope->templateParams),
        EF_DISAMBIGUATES);
      return false;
    }
  }

  // now we know both declarations have template parameters;
  // check them for naming equivalent types
  //
  // furthermore, fix the names in 'prior' in case they differ
  // with those of 'scope->curTemplateParams'
  //
  // even more, merge their default arguments
  TemplateInfo *priorTI = prior->templateInfo();
  if (!mergeParameterLists(prior->typedefVar,
                           priorTI->params,            // dest
                           scope->templateParams)) {   // src
    return false;
  }

  // furthermore, do the same for inherited parameters (this
  // appears to be the nominal intent of mergeTemplateInfos(),
  // but that function is never called...) (in/t0441.cc)
  //
  // this will walk the list of inherited parameter lists in 'prior'
  ObjListIterNC<InheritedTemplateParams> inhParamIter(priorTI->inheritedParams);

  // this is clumsy; I have 'scope', but I need to find it in
  // the scope stack so I can look at the ones that precede it
  SObjList<Scope const> paramScopes;
  {
    ObjListIter<Scope> scopeIter(this->scopes);
    while (scopeIter.data() != scope) {
      scopeIter.adv();
    }
    scopeIter.adv();

    // I want to compare 'inhParamIter' to the parameter scopes above
    // 'scope'; except they're in the opposite orders, so first collect
    // and reverse the scopes
    for (; !scopeIter.isDone(); scopeIter.adv()) {
      if (scopeIter.data()->isTemplateParamScope()) {
        paramScopes.prepend(scopeIter.data());
      }
    }
  }
  SObjListIter<Scope const> scopeIter(paramScopes);

  // merge corresponding parameter lists
  while (!inhParamIter.isDone() && !scopeIter.isDone()) {
    if (!mergeParameterLists(prior->typedefVar,
                             inhParamIter.data()->params,         // dest
                             scopeIter.data()->templateParams)) { // src
      return false;
    }

    inhParamIter.adv();
    scopeIter.adv();
  }

  // should end at same time
  if (!inhParamIter.isDone() || !scopeIter.isDone()) {
    // TODO: expand this message
    env.error(stringc << "wrong # of template param lists in declaration of "
                      << prior->name);
  }

  return true;
}


// context: I have previously seen a (forward) template
// declaration, such as
//   template <class S> class C;             // dest
//                   ^
// and I want to modify it to use the same names as another
// declaration later on, e.g.
//   template <class T> class C { ... };     // src
//                   ^
// since in fact I am about to discard the parameters that
// come from 'src' and simply keep using the ones from
// 'dest' for future operations, including processing the
// template definition associated with 'src'
bool Env::mergeParameterLists(Variable *prior,
                              SObjList<Variable> &destParams,
                              SObjList<Variable> const &srcParams)
{
  // if 'prior' is actually a definition, then don't make any changes
  bool priorIsDefn = !prior->type->asCompoundType()->forward;

  TRACE("templateParams", "mergeParameterLists: prior=" << prior->name
    << ", dest=" << paramsToCString(destParams)
    << ", src=" << paramsToCString(srcParams)
    << ", priorIsDefn=" << priorIsDefn);

  // keep track of whether I've made any naming changes
  // (alpha conversions)
  bool anyNameChanges = false;

  SObjListMutator<Variable> destIter(destParams);
  SObjListIter<Variable> srcIter(srcParams);
  for (; !destIter.isDone() && !srcIter.isDone();
       destIter.adv(), srcIter.adv()) {
    Variable *dest = destIter.data();
    Variable const *src = srcIter.data();

    // are the types equivalent?
    if (!equalOrIsomorphic(dest->type, src->type)) {
      error(stringc
        << "prior declaration of " << prior->toString()
        << " at " << prior->loc
        << " was templatized with parameter `"
        << dest->name << "' of type `" << dest->type->toString()
        << "' but this one has parameter `"
        << src->name << "' of type `" << src->type->toString()
        << "', and these are not equivalent",
        EF_DISAMBIGUATES);
      return false;
    }

    // what's up with their default arguments?
    if (dest->value && src->value) {
      // this message could be expanded...
      error("cannot specify default value of template parameter more than once");
      return false;
    }

    // there is a subtle problem if the prior declaration has a
    // default value which refers to an earlier template parameter,
    // but the name of that parameter has been changed
    // bhackett: disabled
    /*
    if (anyNameChanges &&              // earlier param changed
        dest->value) {                 // prior has a value
      // leave it as a to-do for now; a proper implementation should
      // remember the name substitutions done so far, and apply them
      // inside the expression for 'dest->value'
      xfailure("unimplemented: alpha conversion inside default values"
               " (workaround: use consistent names in template parameter lists)");
    }
    */

    // merge their default values
    if (src->value && !dest->value) {
      dest->value = src->value;
    }

    // do they use the same name?
    if (!priorIsDefn &&
        dest->name != src->name) {
      // make the names the same
      TRACE("templateParams", "changing parameter " << dest->name
        << " to " << src->name);
      anyNameChanges = true;

      // Make a new Variable to hold the modified parameter.  I'm not
      // sure this is the right thing to do, b/c I'm concerned about
      // the fact that the original decl will be pointing at the old
      // Variable, but if I modify it in place I've got the problem
      // that the template params for a class are shared by all its
      // members, so I'd be changing all the members' params too.
      // Perhaps it's ok to make a few copies of template parameter
      // Variables, as they are somehow less concrete than the other
      // named entities...
      Variable *v = makeVariable(dest->loc, src->name, src->type, dest->flags);
      
      // copy a few other fields, including default value
      v->value = dest->value;
      v->defaultParamType = dest->defaultParamType;
      v->scope = dest->scope;
      v->setScopeKind(dest->getScopeKind());

      // replace the old with the new
      destIter.dataRef() = v;
    }
  }

  if (srcIter.isDone() && destIter.isDone()) {
    return true;   // ok
  }
  else {
    error(stringc
      << "prior declaration of " << prior->toString()
      << " at " << prior->loc
      << " was templatized with "
      << pluraln(destParams.count(), "parameter")
      << ", but this one has "
      << pluraln(srcParams.count(), "parameter"),
      EF_DISAMBIGUATES);
    return false;
  }
}


// 2005-08-12: There are no call sites for this function.  There is
// now code at the end of verifyCompatibleTemplateParameters that does
// essentially the same thing.  However, I will leave this here
// because this code looks cleaner, and it is possible that at some
// point I will discover how to plug this function in to the design,
// thereby letting me delete the mess in the other function.
bool Env::mergeTemplateInfos(Variable *prior, TemplateInfo *dest,
                             TemplateInfo const *src)
{
  bool ok = mergeParameterLists(prior, dest->params, src->params);

  // sync up the inherited parameters too
  ObjListIterNC<InheritedTemplateParams> destIter(dest->inheritedParams);
  ObjListIter<InheritedTemplateParams> srcIter(src->inheritedParams);

  for (; !destIter.isDone() && !srcIter.isDone();
         destIter.adv(), srcIter.adv()) {
    if (!mergeParameterLists(prior, destIter.data()->params, srcIter.data()->params)) {
      ok = false;
    }
  }

  if (!destIter.isDone() || !srcIter.isDone()) {
    // TODO: expand this error message
    error("differing number of template parameter lists");
    ok = false;
  }

  return ok;
}


// ------------ BEGIN: applyArgumentMap -------------
// The algorithm in this section is doing what is specified by
// 14.8.2p2b3, substitution of template arguments for template
// parameters in a type.  'src' is the type containing references
// to the parameters, 'map' binds parameters to arguments, and
// the return value is the type with substitutions performed.
Type *Env::applyArgumentMapToType(MType &map, Type *origSrc)
{
  // my intent is to not modify 'origSrc', so I will use 'src', except
  // when I decide to return what I already have, in which case I will
  // use 'origSrc'
  Type const *src = origSrc;

  switch (src->getTag()) {
    default: xfailure("bad tag");

    case Type::T_ATOMIC: {
      CVAtomicType const *scat = src->asCVAtomicTypeC();
      Type *ret = applyArgumentMapToAtomicType(map, scat->atomic, scat->cv);
      if (!ret) {
        return origSrc;      // use original
      }
      else {
        return ret;
      }
    }

    case Type::T_POINTER: {
      PointerType const *spt = src->asPointerTypeC();
      return tfac.makePointerType(spt->cv,
        applyArgumentMapToType(map, spt->atType));
    }

    case Type::T_REFERENCE: {
      ReferenceType const *srt = src->asReferenceTypeC();
      return tfac.makeReferenceType(applyArgumentMapToType(map, srt->atType));
    }

    case Type::T_FUNCTION: {
      FunctionType const *sft = src->asFunctionTypeC();
      FunctionType *rft = tfac.makeFunctionType(applyArgumentMapToType(map, sft->retType));

      // copy parameters
      SFOREACH_OBJLIST(Variable, sft->params, iter) {
        Variable const *sp = iter.data();
        Variable *rp = makeVariable(sp->loc, sp->name,
          applyArgumentMapToType(map, sp->type), sp->flags);
          
        if (sp->value) {
          // TODO: I should be substituting the template parameters
          // in the default argument too... but for now I will just
          // use it without modification
          rp->value = sp->value;
        }

        rft->addParam(rp);
      }
      doneParams(rft);

      rft->flags = sft->flags;

      if (rft->exnSpec) {
        // TODO: this
        //
        // Note: According to 14.8.2p2b3, if mapping the exception types
        // leads to a failure, that is only diagnosed when the function
        // *definition* is instantiated.  Thus, my tentative plan here is
        // to attempt to do the map here, and if it fails, store ST_ERROR.
        // Later, if/when I instantate the definition, check for ST_ERROR
        // and diagnose it then (hmm, by then I will have lost the error
        // message itself ...).
        xunimp("applyArgumentMap: exception spec");
      }

      return rft;
    }

    case Type::T_ARRAY: {
      ArrayType const *sat = src->asArrayTypeC();

      Type *new_eltType = applyArgumentMapToType(map, sat->eltType);

      int size = sat->size;
      if (sat->depType) {
        xassert(sat->size == ArrayType::DEP_SIZE);

        STemplateArgument sarg = map.getBoundValue(sat->depType->name, tfac);
        if (sarg.isInt())
          size = sarg.getInt();
      }

      return tfac.makeArrayType(new_eltType, size);
    }

    case Type::T_POINTERTOMEMBER: {
      PointerToMemberType const *spmt = src->asPointerToMemberTypeC();
      
      // slightly tricky mapping the 'inClassNAT' since we need to make
      // sure the mapped version is still a NamedAtomicType
      Type *retInClassNAT =
        applyArgumentMapToAtomicType(map, spmt->inClassNAT, CV_NONE);
      if (!retInClassNAT) {
        // use original 'spmt->inClassNAT'
        return tfac.makePointerToMemberType
          (spmt->inClassNAT,
           spmt->cv,
           applyArgumentMapToType(map, spmt->atType));
      }
      else if (!retInClassNAT->isCompoundType()) {
        // 14.8.2p2b3.6
        xTypeDeduction(stringc 
          << "during construction of pointer-to-member, type `" 
          << retInClassNAT->toString() << "' is not a class");
      }
      else {
        return tfac.makePointerToMemberType
          (retInClassNAT->asCompoundType(),
           spmt->cv,
           applyArgumentMapToType(map, spmt->atType));
      }
    }
  }
}

Type *Env::applyArgumentMapToAtomicType
  (MType &map, AtomicType *origSrc, CVFlags srcCV)
{
  AtomicType const *src = origSrc;

  if (src->isTypeVariable()) {
    TypeVariable const *stv = src->asTypeVariableC();

    STemplateArgument replacement = map.getBoundValue(stv->name, tfac);
    if (!replacement.hasValue()) {
      // I can trigger these when there is a preceding error;
      // an example is in/t0517.cc error 1
      xTypeDeduction(stringc << "the type name `"
                             << stv->name << "' is not bound");
    }
    else if (!replacement.isType()) {
      xTypeDeduction(stringc << "the type name `"
                             << stv->name << "' is bound to a non-type argument");
    }

    // take what we got and apply the cv-flags that were associated
    // with the type variable, e.g. "T const" -> "int const"
    return applyArgumentMap_applyCV(srcCV, replacement.getType());
  }

  else if (src->isPseudoInstantiation()) {
    PseudoInstantiation const *spi = src->asPseudoInstantiationC();

    // build a concrete argument list, so we can make a real instantiation
    ObjList<STemplateArgument> args;
    applyArgumentMapToTemplateArgs(map, args, spi->args);

    // instantiate the class with our newly-created arguments
    Variable *instClass = instantiateClassTemplate_or_PI(spi->primary, args);
    if (!instClass) {
      instClass = errorVar;    // error already reported; this is recovery
    }

    // apply the cv-flags and return it
    return applyArgumentMap_applyCV(srcCV, instClass->type);
  }

  else if (src->isDependentQType()) {     // e.g. in/t0506.cc
    DependentQType const *sdqt = src->asDependentQTypeC();

    // resolve 'first' (this unfortunately wraps the result in an
    // extraneous CVAtomicType)
    AtomicType *retFirst =
      applyArgumentMapToAtomicType(map, sdqt->first, CV_NONE)->
        asCVAtomicType()->atomic;
    if (!retFirst->isCompoundType()) {
      // 14.8.2p2b3.3
      xTypeDeduction(stringc
        << "attempt to extract member `" << sdqt->rest->toString()
        << "' from non-class `" << retFirst->toString() << "'");
    }

    // resolve 'first'::'rest'
    return applyArgumentMap_applyCV(srcCV,
             applyArgumentMapToQualifiedType(map, retFirst->asCompoundType(),
                                             sdqt->rest));
  }

  else {
    // all others do not refer to type variables; returning NULL
    // here means to use the original unchanged
    return NULL;
  }
}

Type *Env::applyArgumentMap_applyCV(CVFlags cv, Type *type)
{
  if (type->isReferenceType()) {
    // apparently, since 14.8.1p2 doesn't explicitly prohibit
    // attempting to cv-qualify a reference, it is allowed
    // (in/t0549.cc)
    return type;
  }

  Type *ret = tfac.applyCVToType(SL_UNKNOWN, cv,
                                 type, NULL /*syntax*/);
  if (!ret) {
    // 14.8.2p2b3.9
    //
    // This might be wrong, since b3.9 discusses cv-qualification of
    // functions, but applyCVToType also does not like
    // cv-qualification of arrays.  Who should push the
    // cv-qualification down?  I'm thinking it should be applyCV...
    xTypeDeduction(stringc << "type `" << type->toString()
                           << "' cannot be cv-qualified");
  }
  else {
    return ret;     // good to go
  }
}


void Env::applyArgumentMapToTemplateArgs
  (MType &map, ObjList<STemplateArgument> &dest,
                               ObjList<STemplateArgument> const &srcArgs)
{
  xassert(dest.isEmpty());     // for prepend+reverse

  FOREACH_OBJLIST(STemplateArgument, srcArgs, iter) {
    STemplateArgument const *sta = iter.data();
    if (sta->isType()) {
      STemplateArgument *rta = new STemplateArgument;
      rta->setType(applyArgumentMapToType(map, sta->getType()));
      dest.prepend(rta);
    }
    else if (sta->isDepExpr()) {
      STemplateArgument replacement = 
        applyArgumentMapToExpression(map, sta->getDepExpr());
      dest.prepend(replacement.shallowClone());
    }
    else {
      // assume any other kind does not need to be mapped
      dest.prepend(sta->shallowClone());
    }
  }

  dest.reverse();
}


STemplateArgument Env::applyArgumentMapToExpression
  (MType &map, Expression *e)
{
  // hack: just try evaluating it first; this will only work if
  // the expression is entirely non-dependent (in/t0287.cc)
  STemplateArgument ret;
  setSTemplArgFromExpr(ret, e);
  if (!ret.isDepExpr()) {
    return ret;     // good to go
  }
  
  // TOOD: I think the right way to do this is to use the
  // constant-evaluator (which setSTemplArgFromExpr uses
  // internally), modified to use 'map'

  if (!e->isE_variable()) {
    // example: Foo<T::x + 1>, where T maps to some class 'C' that
    // has an integer constant 'x'
    //
    // TODO: my plan is to invoke the constant-expression
    // evaluator, modified to accept 'map' so it knows how to
    // handle template parameters

    // bhackett: disable
    // xunimp("applyArgumentMap: dep-expr is not E_variable");

    return ret;
  }
  E_variable *evar = e->asE_variable();

  if (evar->var->isTemplateParam()) {
    // name refers directly to a template parameter
    xassert(evar->name->isPQ_name());     // no qualifiers
    ret = map.getBoundValue(evar->var->name, tfac);
    xassert(ret.hasValue());              // map should bind it
  }
  else {
    // name must refer to a qualified name involving the template
    // parameter
    xassert(evar->var == dependentVar);
    xassert(evar->name->isPQ_qualifier());
    ret = applyArgumentMapToQualifiedName(map, evar->name->asPQ_qualifier());
    if (!ret.hasValue()) {
      // couldn't resolve; just package up as dependent name again (in/t0543.cc)
      ret.setDepExpr(e);
    }
  }

  if (!ret.isObject()) {
    xTypeDeduction(stringc
      << "the name `" << evar->name->toString()
      << "' should be bound to an object argument");
  }

  return ret;
}


// resolve 'qual' using 'map'
STemplateArgument Env::applyArgumentMapToQualifiedName
  (MType &map, PQ_qualifier *qual)
{
  // we need to know what the qualifier (ignoring template
  // args) refers to
  xassert(qual->qualifierVar);

  // combine with template args to yield a scope that we
  // can use to look up subsequent components of the name
  Scope *firstScope;
  if (qual->sargs.isEmpty()) {
    // no template arguments, so the qualifier variable
    // should be directly usable
    firstScope = qual->qualifierVar->getDenotedScope();
  }
  else {
    // apply the map to the arguments, then use them to
    // instantiate the class
    firstScope = applyArgumentMap_instClass(map, qual->qualifierVar, qual->sargs);
    if (!firstScope) {
      return STemplateArgument();     // keep pushing back to caller...
    }
  }

  // interpret the rest of the name w.r.t. the computed scope
  return applyArgumentMapToPQName(map, firstScope, qual->rest);
}

// map 'sargs', apply them to 'primary', yield result as a Scope
CompoundType *Env::applyArgumentMap_instClass
  (MType &map, Variable *primary,
   ObjList<STemplateArgument> const &sargs)
{
  // should be a template class
  xassert(primary->isTemplateClass(false /*considerInherited*/));

  // map the template arguments
  ObjList<STemplateArgument> mappedArgs;
  applyArgumentMapToTemplateArgs(map, mappedArgs, sargs);

  if (containsVariables(mappedArgs)) {
    return NULL;     // caller must deal with this
  }

  // instantiate the template with the arguments
  Variable *inst =
    instantiateClassTemplate(loc(), primary, mappedArgs);
  xassert(inst);     // can this fail?

  return inst->type->asCompoundType();
}

// resolve 'name', which is qualified with 'scope', using 'map'
STemplateArgument Env::applyArgumentMapToPQName
  (MType &map, Scope *scope, PQName *name)
{
  if (scope->curCompound) {
    applyArgumentMap_ensureComplete(scope->curCompound);
  }

  // lookups are by qualification with 'scope', and should not need
  // using-edge traversal (as it happens, LF_IGNORE_USING makes
  // LF_QUALIFIED irrelevant, but it is an accurate description of the
  // lookup context so I keep it)
  LookupFlags lflags = LF_QUALIFIED | LF_IGNORE_USING;

  // take apart the name; this isn't shared with other code that
  // does similar things because of the presence of 'map' ...
  if (name->isPQ_name()) {
    // lookup in 'scope'
    LookupSet set;
    scope->lookup(set, name->getName(), NULL /*env*/, lflags);
    if (set.isEmpty()) {
      xTypeDeduction(stringc << "failed to find `" << name->getName()
                             << "' in " << scope->scopeName());
    }
    else if (set.count() != 1) {
      // in principle I think this is legal, but would be rather difficult
      // to implement, since it means tracking down the expected type of
      // the parameter...
      xunimp("overloaded function name used as template argument in unusual circumstance");
    }

    return variableToSTemplateArgument(set.first());
  }

  else if (name->isPQ_operator()) {
    // can this happen?
    xfailure("applyArgumentMap: operator name as dependent expr?");
  }

  else if (name->isPQ_template()) {
    // NOTE: This code has not been tested.  I'm being a bit lazy
    // right now, and it would be pretty unusual (something like using
    // a qualified name of a member template function as a non-type
    // argument to a template).

    PQ_template *templ = name->asPQ_template();

    lflags |= LF_TEMPL_PRIMARY;
    Variable *v = scope->lookup_one(templ->name, NULL /*env*/, lflags);
    if (!v) {
      xTypeDeduction(stringc << "failed to find `" << templ->name
                             << "' in " << scope->scopeName());
    }
    if (!v->isTemplateClass(false /*considerInherited*/)) {
      xTypeDeduction(stringc << "`" << templ->name << "' in "
                             << scope->scopeName() << " is not a template class");
    }

    // apply the arguments
    CompoundType *ct = applyArgumentMap_instClass(map, v, templ->sargs);
    if (!ct) {
      return STemplateArgument();    // ...
    }

    // wrap in an STemplateArgument
    STemplateArgument ret;
    ret.setType(ct->typedefVar->type);
    return ret;
  }

  else {
    xassert(name->isPQ_qualifier());
    PQ_qualifier *qual = name->asPQ_qualifier();

    lflags |= LF_TEMPL_PRIMARY | LF_TYPES_NAMESPACES;
    Variable *q = scope->lookup_one(qual->qualifier, NULL /*env*/, lflags);
    if (!q) {
      xTypeDeduction(stringc << "failed to find `" << qual->qualifier
                             << "' in " << scope->scopeName());
    }
    if (!q->type->isCompoundType()) {
      xTypeDeduction(stringc << "`" << qual->qualifier << "' in "
                             << scope->scopeName() << " is not a class");
    }

    if (qual->sargs.isEmpty() && !q->isTemplate(false /*considerInherited*/)) {
      // use 'q' as a scope to process the rest
      return applyArgumentMapToPQName(map, q->getDenotedScope(), qual->rest);
    }
    else if (!qual->sargs.isEmpty() && q->isTemplate(false /*considerInherited*/)) {
      // apply the arguments to obtain a scope, and then use that
      Scope *s = applyArgumentMap_instClass(map, q, qual->sargs);
      if (!s) {
        return STemplateArgument();    // ...
      }
      return applyArgumentMapToPQName(map, s, qual->rest);
    }
    else {
      xTypeDeduction(stringc
        << "mismatch between template-ness and argument application for `"
        << qual->qualifier << "' in " << scope->scopeName());
      return STemplateArgument();    // silence warning
    }
  }
}

void Env::applyArgumentMap_ensureComplete(CompoundType *ct)
{
  // instantiate if necessary
  ensureClassBodyInstantiated(ct);

  // if the class is still incomplete (because the definition was
  // not available), I say it's another case like those mentioned
  // in 14.8.2p2b3, even though it isn't explicitly among them
  if (ct->forward) {
    xTypeDeduction(stringc
      << "attempt to access member of `" << ct->instName
      << "' but no definition has been seen");
  }
}



// We are trying to resolve 'ct'::'name', but 'name' might refer to
// type variables bound only in 'map'.
//
// This code is somewhat related to Env::resolveDQTs, but that
// function looks for bindings in the environment, and is in general a
// bit of a hack.  The code here is more principled, and does its work
// without using the environment.
//
// 2005-08-07: There is some overlap between this function and
// applyArgumentMapToQualifiedName.  Essentially, the former is for
// names of types and the latter for names of non-types.  However,
// those tasks are not sufficiently different to warrant two
// completely separate mechanisms.  Collapsing them is a TODO.
Type *Env::applyArgumentMapToQualifiedType
  (MType &map, CompoundType *ct, PQName *name)
{
  applyArgumentMap_ensureComplete(ct);

  // similar to above
  LookupFlags lflags = LF_QUALIFIED | LF_IGNORE_USING;

  if (name->isPQ_name() || name->isPQ_operator()) {
    // ordinary lookup will suffice
    Variable *var = ct->lookup_one(name->getName(), NULL /*env*/, lflags);
    if (!var || !var->isType()) {
      xTypeDeduction(stringc << "no such type: " << ct->name
                             << "::" << name->toString());
    }
    else {
      return var->type;
    }
  }

  // PQ_qualifier or PQ_template; get name and args
  StringRef memberName;
  ObjList<STemplateArgument> *srcArgs;
  if (name->isPQ_template()) {
    PQ_template *pqt = name->asPQ_template();
    memberName = pqt->name;
    srcArgs = &(pqt->sargs);
  }
  else {
    PQ_qualifier *pqq = name->asPQ_qualifier();
    memberName = pqq->qualifier;
    srcArgs = &(pqq->sargs);
  }
  xassert(memberName);     // can't refer to anon member in DQT

  // lookup the name portion
  Variable *qualVar = ct->lookup_one(memberName, NULL /*env*/,
                                     lflags | LF_TEMPL_PRIMARY);
  if (!qualVar || !qualVar->type->isCompoundType()) {
    xTypeDeduction(stringc << "no such member class: " << ct->name
                           << memberName);
  }

  bool argsProvided = !srcArgs->isEmpty();
  bool isTemplate = qualVar->isTemplateClass(false /*considerInherited*/);

  if (argsProvided && isTemplate) {
    // resolve the template arguments using 'map'
    ObjList<STemplateArgument> args;
    applyArgumentMapToTemplateArgs(map, args, *srcArgs);

    // instantiate the template with the arguments
    qualVar = instantiateClassTemplate(loc(), qualVar, args);
    if (!qualVar) {
      return env.errorType();    // error already reported
    }
  }
  else if (!argsProvided && isTemplate) {
    xTypeDeduction(stringc << "member " << ct->name << "::" << memberName
                           << " is a template, but template args were not provided");
  }
  else if (argsProvided && !isTemplate) {
    xTypeDeduction(stringc << "member " << ct->name << "::" << memberName
                           << " is not a template, but template args were provided");
  }

  if (name->isPQ_template()) {
    // we're done; package up the answer
    //
    // 2005-08-07: Why the heck to I apply CV_NONE?  Why not just
    // return inst->type directly?
    return tfac.applyCVToType(SL_UNKNOWN, CV_NONE,
                              qualVar->type, NULL /*syntax*/);
  }
  else {
    // recursively continue deconstructing 'name'
    return applyArgumentMapToQualifiedType(map, qualVar->type->asCompoundType(),
                                           name->asPQ_qualifier()->rest);
  }
}
// ------------ END: applyArgumentMap -------------


Variable *Env::findCompleteSpecialization(TemplateInfo *tinfo,
                                          ObjList<STemplateArgument> const &sargs)
{
  SFOREACH_OBJLIST_NC(Variable, tinfo->specializations, iter) {
    TemplateInfo *instTI = iter.data()->templateInfo();
    if (instTI->isomorphicArguments(sargs)) {
      return iter.data();      // found it
    }
  }
  return NULL;                 // not found
}


Variable *Env::findInstantiation(TemplateInfo *tinfo,
                                 ObjList<STemplateArgument> const &sargs)
{
  if (tinfo->isCompleteSpec()) {
    xassertdb(tinfo->isomorphicArguments(sargs));
    return tinfo->var;
  }

  SFOREACH_OBJLIST_NC(Variable, tinfo->instantiations, iter) {
    TemplateInfo *instTI = iter.data()->templateInfo();
    if (instTI->isomorphicArguments(sargs)) {
      return iter.data();      // found it
    }
  }
  return NULL;                 // not found
}


// make a Variable with type 'type' that will be an instantiation
// of 'templ'
Variable *Env::makeInstantiationVariable(Variable *templ, Type *instType)
{
  Variable *inst = makeVariable(templ->loc, templ->name, instType, templ->flags);

  inst->setAccess(templ->getAccess());
  inst->scope = templ->scope;
  inst->setScopeKind(templ->getScopeKind());
  return inst;
}


void Env::bindParametersInMap(MType &map, TemplateInfo *tinfo,
                              SObjList<STemplateArgument> const &sargs)
{
  SObjListIter<STemplateArgument> argIter(sargs);

  // inherited parameters
  FOREACH_OBJLIST(InheritedTemplateParams, tinfo->inheritedParams, iter) {
    bindParametersInMap(map, iter.data()->params, argIter);
  }

  // main parameters
  bindParametersInMap(map, tinfo->params, argIter);
  
  if (!argIter.isDone()) {
    error(stringc << "too many template arguments supplied for "
                  << tinfo->var->name);
  }
}

void Env::bindParametersInMap(MType &map,
                              SObjList<Variable> const &params,
                              SObjListIter<STemplateArgument> &argIter)
{
  SFOREACH_OBJLIST(Variable, params, iter) {
    Variable const *param = iter.data();

    if (map.getBoundValue(param->name, tfac).hasValue()) {
      error(stringc << "template parameter `" << param->name <<
                       "' occurs more than once");
    }
    else if (argIter.isDone()) {
      error(stringc << "no template argument supplied for parameter `" <<
                       param->name << "'");
    }
    else {
      map.setBoundValue(param->name, *argIter.data());
    }

    if (!argIter.isDone()) {
      argIter.adv();
    }
  }
}


// given a CompoundType that is a template (primary or partial spec),
// yield a PseudoInstantiation of that template with its own params
Type *Env::pseudoSelfInstantiation(CompoundType *ct, CVFlags cv)
{
  TemplateInfo *tinfo = ct->typedefVar->templateInfo();
  xassert(tinfo);     // otherwise why are we here?

  PseudoInstantiation *pi = new PseudoInstantiation(
    tinfo->getPrimary()->var->type->asCompoundType());   // awkward...

  if (tinfo->isPrimary()) {
    // 14.6.1 para 1

    // I'm guessing we just use the main params, and not any
    // inherited params?
    SFOREACH_OBJLIST_NC(Variable, tinfo->params, iter) {
      Variable *param = iter.data();

      // build a template argument that just refers to the template
      // parameter
      STemplateArgument *sta = new STemplateArgument;
      if (param->type->isTypeVariable()) {
        sta->setType(param->type);
      }
      else {        
        // perhaps there should be an STemplateArgument variant that
        // is like STA_DEPEXPR but can only hold a single Variable?
        PQ_name *name = new PQ_name(param->loc, param->name);
        E_variable *evar = new E_variable(name);
        evar->var = param;
        sta->setDepExpr(evar);
      }

      pi->args.append(sta);
    }
  }

  else /*partial spec*/ {
    // 14.6.1 para 2
    xassert(tinfo->isPartialSpec());

    // use the specialization arguments
    copyTemplateArgs(pi->args, objToSObjListC(tinfo->arguments));
  }

  return makeCVAtomicType(pi, cv);
}


Variable *Env::makeExplicitFunctionSpecialization
  (SourceLoc loc, DeclFlags dflags, PQName *name, FunctionType *ft)
{
  // find the overload set
  LookupSet set;
  lookupPQ(set, name, LF_TEMPL_PRIMARY);
  if (set.isEmpty()) {
    error(stringc << "cannot find primary `" << name->toString()
                  << "' to specialize");
    return NULL;
  }

  // find last component of 'name' so we can see if template arguments
  // are explicitly supplied
  PQ_template *pqtemplate = NULL;
  ObjList<STemplateArgument> *nameArgs = NULL;
  if (name->getUnqualifiedName()->isPQ_template()) {
    pqtemplate = name->getUnqualifiedName()->asPQ_template();
    nameArgs = &(pqtemplate->sargs);
  }

  // look for a template member of the overload set that can
  // specialize to the type 'ft' and whose resulting parameter
  // bindings are 'sargs' (if supplied)
  Variable *best = NULL;     
  Variable *ret = NULL;
  SFOREACH_OBJLIST_NC(Variable, set, iter) {
    Variable *primary = iter.data();
    if (!primary->isTemplate()) {
      continue_outer_loop:     // poor man's labeled continue ...
      continue;
    }

    // 2005-05-26 (in/t0485.cc): if we're trying to associate a
    // specialization with a member template, the specialization
    // does not yet know whether it is a nonstatic member or not,
    // so we must ignore the receiver argument when matching
    MatchFlags mflags = MF_IGNORE_IMPLICIT | MF_MATCH | MF_STAT_EQ_NONSTAT;

    // can this element specialize to 'ft'?
    MType match(env);
    if (match.matchTypeNC(ft, primary->type, mflags)) {
      // yes; construct the argument list that specializes 'primary'
      TemplateInfo *primaryTI = primary->templateInfo();
      ObjList<STemplateArgument> specArgs;

      if (primaryTI->inheritedParams.isNotEmpty()) {
        // two difficulties:
        //   - both the primary and specialization types might refer
        //     to inherited type varibles, but MM_BIND doesn't want
        //     type variables occurring on both sides
        //   - I want to compute right now the argument list that
        //     specializes primary, but then later I will want the
        //     full argument list for making the TemplateInfo
        xunimp("specializing a member template of a class template");
      }

      // simultanously iterate over the user's provided arguments,
      // if any, checking for correspondence with inferred arguments
      ObjList<STemplateArgument> empty;
      ObjListIter<STemplateArgument> nameArgsIter(nameArgs? *nameArgs : empty);

      // just use the main (not inherited) parameters...
      SFOREACH_OBJLIST_NC(Variable, primaryTI->params, paramIter) {
        Variable *param = paramIter.data();

        // get the binding
        STemplateArgument binding = match.getBoundValue(param->name, tfac);
        if (!binding.hasValue()) {
          // inference didn't pin this down; did the user give me
          // arguments to use instead?
          if (!nameArgsIter.isDone()) {
            // yes, use the user's argument instead
            binding = *nameArgsIter.data();
          }
          else {
            // no, so this candidate can't match
            goto continue_outer_loop;
          }
        }
        else {
          // does the inferred argument match what the user has?
          if (pqtemplate &&                               // user gave me arguments
              (nameArgsIter.isDone() ||                           // but not enough
               !binding.isomorphic(nameArgsIter.data()))) {       // or no match
            // no match, this candidate can't match
            goto continue_outer_loop;
          }
        }

        // remember the argument
        specArgs.append(new STemplateArgument(binding));

        if (!nameArgsIter.isDone()) {
          nameArgsIter.adv();
        }
      }

      // does the inferred argument list match 'nameArgs'?  we already
      // checked individual elements above, now just confirm the count
      // is correct (in fact, only need to check there aren't too many)
      if (pqtemplate &&                  // user gave me arguments
          !nameArgsIter.isDone()) {        // but too many
        // no match, go on to the next primary
        continue;
      }

      // ok, found a suitable candidate
      if (best) {
        error(stringc << "ambiguous specialization, could specialize `"
                      << best->type->toString() << "' or `"
                      << primary->type->toString()
                      << "'; use explicit template arguments to disambiguate",
                      EF_STRONG);
        // error recovery: use 'best' anyway
        break;
      }
      best = primary;

      // make SObjList version of specArgs
      SObjList<STemplateArgument> const &serfSpecArgs = objToSObjListC(specArgs);

      // do we already have a specialization like this?
      ret = primary->templateInfo()->getSpecialization(specArgs);
      if (ret) {
        TRACE("template", "re-declaration of function specialization of " <<
                          primary->type->toCString(primary->fullyQualifiedName()) <<
                          ": " << ret->name << sargsToString(serfSpecArgs));
      }
      else {
        // build a Variable to represent the specialization
        ret = makeSpecializationVariable(loc, dflags, primary, ft, serfSpecArgs);
        TRACE("template", "complete function specialization of " <<
                          primary->type->toCString(primary->fullyQualifiedName()) <<
                          ": " << ret->toQualifiedString());
      }
    } // initial candidate match check
  } // candidate loop

  if (!ret) {
    error("specialization does not match any function template", EF_STRONG);
    return NULL;
  }

  return ret;
}


Variable *Env::makeSpecializationVariable
  (SourceLoc loc, DeclFlags dflags, Variable *templ, FunctionType *type,
   SObjList<STemplateArgument> const &args)
{
  // make 'type' into a method if 'templ' is
  FunctionType *templType = templ->type->asFunctionType();
  if (templType->isMethod()) {
    // The reason I am making a copy instead of modifying 'type' is
    // that, at the call site in Declarator::mid_tcheck, if it gets
    // back a Variable with a method it will method-ize 'type' again.
    // But by making a copy, I method-ize my copy here, and then let
    // Declarator::mid_tcheck method-ize 'type' later, harmlessly.
    // (Wow, what a borked design... yikes.)

    FunctionType *oldFt = type;
    xassert(!oldFt->isMethod());

    // everything the same but empty parameter list
    FunctionType *newFt =
      tfac.makeSimilarFunctionType(SL_UNKNOWN, oldFt->retType, oldFt);

    // add the receiver parameter
    NamedAtomicType *nat = templType->getNATOfMember();
    newFt->addReceiver(receiverParameter(SL_UNKNOWN, nat, templType->getReceiverCV()));

    // copy the other parameters
    SObjListIterNC<Variable> iter(oldFt->params);
    for (; !iter.isDone(); iter.adv()) {
      newFt->addParam(iter.data());    // re-use parameter objects
    }
    doneParams(newFt);

    // treat this new type as the one to declare from here out
    type = newFt;
  }

  // make the Variable
  Variable *spec = makeVariable(loc, templ->name, type, dflags);
  spec->setAccess(templ->getAccess());
  spec->scope = templ->scope;
  spec->setScopeKind(templ->getScopeKind());

  // make & attach the TemplateInfo
  TemplateInfo *ti = new TemplateInfo(loc, spec);
  ti->copyArguments(args);

  // attach to the template
  templ->templateInfo()->addSpecialization(spec);

  // this is a specialization
  xassert(ti->isSpecialization());

  return spec;
}


void Env::explicitlyInstantiate(Variable *var, DeclFlags instFlags)
{
  TemplateInfo *tinfo = var->templateInfo();
  xassert(tinfo);

  // 8/12/04: This code has not been tested very much ...

  // function instantiation?
  if (var->type->isFunctionType()) {
    if (instFlags & DF_EXTERN) {
      // this is a request to *never* instantiate this thing
      if (tinfo->instantiatedFunctionBody()) {
        // already did it... oh well
      }
      else {
        // prevent it
        tinfo->instantiationDisallowed = true;
      }
    }

    else {
      // It's ok if we haven't seen the definition yet, however, the
      // presence of this explicit instantiation request means that the
      // definition must be somewhere in the translation unit (14.7.2
      // para 4).  However, I do not enforce this.
      ensureFuncBodyTChecked(var);
    }

    return;
  }

  // class instantiation
  xassert(var->type->isCompoundType());
  CompoundType *ct = var->type->asCompoundType();
  if (!ensureCompleteType("instantiate", var->type)) {
    return;    // recovery
  }

  // 14.7.2 para 7: instantiate all members, too

  // base classes
  FOREACH_OBJLIST(BaseClass, ct->bases, baseIter) {
    Variable *b = baseIter.data()->ct->typedefVar;
    if (b->isInstantiation()) {     // t0273.cc
      explicitlyInstantiate(b, instFlags);
    }
  }

  // member variables, functions
  for (PtrMap<const char, Variable>::Iter membIter(ct->getVariableIter());
       !membIter.isDone(); membIter.adv()) {
    Variable *memb = membIter.value();

    if (memb->templateInfo()) {
      explicitlyInstantiate(memb, instFlags);
    }
  }

  // inner classes
  for (PtrMap<const char, Variable>::Iter innerIter(ct->getTypeTagIter());
       !innerIter.isDone(); innerIter.adv()) {
    Variable *inner = innerIter.value();
              
    if (inner->type->isCompoundType()) {
      explicitlyInstantiate(inner, instFlags);
    }
  }
}


// This is called in response to syntax like (t0256.cc)
//
//   template
//   int foo(int t);
//
// for which 'name' would be "foo" and 'type' would be "int ()(int)".
// This function then finds a function template called "foo" that
// matches the given type, and instantiates its body.  Finally, that
// instantiation is returned.
//
// On error, an error message is emitted and NULL is returned.
Variable *Env::explicitFunctionInstantiation(PQName *name, Type *type,
                                             DeclFlags instFlags)
{
  if (!type->isFunctionType()) {
    error("explicit instantiation of non-function type");
    return NULL;
  }

  LookupSet set;
  lookupPQ(set, name, LF_TEMPL_PRIMARY);
  if (set.isEmpty() || !set.first()->type->isFunctionType()) {
    error(stringc << "no such function `" << *name << "'");
    return NULL;
  }

  // did the user attach arguments to the name?
  ObjList<STemplateArgument> *nameArgs = NULL;
  if (name->getUnqualifiedName()->isPQ_template()) {
    nameArgs = &( name->getUnqualifiedName()->asPQ_template()->sargs );
  }

  // collect candidates
  InstCandidateResolver resolver(env);

  // examine all overloaded versions of the function
  SFOREACH_OBJLIST_NC(Variable, set, iter) {
    Variable *primary = iter.data();

    if (!nameArgs &&                      // no arguments attached to final name
        primary->isInstantiation() &&     // member of an instantiated template
        type->equals(primary->type, MF_IGNORE_IMPLICIT |     // right type
                                    MF_STAT_EQ_NONSTAT)) {
      // an instantiation request like (in/k0016.cc)
      //   template
      //   void S<int>::foo();
      // where 'foo' is *not* a member template, but is a member of
      // a class template
      explicitlyInstantiate(primary, instFlags);
      return primary;
    }

    if (!primary->isTemplate()) continue;
    TemplateInfo *primaryTI = primary->templateInfo();

    // does the type we have match the type of this template?
    MType match(env);
    if (!match.matchTypeNC(type, primary->type, MF_MATCH)) {
      continue;   // no match
    }

    // use user's arguments (if any) to fill in missing bindings
    if (nameArgs) {
      if (!loadBindingsWithExplTemplArgs(primary, *nameArgs, match,
                                         IA_NO_ERRORS)) {
        continue;      // no match
      }
    }

    // build the candidate structure now, since it contains the
    // 'sargs' to store the arguments
    InstCandidate *cand = new InstCandidate(primary);

    // convert the bindings into a sequential argument list
    // (I am ignoring the inherited params b/c I'm not sure if it
    // is correct to use them here...)
    bool haveAllArgs = true;
    getFuncTemplArgs_oneParamList(match, cand->sargs, IA_NO_ERRORS,
                                  haveAllArgs, primaryTI->params);
    if (!haveAllArgs) {
      delete cand;
      continue;   // no match
    }

    // at this point, the match is a success; store this candidate
    resolver.candidates.push(cand);
  }
  
  // did we find any candidates?
  if (resolver.candidates.isEmpty()) {
    error(stringc << "type `" << type->toString() 
                  << "' does not match any template function `" << *name << "'");
    return NULL;
  }
  
  // choose from among those we found
  InstCandidate *best = resolver.selectBestCandidate();
  if (!best) {
    // TODO: make this error message more informative
    error("ambiguous function template instantiation");
    best = resolver.candidates[0];       // error recovery; pick arbitrarily
  }

  // apply the arguments to the primary
  Variable *ret = instantiateFunctionTemplate(name->loc, best->primary, best->sargs);

  // instantiate the body
  explicitlyInstantiate(ret, instFlags);
  
  // done; 'resolver' and its candidates automatically deallocated
  return ret;
}


// This returns true if 'otherPrimary/otherArgs' names the same
// template that I am.  For example, if 'this' template is
//
//   template <class T, int n>
//   struct A { ... };
//
// and we see a definition like
//
//   template <class S, int m>
//   A<S,m>::some_type *A<S,m>::foo(...) {}
//   ^^^^^^
//
// then we need to recognize that "A<S,m>" means this template.  Note
// that for this to work the parameters S and m must already have been
// associated with a specific (i.e., this) template.
bool TemplateInfo::matchesPI(CompoundType *otherPrimary,
                             ObjList<STemplateArgument> const &otherArgs)
{
  // same template?
  if (getPrimary()->var != otherPrimary->typedefVar) {
    return false;
  }
  
  // if I am a primary, then 'pi->args' should be a list of
  // type variables that correspond to my parameters
  if (isPrimary()) {
    int ct = -1;
    FOREACH_OBJLIST(STemplateArgument, otherArgs, iter) {
      ct++;
      Variable *argVar = NULL;

      // type parameter?
      if (iter.data()->isType() &&
          iter.data()->getType()->isTypeVariable()) {
        argVar = iter.data()->getType()->asTypeVariable()->typedefVar;
      }

      // non-type paramter?
      else if (iter.data()->isDepExpr() &&
               iter.data()->getDepExpr()->isE_variable()) {
        argVar = iter.data()->getDepExpr()->asE_variable()->var;
      }
      
      // TODO: template template parameter
      
      if (argVar &&
          argVar->isTemplateParam() &&
          argVar->getParameterizedEntity() == this->var &&
          argVar->getParameterOrdinal() == ct) {
        // good to go
      }  
      else {
        return false;     // no match
      }
    }
    
    // should be right # of args
    if (ct+1 != params.count()) {
      return false;
    }

    // TODO: Take default arguments into account. (in/t0440.cc)

    // match!
    return true;
  }

  // not a primary; we are a specialization; check against arguments
  // to primary
  return isomorphicArgumentLists(argumentsToPrimary, otherArgs);
}


bool TemplateInfo::instantiatedFunctionBody() const
{
  return var->funcDefn && !var->funcDefn->instButNotTchecked();
}

     
// ------------------- InstantiationContextIsolator -----------------------
InstantiationContextIsolator::InstantiationContextIsolator(Env &e, SourceLoc loc)
  : env(e),
    origNestingLevel(e.disambiguationNestingLevel),
    origSecondPass(e.secondPassTcheck),
    origErrors()
{
  env.instantiationLocStack.push(loc);
  env.disambiguationNestingLevel = 0;
  env.secondPassTcheck = false;
  origErrors.takeMessages(env.errors);
}

InstantiationContextIsolator::~InstantiationContextIsolator()
{
  env.setLoc(env.instantiationLocStack.pop());
  env.disambiguationNestingLevel = origNestingLevel;
  env.secondPassTcheck = origSecondPass;

  // where do the newly-added errors, i.e. those from instantiation,
  // which are sitting in 'env.errors', go?
  if (env.hiddenErrors) {
    // shuttle them around to the hidden message list
    env.hiddenErrors->takeMessages(env.errors);
  }
  else {
    // put them at the end of the original errors, as if we'd never
    // squirreled away any messages
    origErrors.takeMessages(env.errors);
  }
  xassert(env.errors.isEmpty());

  // now put originals back into env.errors
  env.errors.takeMessages(origErrors);
}


// ---------------------- XTypeDeduction ------------------------
XTypeDeduction::XTypeDeduction(XTypeDeduction const &obj)
  : xBase(obj)
{}

XTypeDeduction::~XTypeDeduction()
{}


void xTypeDeduction(rostring why)
{
  XTypeDeduction x(why);
  THROW(x);
}


// ---------------------- DelayedFuncInst -----------------------
DelayedFuncInst::DelayedFuncInst(Variable *v, ArrayStack<SourceLoc> const &s,
                                 SourceLoc L)
  : instV(v),
    instLocStack(s),
    loc(L)
{}
  
DelayedFuncInst::~DelayedFuncInst()
{}


// EOF
