// cc_scope.cc            see license.txt for copyright and terms of use
// code for cc_scope.h

#include "cc_scope.h"     // this module
#include "trace.h"        // trace
#include "variable.h"     // Variable
#include "cc_type.h"      // CompoundType
#include "cc_env.h"       // doh.  Env::error
#include "mangle.h"       // mangle
#include "exc.h"          // unwinding


Scope::Scope(ScopeKind sk, int cc, SourceLoc initLoc)
  : variables(),
    typeTags(),
    changeCount(cc),
    onScopeStack(false),
    canAcceptNames(true),
    parentScope(),
    scopeKind(sk),
    namespaceVar(NULL),
    templateParams(),
    parameterizedEntity(NULL),
    usingEdges(0),            // the arrays start as NULL b/c in the
    usingEdgesRefct(0),       // common case the sets are empty
    activeUsingEdges(0),
    outstandingActiveEdges(0),
    curCompound(NULL),
    curFunction(NULL),
    curLoc(initLoc)
{
  xassert(sk != SK_UNKNOWN);
}

// a ctor for de-serialization
Scope::Scope(ReadXML&)
  : variables(),
    typeTags(),
    changeCount(0),
    onScopeStack(false),
    canAcceptNames(true),
    parentScope(),
    scopeKind(SK_UNKNOWN),
    namespaceVar(NULL),
    templateParams(),
    parameterizedEntity(NULL),
    usingEdges(0),            // the arrays start as NULL b/c in the
    usingEdgesRefct(0),       // common case the sets are empty
    activeUsingEdges(0),
    outstandingActiveEdges(0),
    curCompound(NULL),
    curFunction(NULL),
    curLoc(SL_UNKNOWN)
{}

Scope::~Scope()
{
  // 8/14/04: I got all of our test suite to go through without
  // running into what is now the xfailure below, so I think I've got
  // most of this straightened out.  But this isn't such a big deal if
  // it fails so I'm going to turn it off again.  If at some point
  // we are more interested in improving the implementation than in
  // getting code to go through, I might turn it on again.
  #if 0
  if (scopeKind == SK_TEMPLATE_PARAMS && !parameterizedPrimary) {
    // my intent is that all SK_TEMPLATE_PARAMSs get assigned to some
    // primary eventually; this warning should be commented-out once
    // the implementation stabilizes
    xfailure(stringc << desc() << " has no parameterizedPrimary");
  }
  #endif // 0

  // if we were delegated, break the delegation
  if (isDelegated()) {
    CompoundType *ct = parameterizedEntity->type->asCompoundType();
    if (!unwinding()) {
      xassert(ct->parameterizingScope == this);
    }

    TRACE("templateParams", desc() << " removing delegation to " << ct->desc());

    ct->parameterizingScope = NULL;
    parameterizedEntity = NULL;     // irrelevant but harmless
  }
  
  if (!unwinding()) {         // if not already raising an exception,
    xassert(!onScopeStack);   // check that we are not pointed-to
  }
}


bool Scope::isPermanentScope() const
{
  return isGlobalScope() ||
         isNamespace() ||
         (curCompound && curCompound->name);
}


bool Scope::isDelegated() const
{
  return parameterizedEntity &&
         parameterizedEntity->type->isCompoundType();
}


Scope *Scope::getDelegationPointer() const
{
  if (curCompound) {
    return curCompound->parameterizingScope;
  }
  return NULL;
}

Scope *Scope::getAndNullifyDelegationPointer()
{
  Scope *ret = curCompound->parameterizingScope;
  xassert(ret);
  curCompound->parameterizingScope = NULL;
  return ret;
}

void Scope::setDelegationPointer(Scope *s)
{
  xassert(!curCompound->parameterizingScope);
  xassert(s);
  curCompound->parameterizingScope = s;
}


// -------- insertion --------
template <class T>
bool insertUnique(StringRefMap<T> &table, char const *key, T *value,
                  int &changeCount, bool forceReplace)
{
  if (!forceReplace && table.get(key)) {
    return false;
  }

  // NOTE: it is no longer necessary to remove before adding; add will
  // just overwrite
  table.add(key, value);
  changeCount++;
  return true;
}


bool Scope::isGlobalTemplateScope() const 
{
  return isTemplateParamScope() && 
         (parentScope && parentScope->isGlobalScope());
}


bool Scope::isWithinUninstTemplate() const 
{
  if (curCompound && 
      curCompound->templateInfo() &&
      curCompound->templateInfo()->hasParameters()) {
    return true;
  }

  if (parentScope) {
    return parentScope->isWithinUninstTemplate();
  }
  else {
    return false;
  }
}


bool Scope::hasTemplateParams() const
{
  return isTemplateParamScope() &&
         templateParams.isNotEmpty();
}


// This function should not modify 'v'; any changes to 'v' should
// instead be done by 'registerVariable'.
bool Scope::addVariable(Variable *v, bool forceReplace)
{
  xassert(canAcceptNames);

  if (!v->isNamespace()) {
    // classify the variable for debugging purposes
    #if DO_TRACE
      char const *classification =
        v->hasFlag(DF_TYPEDEF)?    "typedef" :
        v->type->isFunctionType()? "function" :
                                   "variable" ;
    #endif // DO_TRACE

    // does the type contain any error-recovery types?  if so,
    // then we don't want to add the variable because we could
    // be trying to disambiguate a declarator, and this would
    // be the erroneous interpretation which is not supposed to
    // modify the environment
    bool containsErrors = v->type->containsErrors();
    char const *prefix = "";
    if (containsErrors) {
      prefix = "[cancel/error] ";
    }

    if (!curCompound) {
      // variable outside a class
      TRACE("env",    prefix << "added " << classification
                   << " `" << v->name
                   << "' of type `" << v->type->toString()
                   << "' at " << toLCString(v->loc)
                   << " to " << desc());
    }
    else {
      // class member
      //v->access = curAccess;      // moved into registerVariable()
      TRACE("env",    prefix << "added " << toString(v->getAccess())
                   << " member " << classification
                   << " `" << v->name
                   << "' of type `" << v->type->toString()
                   << "' at " << toLCString(v->loc)
                   << " to " << desc());
    }

    if (containsErrors) {
      return true;     // pretend it worked; don't further rock the boat
    }
  }

  // moved into registerVariable()
  //if (isGlobalScope()) {
  //  v->setFlag(DF_GLOBAL);
  //}

  if (insertUnique(variables, v->name, v, changeCount, forceReplace)) {
    afterAddVariable(v);
    return true;
  }
  else {
    return false;
  }
}

void Scope::afterAddVariable(Variable *v)
{}


bool Scope::addCompound(CompoundType *ct)
{
  xassert(canAcceptNames);
  xassert(ct->typedefVar);

  TRACE("env", "added " << toString(ct->keyword) << " " << ct->name);

  ct->access = curAccess;
  return addTypeTag(ct->typedefVar);
}


bool Scope::addEnum(EnumType *et)
{
  xassert(canAcceptNames);
  xassert(et->typedefVar);

  TRACE("env", "added enum " << et->name);

  et->access = curAccess;
  return addTypeTag(et->typedefVar);
}


bool Scope::addTypeTag(Variable *tag)
{
  xassert(tag->type->isEnumType() ||
          tag->type->isCompoundType());

  tag->setAccess(curAccess);
  return insertUnique(typeTags, tag->name, tag, changeCount, false /*forceReplace*/);
}


// This function is responsble for modifying 'v' in preparation for
// adding it to this scope.  It's separated out from 'addVariable'
// because in certain cases the variable is actually not added; but
// this function should behave as if it always is added.
void Scope::registerVariable(Variable *v)
{
  if (v->getScopeKind() == SK_UNKNOWN) {
    v->setScopeKind(scopeKind);
  }
  else {
    // this happens to parameters at function definitions: the
    // variable is created and first entered into the parameter scope,
    // but then the they are also inserted into the function scope
    // (because the parameter scope ends at the closing-paren); so
    // leave the scope kind alone, even though now the variable has
    // been added to a function scope
  }

  if (isPermanentScope()) {
    v->scope = this;
  }

  if (curCompound) {
    // take access control from scope's current setting
    v->setAccess(curAccess);
  }

  if (isGlobalScope()
      // FIX: is this right?  dsw: if we are in a template scope that
      // is in a global scope, you are effectively also a global
      // unless you are a template parameter
      //
      // sm: TODO: what is going on here?  why does this matter?  what
      // is being set DF_GLOBAL that wouldn't otherwise?  who pays
      // attention that flag?
      || (isGlobalTemplateScope() && !v->hasFlag(DF_PARAMETER))
      ) {
    v->setFlag(DF_GLOBAL);
  }
}


void Scope::addUniqueVariable(Variable *v)
{
  registerVariable(v);
  bool ok = addVariable(v);
  xassert(ok);
}

 
// is 'ancestor' an ancestor of 'child'?
bool hasAncestor(BaseClassSubobj const *child, BaseClassSubobj const *ancestor)
{
  // Unfortunately, I can't do a DFS using the 'visited' fields,
  // because this query happens right in the middle of *another* DFS
  // that is using those same fields.  Oh well, just to it without
  // the 'visited' flags, and take the possibly exponential hit ...

  if (child == ancestor) {
    return true;
  }
  
  SFOREACH_OBJLIST(BaseClassSubobj, child->parents, iter) {
    if (hasAncestor(iter.data(), ancestor)) {
      return true;
    }
  }
  
  return false;
}


Variable *Scope::lookupVariable_inner
  (LookupSet &candidates, StringRef name, Env &env, LookupFlags flags)
{
  Variable *v1 = NULL;

  // [cppstd sec. 10.2]: class members hide all members from
  // base classes
  //
  // 2005-08-14: calling 'lookupSingleVariable' to fix in/t0527.cc;
  // this now filters twice, but it should be ok anyway
  v1 = candidates.filter(lookupSingleVariable(name, flags), flags);

  if (!(flags & LF_IGNORE_USING)) {
    if (!(flags & LF_QUALIFIED)) {
      // 7.3.4 para 1: "active using" edges are a source of additional
      // declarations that can satisfy an unqualified lookup
      if (activeUsingEdges.isNotEmpty()) {
        v1 = searchActiveUsingEdges(candidates, name, env, flags, v1);
      }
    }
    else {
      // 3.4.3.2 para 2: do a DFS on the "using" edge graph, but only
      // if we haven't already found the name
      if (!v1 && usingEdges.isNotEmpty()) {
        v1 = searchUsingEdges(candidates, name, env, flags);
      }
    }
  }

  if (v1) {
    return v1;
  }

  if (!curCompound) {
    // nowhere else to look
    return NULL;
  }

  // [ibid] if I can find a class member by looking in multiple
  // base classes, then it's ambiguous and the program has
  // an error
  //
  // to implement this, I'll walk the list of base classes,
  // keeping in 'ret' the latest successful lookup, and if I
  // find another successful lookup then I'll complain

  // recursively examine the subobject hierarchy
  BaseClassSubobj const *v1Subobj = NULL;
  curCompound->clearSubobjVisited();
  lookupVariable_considerBase(name, env, flags,
                              v1, v1Subobj, &(curCompound->subobj));

  if (v1) {
    candidates.adds(v1);
  }

  return v1;
}

// helper for lookupVariable_inner; if we find a suitable variable, set
// v1/v1Subobj to refer to it; if we find an ambiguity, report that
void Scope::lookupVariable_considerBase
  (StringRef name, Env &env, LookupFlags flags,  // stuff from caller
   Variable *&v1,                                    // best so far
   BaseClassSubobj const *&v1Subobj,                 // where 'v1' was found
   BaseClassSubobj const *v2Subobj)                  // where we're looking now
{
  if (v2Subobj->visited) return;
  v2Subobj->visited = true;

  CompoundType const *v2Base = v2Subobj->ct;

  // look in 'v2Base' for the field
  Variable *v2 =
    vfilter(v2Base->variables.get(name), flags);
  if (v2) {
    TRACE("lookup", "found " << v2Base->name << "::" << name);

    if (v1) {
      if (v1 == v2 &&
          (v1->hasFlag(DF_STATIC) || v1->hasFlag(DF_TYPEDEF))) {
        // they both refer to the same static entity; that's ok
        // (10.2 para 2); ALSO: we believe this exception should
        // apply to types also (DF_TYPEDEF), though the standard
        // does not explicitly say so (in/t0166.cc is testcase)
        return;
      }

      // 9/21/04: It is still possible that this is not an error, if
      // 'v1' is hidden by 'v2' but (because of virtual inheritance)
      // 'v1' was nevertheless traversed before 'v2'.  So, check whether
      // 'v2' hides 'v1'.  See in/d0104.cc.
      if (hasAncestor(v2Subobj, v1Subobj)) {
        // ok, just go ahead and let 'v2' replace 'v1'
        TRACE("lookup", "DAG ancestor conflict suppressed (v2 is lower)");
      }
      else if (hasAncestor(v1Subobj, v2Subobj)) {
        // it could also be the other way around
        TRACE("lookup", "DAG ancestor conflict suppressed (v1 is lower)");

        // in this case, 'v1' is already the right one
        return;
      }
      else {
        // ambiguity
        env.error(stringc
          << "reference to `" << name << "' is ambiguous, because "
          << "it could either refer to "
          << v1Subobj->ct->name << "::" << name << " or "
          << v2Base->name << "::" << name);
        return;
      }
    }

    // found one; copy it into 'v1', my "best so far"
    v1 = v2;
    v1Subobj = v2Subobj;

    // this name hides any in base classes, so this arm of the
    // search stops here
    return;
  }

  // we didn't find it; recursively look into base classes of
  // 'v2Subobj'
  SFOREACH_OBJLIST(BaseClassSubobj, v2Subobj->parents, iter) {
    lookupVariable_considerBase(name, env, flags, v1, v1Subobj, iter.data());
  }
}


Variable *Scope::lookupVariable(StringRef name, Env &env,
                                LookupFlags flags)
{
  LookupSet candidates;
  return lookupVariable_set(candidates, name, env, flags);
}

Variable *Scope::lookupVariable_set
  (LookupSet &candidates, StringRef name, Env &env, LookupFlags flags)
{
  if (flags & LF_INNER_ONLY) {
    return candidates.filter(variables.get(name), flags);
  }

  if (curCompound && (flags & LF_ARG_DEP)) {
    // (in/t0569.cc) Arg-dep lookup only finds friends of classes
    // [3.4.2p1].  This is iterative search is not very efficient, but
    // it probably won't be used that often.  Building a more
    // efficient structure is a bit of a pain since friend sets need
    // not correspond to existing overload sets.
    SFOREACH_OBJLIST_NC(Variable, curCompound->friends, iter) {
      Variable *v = iter.data();
      if (v->name == name) {
        candidates.filter(v, flags);
      }
    }
    return candidates.isEmpty() ? NULL : candidates.first();
  }

  Variable *ret = lookupVariable_inner(candidates, name, env, flags);
  if (ret) return ret;

  // previously, I had code here which traversed the 'parentScope'
  // link to find additional places to look for 'name'; however, that
  // is very bad because:
  //   - the caller (typically Env::lookupVariable) is already iterating
  //     through the scope stack, so this will defeat that function's
  //     'foundScope' return value
  //   - the 'parentScope' link is NULL for unnamed scopes (at least in
  //     the current design), so searching along that path leads to
  //     different behavior depending on whether things are named
  //
  // so, if we do not find the name here, we just stop; the caller is
  // responsible for checking in parent scopes, etc.
  return NULL;
}


CompoundType const *Scope::lookupCompoundC(StringRef name, Env &env,
                                           LookupFlags flags) const
{
  Variable *v = lookupTypeTag(name, env, flags);
  if (!v) {
    return NULL;
  }
  else if (!v->type->isCompoundType()) {
    // TODO: further distinguish between struct/class and union
    if (!(flags & LF_SUPPRESS_ERROR)) {
      env.error(stringc << "`" << name << "' is not a struct/class/union");
    }
    return NULL;
  }
  else {
    return v->type->asCompoundType();
  }
}


EnumType const *Scope::lookupEnumC(StringRef name, Env &env,
                                   LookupFlags flags) const
{
  Variable *v = lookupTypeTag(name, env, flags);
  if (!v) {
    return NULL;
  }
  else if (!v->type->isEnumType()) {
    if (!(flags & LF_SUPPRESS_ERROR)) {
      env.error(stringc << "`" << name << "' is not an enum");
    }
    return NULL;
  }
  else {
    return v->type->asCVAtomicType()->atomic->asEnumType();
  }
}


Variable *Scope::lookupTypeTag(StringRef name, Env &env, LookupFlags flags) const
{
  Variable *v = vfilter(typeTags.get(name), flags);
  if (v || (flags & LF_INNER_ONLY)) {
    return v;
  }

  // consider bases
  if (curCompound) {
    FOREACH_OBJLIST(BaseClass, curCompound->bases, iter) {
      Variable *v2 = iter.data()->ct->lookupTypeTag(name, env, flags);
      if (v2) {
        if (!v) {
          v = v2;
        }
        else if (v != v2) {
          env.error(stringc << "ambiguous type tag: `" << v->fullyQualifiedName()
                            << "' vs. `" << v2->fullyQualifiedName() << "'");
        }
      }
    }
  }

  return v;
}


Variable *Scope::lookupSingleVariable(StringRef name, LookupFlags flags)
{
  if (flags & LF_QUERY_TAGS) {
    return vfilter(typeTags.get(name), flags);
  }
      
  if (flags & LF_ONLY_TYPES) {
    // 3.4.4p2,3: what we are implementing is "ignoring any non-type
    // names that have been declared"; in C++ mode it does not matter
    // whether we look in the tags or the variables first
    // (in/t0414.cc), but in C mode we must look in tags first
    // (in/c/t0019.c)
    Variable *v = vfilter(typeTags.get(name), flags);
    if (v) {
      return v;
    }
  }

  if (flags & LF_TYPES_NAMESPACES) {
    // (in/t0527.cc) try 'variables' (so we see namespaces and
    // typedefs), but if that yields something but it is not a type or
    // namespace, then look in the type tags too
    Variable *v = variables.get(name);
    if (v && !vfilter(v, flags)) {
      return vfilter(typeTags.get(name), flags);
    }
    else {
      return v;
    }
  }

  return vfilter(variables.get(name), flags);
}

void Scope::lookup(LookupSet &set, StringRef name, Env &env, LookupFlags flags)
{
  lookup(set, name, &env, flags);
}

void Scope::lookup(LookupSet &set, StringRef name, Env *env, LookupFlags flags)
{
  // check in our local map
  Variable *v = lookupSingleVariable(name, flags);

  // if found, expand overload sets
  if (v) {
    set.adds(v);
  }

  if (flags & LF_INNER_ONLY) {
    return;        // don't follow 'using' or base class chains
  }

  // consider 'using' directive edges
  if (!(flags & LF_IGNORE_USING)) {
    xassert(env);    // must pass an 'env' if you want 'using' edge traversal

    if (!(flags & LF_QUALIFIED)) {
      // 7.3.4 para 1: "active using" edges are a source of additional
      // declarations that can satisfy an unqualified lookup
      if (activeUsingEdges.isNotEmpty()) {
        v = searchActiveUsingEdges(set, name, *env, flags, v);
      }
    }
    else {
      // 3.4.3.2 para 2: do a DFS on the "using" edge graph, but only
      // if we haven't already found the name
      if (!v && usingEdges.isNotEmpty()) {
        v = searchUsingEdges(set, name, *env, flags);
      }
    }
  }
  
  // if we have found something, stop here, rather than considering
  // base classes
  xassert((!!v) == set.isNotEmpty());
  if (set.isNotEmpty()) {
    return;
  }

  // base classes?
  if (!curCompound) {
    return;
  }
  
  // get all the subobjects (I believe we do not have to call
  // ensureClassBodyInstantiated since every context will already
  // require that 'curCompound' be complete.)
  SObjList<BaseClassSubobj const> subobjs;
  curCompound->getSubobjects(subobjs);
  
  // look in each one for 'name', keeping track of which subobject
  // we find it in, if any     
  xassert(!v);
  BaseClassSubobj const *vObj = NULL;
  SFOREACH_OBJLIST(BaseClassSubobj const, subobjs, iter) {
    BaseClassSubobj const *v2Obj = iter.data();
    Variable *v2 = v2Obj->ct->lookupSingleVariable(name, flags);
    if (v2) {
      TRACE("lookup", "found " << v2Obj->ct->name << "::" << name);

      if (v) {
        // allow same entity, and static or type or enumerator
        // (cppstd 10.2 para 5)
        if (v==v2 && v->hasAnyFlags(DF_STATIC | DF_TYPEDEF | DF_ENUMERATOR)) {
          continue;
        }

        // allow hidden entities (cppstd 10.2 para 6)
        if (hasAncestor(v2Obj, vObj)) {
          // ok, just go ahead and let 'v2' replace 'v'
          TRACE("lookup", "DAG ancestor conflict suppressed (v2 is lower)");
        }
        else if (hasAncestor(vObj, v2Obj)) {
          // it could also be the other way around
          TRACE("lookup", "DAG ancestor conflict suppressed (v is lower)");

          // in this case, 'v1' is already the right one
          continue;
        }
        else {
          // ambiguity
          if (env) {
            env->error(stringc
              << "reference to `" << name << "' is ambiguous, because "
              << "it could either refer to "
              << vObj->ct->name << "::" << name << " or "
              << v2Obj->ct->name << "::" << name);
            break;
          }
          else {
            // since not reporting errors, must communicate the problem
            // via the result set
            set.removeAll();
            return;
          }
        }
      }

      // found one; copy it into 'v', my "best so far"
      v = v2;
      vObj = v2Obj;
    }
  }
  
  // if the above search yielded something, expand it and return
  if (v) {
    set.adds(v);
  }
}


Variable *Scope::lookup_one(StringRef name, Env &env, LookupFlags flags)
{
  return lookup_one(name, &env, flags);
}

Variable *Scope::lookup_one(StringRef name, Env *env, LookupFlags flags)
{
  LookupSet set;
  lookup(set, name, env, flags);
  return set.isEmpty()? NULL : set.first();
}


Variable const *Scope::getTypedefNameC() const
{
  if (scopeKind == SK_CLASS) {
    return curCompound->typedefVar;
  }
  if (scopeKind == SK_NAMESPACE) {
    return namespaceVar;
  }
  return NULL;
}


bool Scope::encloses(Scope const *s) const
{
  // in all situations where this is relevant, 's' has named parent
  // scopes (since we found it by qualified lookup), so just walk
  // the scope parent links

  Scope const *me = this;
  while (s && s!=me) {
    s = s->parentScope;
  }

  return s == me;
}


bool Scope::enclosesOrEq(Scope const *s) const
{ 
  return this == s || this->encloses(s);
}


string Scope::scopeName() const
{
  if (curCompound) {
    return curCompound->keywordAndName();
  }
  else {
    Variable const *v = getTypedefNameC();
    if (v && v->name) {
      return stringc << toString(scopeKind) << " " << v->name;
    }
    else if (isGlobalScope()) {
      return "global scope";
    }
    else {
      return stringc << "anonymous " << toString(scopeKind) << " scope";
    }
  }
}


string Scope::desc() const
{
  // name, plus address or serial number
  #if USE_SERIAL_NUMBERS
    return stringc << scopeName() << " #" << serialNumber;
  #else
    return stringc << scopeName() << " at " << stringf("%p", this);
  #endif
}

static void dumpMap(char const *label, StringRefMap<Variable> const &map)
{
  cout << "  " << label << ":\n";
  for (StringRefMap<Variable>::Iter iter(map);
       !iter.isDone();
       iter.adv()) {
    cout << "    " << iter.key() << ": " << iter.value()->toString() << "\n";
  }
}

void Scope::gdb() const
{
  cout << "Scope dump of " << desc() << ":\n";
  dumpMap("variables", variables);
  dumpMap("typeTags", typeTags);

  if (curCompound) {
    cout << "  friends (found during arg-dep lookup):\n";
    SFOREACH_OBJLIST(Variable, curCompound->friends, iter) {
      cout << "    " << iter.data()->toQualifiedString() << "\n";
    }
  }

  cout << flush;
}


void Scope::addUsingEdge(Scope *target)
{
  TRACE("using", "added using-edge from " << desc()
              << " to " << target->desc());

  usingEdges.push(target);
  target->usingEdgesRefct++;
}


void Scope::addActiveUsingEdge(Scope *target)
{
  TRACE("using", "added active-using-edge from " << desc()
              << " to " << target->desc());

  activeUsingEdges.push(target);
}

void Scope::removeActiveUsingEdge(Scope *target)
{
  TRACE("using", "removing active-using-edge from " << desc()
              << " to " << target->desc());

  if (activeUsingEdges.top() == target) {
    // we're in luck
    activeUsingEdges.pop();
  }
  else {
    // find the element that has 'target'
    for (int i=0; i<activeUsingEdges.length(); i++) {
      if (activeUsingEdges[i] == target) {
        // found it, swap with the top element
        Scope *top = activeUsingEdges.pop();
        activeUsingEdges[i] = top;
        return;
      }
    }
    
    xfailure("attempt to remove active-using edge not in the set");
  }
}


void Scope::scheduleActiveUsingEdge(Env &env, Scope *target)
{
  // find the innermost scope that contains both 'this' and 'target',
  // as this is effectively where target's declarations appear while
  // we're in this scope
  Scope *enclosing = env.findEnclosingScope(target);
  enclosing->addActiveUsingEdge(target);

  // schedule it for removal later
  outstandingActiveEdges.push(ActiveEdgeRecord(enclosing, target));
}


void Scope::openedScope(Env &env)
{
  if (onScopeStack) {
    xfailure(stringc << "opened twice: " << desc());
  }
  onScopeStack = true;

  if (usingEdges.length() == 0) {
    return;    // common case
  }

  // it's like I'm "using" myself, and thus all the things that
  // I have "using" edges to
  addUsingEdgeTransitively(env, this);
}

void Scope::closedScope()
{
  // remove the "active using" edges I previously added
  while (outstandingActiveEdges.isNotEmpty()) {
    ActiveEdgeRecord rec = outstandingActiveEdges.pop();

    // hmm.. I notice that I could just have computed 'source'
    // again like I did above..

    rec.source->removeActiveUsingEdge(rec.target);
  }

  xassert(onScopeStack);
  onScopeStack = false;
}


void Scope::addUsingEdgeTransitively(Env &env, Scope *target)
{
  // get set of scopes that are reachable along "using" edges from
  // 'target'; all get active-using edges, as if they directly
  // appeared in a using-directive in this scope (7.3.4 para 2)
  ArrayStack<Scope*> reachable;
  if (target != this) {
    // include it in the closure
    reachable.push(target);
  }
  target->getUsingClosure(reachable);

  // all (transitive) "using" edges give rise to "active using" edges
  for (int i=0; i<reachable.length(); i++) {
    scheduleActiveUsingEdge(env, reachable[i]);
  }
}


// search the lists instead of maintaining state in the Scope
// objects, to keep things simple; if the profiler tells me
// to make this faster, I can put colors into the objects
static void pushIfWhite(ArrayStack<Scope*> const &black,
                        ArrayStack<Scope*> &gray,
                        Scope *s)
{
  // in the black list?
  int i;
  for (i=0; i<black.length(); i++) {
    if (black[i] == s) {
      return;
    }
  }

  // in the gray list?
  for (i=0; i<gray.length(); i++) {
    if (gray[i] == s) {
      return;
    }
  }

  // not in either, color is effectively white, so push it
  gray.push(s);
}

// DFS over the network of using-directive edges
void Scope::getUsingClosure(ArrayStack<Scope*> &dest)
{
  // set of scopes already searched
  ArrayStack<Scope*> black;

  // stack of scopes remaining to be searched in the DFS
  ArrayStack<Scope*> gray;

  // initial condition
  gray.push(this);

  // process the gray set until empty
  while (gray.isNotEmpty()) {
    Scope *s = gray.pop();
    black.push(s);

    // add 's' to the desination list, except that 'this' is excluded
    if (s != this) {
      dest.push(s);
    }

    // push the "using" edges' targets
    for (int i=0; i < s->usingEdges.length(); i++) {
      pushIfWhite(black, gray, s->usingEdges[i]);
    }
  }
}


// return true if caller should return 'v'
bool Scope::foundViaUsingEdge(LookupSet &candidates, Env &env, LookupFlags flags,
                              Variable *v, Variable *&vfound)
{
  if (vfound) {
    if (!sameEntity(vfound, v)) {
      if (v->type->isFunctionType() &&
          vfound->type->isFunctionType()) {
        // ok; essentially they form an overload set
      }
      else {
        env.error(stringc
          << "ambiguous lookup: `" << vfound->fullyQualifiedName()
          << "' vs. `" << v->fullyQualifiedName() << "'");

        // originally I kept going in hopes of reporting more
        // interesting things, but now that the same scope can
        // appear multiple times on the active-using list, I
        // get multiple reports of the same thing, so bail after
        // the first
        return true;
      }
    }
  }
  else {
    vfound = v;
  }

  candidates.adds(v);

  return false;
}


Variable *Scope::searchActiveUsingEdges
  (LookupSet &candidates, StringRef name,
   Env &env, LookupFlags flags, Variable *vfound)
{
  // just consider the set of "active using" edges
  for (int i=0; i<activeUsingEdges.length(); i++) {
    Scope *s = activeUsingEdges[i];

    // look for 'name' in 's'
    Variable *v = s->lookupSingleVariable(name, flags);
    if (v) {
      if (foundViaUsingEdge(candidates, env, flags, v, vfound /*IN/OUT*/)) {
        return v;
      }
    }
  }

  return vfound;
}


// another DFS; 3.4.3.2 para 2
Variable *Scope::searchUsingEdges
  (LookupSet &candidates, StringRef name, Env &env, LookupFlags flags)
{
  // set of scopes already searched
  ArrayStack<Scope*> black;

  // stack of scopes remaining to be searched in the DFS
  ArrayStack<Scope*> gray;

  // initial condition
  gray.push(this);
  Variable *vfound = NULL;

  // process the gray set until empty
  while (gray.isNotEmpty()) {
    Scope *s = gray.pop();
    black.push(s);

    // does 's' have the name?
    Variable *v = s->lookupSingleVariable(name, flags);
    if (v) {
      if (foundViaUsingEdge(candidates, env, flags, v, vfound /*IN/OUT*/)) {
        return v;
      }
    }

    // if 's' does *not* have the name, then push the things it
    // points to
    else {
      // push the "using" edges' targets
      for (int i=0; i < s->usingEdges.length(); i++) {
        pushIfWhite(black, gray, s->usingEdges[i]);
      }
    }
  }

  return vfound;
}


// true if this scope is a member of the global scope
bool Scope::immediateGlobalScopeChild()
{
  return parentScope && parentScope->isGlobalScope();
}

// are we in a scope where the parent chain terminates in a global?
// That is, can fullyQualifiedName() be called on this scope without
// failing?
bool Scope::linkerVisible()
{
  if (parentScope) {
    return parentScope->linkerVisible();
  }
  else {
    return isGlobalScope();
  }
}


void fqn_STemplateArgs(stringBuilder &sb, ObjList<STemplateArgument> const &args,
                       bool doMangle)
{
  if (!doMangle) {
    sb << sargsToString(args);
  }
  else {
    mangleSTemplateArgs(sb, args);
  }
}


// FIX: Would be cleaner to implement this as a call to
// PQ_fullyQualifiedName() below and then to a toString() method.
// UPDATE: After long discussion with Scott, we determine that that
// idea is not practical.
// FIX: This is wrong as it does not take into account template
// arguments; Should be moved into CompoundType and done right.
//
// 8/09/04: sm: mangle=true is the original behavior of this function,
// mangle=false is the behavior I want
string Scope::fullyQualifiedName(bool mangle)
{
  // 7/28/04: I just changed things so that children of the global
  // scope have a non-NULL 'parentScope', and then adjusted this
  // code so it works like it used to.  I suspect this code could
  // be simplified in light of the new invariant.

  // a few places are still calling into this when it is the global
  // scope; since those places should be happy with "", and that is
  // in fact the "name" of the global scope, let's try this...
  if (isGlobalScope()) {
    return "";
  }

  stringBuilder sb;
  if (parentScope && !parentScope->isGlobalScope()) {
    sb = parentScope->fullyQualifiedName(mangle);
    if (!mangle) {
      sb << "::";     // put this only *between* names, so none at start
    }
  }
  else {
    if (!immediateGlobalScopeChild()) {
      // we didn't end up in the global scope; for example a function
      // in a class in a function. for now we don't add the outer scope
      // information and just hope there aren't collisions.
    }
  }
  if (mangle) {
    sb << "::";       // put this *before* names, so there is one at start
  }

  xassert(hasName());
  Variable *v = getTypedefName();
  xassert(v);
  if (v->name) {
    sb << v->name;
  }
  else {
    sb << "anonymous@" << toString(v->loc);    // anonymous namespaces
  };

  // return if no templates are involved
  if (!curCompound || !(curCompound->templateInfo())) return sb;
  TemplateInfo *tinfo = curCompound->templateInfo();
  if (tinfo->isPrimary()) {
    // print the params like arguments for a primary
    sb << tinfo->paramsLikeArgsToString();
  }
  else {
    if (tinfo->isInstantiation() &&
        tinfo->instantiationOf->templateInfo()->isPartialSpec()) {
      // print the partial spec args first, so then the instantiation
      // args can be interpreted relative to the partial spec args
      fqn_STemplateArgs(sb, tinfo->instantiationOf->templateInfo()->arguments,
                        mangle);
    }

    fqn_STemplateArgs(sb, tinfo->arguments, mangle);
  }

  return sb;
}


void Scope::setParameterizedEntity(Variable *entity)
{
  xassert(!parameterizedEntity);             // should do this only once
  xassert(isTemplateScope());                // doesn't make sense otherwise

  parameterizedEntity = entity;

  // arrange to delegate lookup to the entity if it is a compound
  if (entity->type->isCompoundType()) {
    CompoundType *ct = entity->type->asCompoundType();
    ct->setDelegationPointer(this);

    TRACE("templateParams", desc() << " now delegated to " << ct->desc());
  }

  // point all of the template parameters at the template
  for (StringRefMap<Variable>::Iter iter(variables);
       !iter.isDone(); iter.adv()) {
    Variable *param = iter.value();

    // should not already be parameterizing something
    xassert(!param->getParameterizedEntity());

    // this parameter parameterizes the template 'entity'
    param->setParameterizedEntity(entity);
  }
}


Variable *Scope::getScopeVariable() const
{
  if (curCompound) {
    return curCompound->typedefVar;
  }
  
  if (isNamespace() || isGlobalScope()) {
    return namespaceVar;
  }

  xfailure("getScopeVariable: not a compound or namespace");
  return NULL;    // silence warning
}


void Scope::traverse(TypeVisitor &vis)
{
  if (!vis.visitScope(this)) {
    return;
  }
  traverse_internal(vis);
  vis.postvisitScope(this);
}

void Scope::traverse_internal(TypeVisitor &vis)
{
  if (vis.visitScope_variables(variables)) {
    for(PtrMap<char const, Variable>::Iter iter(variables);
        !iter.isDone();
        iter.adv()) {
      StringRef name = iter.key();
      Variable *var = iter.value();
      if (vis.visitScope_variables_entry(name, var)) {
        var->traverse(vis);
        vis.postvisitScope_variables_entry(name, var);
      }
    }
    vis.postvisitScope_variables(variables);
  }

  if (vis.visitScope_typeTags(typeTags)) {
    for(PtrMap<char const, Variable>::Iter iter(typeTags);
        !iter.isDone();
        iter.adv()) {
      StringRef name = iter.key();
      Variable *var = iter.value();
      if (vis.visitScope_typeTags_entry(name, var)) {
        var->traverse(vis);
        vis.postvisitScope_typeTags_entry(name, var);
      }
    }
    vis.postvisitScope_typeTags(typeTags);
  }

  if (parentScope) {
    parentScope->traverse(vis);
  }
  if (namespaceVar) {
    namespaceVar->traverse(vis);
  }

  if (vis.visitScope_templateParams(templateParams)) {
    SFOREACH_OBJLIST_NC(Variable, templateParams, iter) {
      Variable *var = iter.data();
      if (vis.visitScope_templateParams_item(var)) {
        var->traverse(vis);
        vis.postvisitScope_templateParams_item(var);
      }
    }
    vis.postvisitScope_templateParams(templateParams);
  }

  // I don't think I need this; see Scott's comments in the scope
  // class
//    Variable *parameterizedEntity;          // (nullable serf)

  // --------------- for using-directives ----------------
  // Scott says that I don't need these

  // it is basically a bug that we need to serialize this but we do so
  // there it is.
//    CompoundType *curCompound;          // (serf) CompoundType we're building
//    Should not be being used after typechecking, but in theory could omit.
  if (curCompound) {
    curCompound->traverse(vis);
  }
}

// EOF
