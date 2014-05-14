// overload.cc                       see license.txt for copyright and terms of use
// code for overload.h

// This module intends to implement the overload resolution procedure
// described in cppstd clause 13.  However, there is a large gap
// between the English description there and an implementation in
// code, so it's likely there are omissions and deviations.

#include "overload.h"      // this module
#include "cc_env.h"        // Env
#include "variable.h"      // Variable
#include "cc_type.h"       // Type, etc.
#include "trace.h"         // TRACE
#include "typelistiter.h"  // TypeListIter
#include "strtokp.h"       // StrtokParse
#include "mtype.h"         // MType


// ------------------- Candidate -------------------------
Candidate::Candidate(Variable *v, Variable *instFrom0, int numArgs)
  : var(v)
  , instFrom(instFrom0)
  , conversions(numArgs)
{}

Candidate::~Candidate()
{}


bool Candidate::hasAmbigConv() const
{
  for (int i=0; i < conversions.size(); i++) {
    if (conversions[i].isAmbiguous()) {
      return true;
    }
  }
  return false;
}


void Candidate::conversionDescriptions() const
{
  for (int i=0; i < conversions.size(); i++) {
    OVERLOADTRACE(i << ": " << toString(conversions[i]));
  }
}


Type *OverloadResolver::getReturnType(Candidate const *winner) const
{
  FunctionType *ft = winner->var->type->asFunctionType();
  Type *retType = ft->retType;
  if (!retType->isSimpleType()) {
    return retType;      // easy
  }

  SimpleTypeId retId = retType->asSimpleTypeC()->type;
  if (isConcreteSimpleType(retId)) {
    return retType;      // also easy
  }

  // At this point, we do not have a concrete return type, but
  // rather an algorithm for computing a return type given
  // the types of the parameters.
  //
  // However, we also do not have easy access to the parameter types
  // if they are polymorphic, which they must be for us to not have
  // had a concrete type above.  What we have instead is the argument
  // types and the conversion sequences that lead to the parameter
  // types, so we need to use them to find the actual parameter types.

  ArrayStack<Type*> concreteParamTypes;
  int i = 0;
  SFOREACH_OBJLIST(Variable, ft->params, paramIter) {
    // get the polymorphic param type

    // have:
    Type *argType = args[i].type;                            // arg type
    ImplicitConversion const &conv = winner->conversions[i]; // conversion
    Type *paramType = paramIter.data()->type;    // param type, possibly polymorphic

    // want: concrete parameter type
    concreteParamTypes.push(conv.getConcreteDestType(env.tfac, argType, paramType));

    i++;
  }

  // Ok!  Now we have some concrete parameter types, and can apply
  // the algorithm specified by 'retId'.
  switch (retId) {                                    
    // if this fails, we should have detected above that a concrete
    // return type was available
    default: xfailure("bad return type algorithm id");

    // e.g.: T operator++ (VQ T&, int)
    case ST_PRET_STRIP_REF: {
      Type *vqT = concreteParamTypes[0]->getAtType();
      return env.tfac.setQualifiers(SL_UNKNOWN, CV_NONE, vqT, NULL /*syntax*/);
    }

    // see ArrowStarCandidateSet::instantiateCandidate
    case ST_PRET_PTM:
      xfailure("ST_PRET_PTM is handled elsewhere");

    // e.g. T& operator* (T*)
    case ST_PRET_FIRST_PTR2REF: {
      Type *T = concreteParamTypes[0]->getAtType();
      return env.tfac.makeReferenceType(T);
    }

    // see E_binary::itcheck_x and resolveOverloadedBinaryOperator
    case ST_PRET_SECOND_PTR2REF:
      xfailure("ST_PRET_SECOND_PTR2REF is handled elsewhere");

    // e.g.: LR operator* (L, R)
    case ST_PRET_ARITH_CONV:
      return usualArithmeticConversions(env.tfac, 
               concreteParamTypes[0], concreteParamTypes[1]);

    // e.g.: L operator<< (L, R)
    case ST_PRET_FIRST:
      return concreteParamTypes[0];

    // e.g.: T* operator+ (ptrdiff_t, T*)
    case ST_PRET_SECOND:
      return concreteParamTypes[1];
  }
}


// ------------------ resolveOverload --------------------
// prototypes
int compareConversions(ArgumentInfo const &src,
  ImplicitConversion const &left, Type const *leftDest,
  ImplicitConversion const &right, Type const *rightDest);
int compareStandardConversions
  (ArgumentInfo const &leftSrc, StandardConversion left, Type const *leftDest,
   ArgumentInfo const &rightSrc, StandardConversion right, Type const *rightDest);
bool convertsPtrToBool(Type const *src, Type const *dest);
bool isPointerToCompound(Type const *type, CompoundType const *&ct);
bool isReferenceToCompound(Type const *type, CompoundType const *&ct);
bool isPointerToCompoundMember(Type const *type, CompoundType const *&ct);
bool isBelow(CompoundType const *low, CompoundType const *high);
bool isProperSubpath(CompoundType const *LS, CompoundType const *LD,
                     CompoundType const *RS, CompoundType const *RD);



// this function can be used anyplace that there's only one list
// of original candidate functions
Variable *resolveOverload(
  Env &env,
  SourceLoc loc,
  ErrorList * /*nullable*/ errors,
  OverloadFlags flags,
  SObjList<Variable> &varList,
  PQName *finalName,
  GrowArray<ArgumentInfo> &args,
  bool &wasAmbig)
{
  OverloadResolver r(env, loc, errors, flags, finalName, args, varList.count());
  r.processCandidates(varList);
  return r.resolve(wasAmbig);
}


OverloadResolver::OverloadResolver
  (Env &en, SourceLoc L, ErrorList *er,
   OverloadFlags f,
   PQName *finalName0,
   GrowArray<ArgumentInfo> &a,
   int numCand)
  : env(en),
    loc(L),
    errors(er),
    flags(f),
    finalName(finalName0),
    args(a),
    finalDestType(NULL),
    emptyCandidatesIsOk(false),

    // this estimate does not have to be perfect; if it's high,
    // then more space will be allocated than necessary; if it's
    // low, then the 'candidates' array will have to be resized
    // at some point; it's entirely a performance issue
    candidates(numCand),
    origCandidates(numCand)
{
  //overloadNesting++;

  // part of 14.7.1 para 4: If any argument types is a reference to a
  // template class instantiation, but the body has not been
  // instantiated yet, instantiate it.
  //
  // Further, if an argument is (a reference to) a class type and that
  // class has conversion operators that yield pointers or references
  // to template class instnatiations, make sure *their* bodies are
  // instantiated too.
  //
  // All this could conceivably be too much instantiation, as I could
  // imagine that some of these don't necessarily "affect the
  // semantics of the program"; but 14.7.1 para 5 goes on to say that
  // even if you can do overload resolution without instantiating some
  // class, it's ok to do so anyway.  Of course, this begs the
  // question: exactly which classes are in their margin for error?
  // Clearly they don't mean that all instantiations in the program
  // are fair game (14.7.1 para 9), but they do not specify how
  // tangentially related something must be to the overload resolution
  // at hand before it's allowed to be instantiated...
  //
  // 9/22/04: As demonstrated by t0293.cc, we also need to instantiate
  // classes mentioned by way of pointers (in addition to references),
  // to enable derived-to-base conversions.
  for (int i=0; i < args.size(); i++) {
    Type *argType = a[i].type;
    if (!argType) continue;

    argType = argType->asRval();     // skip references
    if (argType->isPointerType()) {  // skip pointers (9/22/04)
      argType = argType->asPointerType()->atType;
    }

    if (argType->isCompoundType()) {
      CompoundType *argCT = argType->asCompoundType();

      // instantiate the argument class if necessary
      env.ensureClassBodyInstantiated(argCT);

      // iterate over the set of conversion operators
      if (argCT->isComplete()) {      // non-instantiations can be incomplete here
        SFOREACH_OBJLIST(Variable, argCT->conversionOperators, iter) {
          Type *convType = iter.data()->type->asFunctionTypeC()->retType;

          // we should only need to consider pointers or references;
          // if 'convType' is itself an instantiation, it should have
          // had its body instantiated when its containing class body
          // was tchecked
          if (convType->isPtrOrRef()) {
            Type *convAtType = convType->getAtType();
            if (convAtType->isCompoundType()) {
              env.ensureClassBodyInstantiated(convAtType->asCompoundType());
            }
          }
        }
      }
    }
  }

  printArgInfo();
}


void OverloadResolver::printArgInfo()
{
  IFDEBUG(
    if (tracingSys("overload")) {
      string info = argInfoString();
      
      // it's a little inefficient to construct the string only to
      // parse it at line boundaries, but I want the indentation to
      // be a certain way, and this is only done in debug mode (and
      // even then, only with the tracing flag enabled)
      StrtokParse tok(info, "\n");
      for (int i=0; i<tok; i++) {
        overloadTrace() << tok[i] << "\n";
      }
    }
  )
}

string OverloadResolver::argInfoString()
{
  stringBuilder sb;
  sb << "arguments:\n";
  for (int i=0; i < args.size(); i++) {
    if (args[i].overloadSet.isEmpty() &&
        !args[i].type) {
      continue;      // don't print anything
    }

    sb << "  " << i << ": ";

    if (args[i].overloadSet.isNotEmpty()) {
      sb << "(13.4 set) ";
      int ct=0;
      SFOREACH_OBJLIST_NC(Variable, args[i].overloadSet, iter) {
        if (ct++ > 0) {
          sb << " or ";
        }
        sb << iter.data()->type->toString();
      }
    }
    else {
      sb << args[i].type->toString();
    }

    if (args[i].special) {
      sb << " (" << toString(args[i].special) << ")";
    }

    sb << "\n";
  }

  return sb;
}


OverloadResolver::~OverloadResolver()
{
  //overloadNesting--;
}


void OverloadResolver::processCandidates(SObjList<Variable> &varList)
{
  SFOREACH_OBJLIST_NC(Variable, varList, iter) {
    xassert(!(iter.data()->notQuantifiedOut()));
    processCandidate(iter.data());
  }
}

 
void OverloadResolver::addCandidate(Variable *var0, Variable *instFrom)
{
  xassert(var0);
  Candidate *c = makeCandidate(var0, instFrom);
  if (c) {
    IFDEBUG( c->conversionDescriptions(); )
    candidates.push(c);

    // part of 14.7.1 para 4: If a candidate function parameter is
    // (a reference to) a template class instantiation, force its body
    // to be instantiated.
    env.instantiateTemplatesInParams(var0->type->asFunctionType());
  }
  else {
    OVERLOADTRACE("(not viable)");
  }
}

void OverloadResolver::addTemplCandidate
  (Variable *baseV, Variable *var0, ObjList<STemplateArgument> &sargs)
{
  Variable *var0inst =
    env.instantiateFunctionTemplate
    (env.loc(),
     baseV,
     sargs);

  if (var0inst) {
    xassert(var0inst->templateInfo()->isCompleteSpecOrInstantiation());

    // try adding the candidate
    addCandidate(var0inst, var0);
  }
  else {
    env.error("failed function template instantiation");
  }
}

void OverloadResolver::processCandidate(Variable *v)
{
  OVERLOADINDTRACE("candidate: " << v->toString() <<
                   " at " << toString(v->loc));

  if ((flags & OF_NO_EXPLICIT) && v->hasFlag(DF_EXPLICIT)) {
    // not a candidate, we're ignoring explicit constructors
    OVERLOADTRACE("(not viable due to 'explicit')");
    return;
  }

  if (!v->isTemplate(false /*considerInherited*/)) {
    // 2005-02-18: Since reorganizing call site name lookup, I am now
    // doing overload resolution among *instantiations*, rather than
    // template primaries.
    Variable *instFrom = NULL;
    if (v->isInstantiation()) {
      // what is it an instantiation of?
      instFrom = v->templateInfo()->instantiationOf;
      xassert(instFrom);
                                                                   
      // do not consider members of template classes to be templates
      // (in/t0269.cc)
      if (!instFrom->isTemplate(false /*considerInherited*/)) {
        instFrom = NULL;
      }
    }

    addCandidate(v, instFrom);
    return;
  }

  // Q: Can this point be reached?
  //
  // A: Yes, in/t0269.cc gets here.  E_constructor still does overload
  // resolution with template primaries.  It's not clear whether that
  // is a problem or not; it's a lot simpler than E_funCall.

  // template function; we have to filter out all of the possible
  // specializations and put them, together with the primary, into the
  // candidates list
  TemplateInfo *vTI = v->templateInfo();
  xassert(vTI->isPrimary());

  // get the semantic template arguments
  ObjList<STemplateArgument> sargs;
  {
    InferArgFlags iflags = IA_NO_ERRORS;
    if (flags & OF_METHODS) {
      iflags |= IA_RECEIVER;
    }
    
    // (in/t0484.cc) an operator invocation site's LHS argument is the
    // receiver when we are considering operators that are methods;
    // but if the operator is a global function, then the LHS is not
    // a receiver, but just an ordinary argument
    if ((flags & OF_OPERATOR) && (v->type->asFunctionType()->isMethod())) {
      iflags |= IA_RECEIVER;
    }

    // FIX: This is a bug!  If the args contain template parameters,
    // they will be the wrong template parameters.
    GrowArray<ArgumentInfo> &args0 = this->args;
    // FIX: check there are no dependent types in the arguments
    TypeListIter_GrowArray argListIter(args0);
    MType match(env);
    if (!env.getFuncTemplArgs(match, sargs, finalName, v, argListIter, iflags)) {
      // something doesn't work about processing the template arguments
      OVERLOADTRACE("(not viable because args to not match template params)");
      return;
    }
  }

  // FIX: the following is copied from Env::findMostSpecific(); it
  // could be factored out and merged but adding to the list in the
  // inner loop would be messy; you would have to make it an iterator
  SFOREACH_OBJLIST_NC(Variable, vTI->specializations, iter) {
    Variable *var0 = iter.data();
    TemplateInfo *templInfo0 = var0->templateInfo();
    xassert(templInfo0);      // should have templateness
    
    // see if this candidate matches
    MType match;
    if (!match.matchSTemplateArguments(sargs, templInfo0->arguments, MF_MATCH)) {
      // if not, skip it
      continue;
    }

    addTemplCandidate(v, var0, sargs);
  }

  // add the primary also
  addTemplCandidate(v, v, sargs);
}


void OverloadResolver::processPossiblyOverloadedVar(Variable *v)
{
  if (v->overload) {
    processCandidates(v->overload->set);
  }
  else {
    processCandidate(v);
  }
}


void OverloadResolver::addAmbiguousBinaryCandidate(Variable *v)
{
  Candidate *c = new Candidate(v, NULL /*instFrom*/, 2);
  c->conversions[0].addAmbig();
  c->conversions[1].addAmbig();

  OVERLOADINDTRACE("candidate: ambiguous-arguments placeholder");
  IFDEBUG( c->conversionDescriptions(); )
  
  candidates.push(c);
}


static EnumType *ifEnumType(Type *t)
{
  if (t && t->isCVAtomicType()) {
    CVAtomicType *cvat = t->asCVAtomicType();
    if (cvat->atomic->isEnumType()) {
      return cvat->atomic->asEnumType();
    }
  }
  return NULL;
}

static bool parameterAcceptsDirectly(EnumType *et, FunctionType *ft, int param)
{
  if (et &&
      ft->params.count() > param) {
    Type *paramType = ft->params.nth(param)->type;
                                    
    // treat 'T&' the same as 'T'
    paramType = paramType->asRval();
    
    // get down to an enumtype
    EnumType *paramEnumType = ifEnumType(paramType);

    return paramEnumType && et->equals(paramEnumType);
  }

  return false;
}

void OverloadResolver::addUserOperatorCandidates
  (Type * /*nullable*/ lhsType, Type * /*nullable*/ rhsType, StringRef opName)
{                      
  if (lhsType) {
    lhsType = lhsType->asRval();
  }
  if (rhsType) {
    rhsType = rhsType->asRval();
  }

  // member candidates
  if (lhsType && lhsType->isCompoundType()) {
    Variable *member = lhsType->asCompoundType()->lookupVariable(opName, env);
    if (member) {
      processPossiblyOverloadedVar(member);
    }
  }

  // non-member candidates
  LookupSet candidates;
  {
    // 13.3.1.2 para 3 bullet 2: "... all member functions are ignored."
    LookupFlags flags = LF_SKIP_CLASSES;

    // associated scopes lookup
    ArrayStack<Type*> argTypes(2);
    if (lhsType) {
      argTypes.push(lhsType);
    }
    if (rhsType) {
      argTypes.push(rhsType);
    }
    env.associatedScopeLookup(candidates, opName, argTypes, flags);

    // ordinary lookup
    { 
      Scope *dummy;
      env.lookupVariable_set(candidates, opName, flags, dummy);
    }
    
    // filter candidates if no class-typed args
    if ((lhsType && lhsType->isCompoundType()) ||
        (rhsType && rhsType->isCompoundType())) {
      // at least one arg is of class type; nothing special is done
    }
    else {
      // no class-typed arguments; at least one must be enumeration type
      // (otherwise operator overload resolution isn't done at all),
      // and we require that every candidate explicitly accept one of
      // the enumeration types
      EnumType *et1 = ifEnumType(lhsType);
      EnumType *et2 = ifEnumType(rhsType);

      SObjListMutator<Variable> mut(candidates);
      while (!mut.isDone()) {
        FunctionType *ft = mut.data()->type->asFunctionType();

        if (parameterAcceptsDirectly(et1, ft, 0) ||
            parameterAcceptsDirectly(et2, ft, 1)) {
          // ok, keep it
          mut.adv();
        }
        else {
          // drop it
          mut.remove();
        }
      }
    }
  }

  // process the resulting set
  SFOREACH_OBJLIST_NC(Variable, candidates, iter) {
    processCandidate(iter.data());
  }
}


void OverloadResolver::addBuiltinUnaryCandidates(OverloadableOp op)
{
  ArrayStack<Variable*> &builtins = env.builtinUnaryOperator[op];
  for (int i=0; i < builtins.length(); i++) {
    processCandidate(builtins[i]);
  }
}


void OverloadResolver::addBuiltinBinaryCandidates(OverloadableOp op,
  ArgumentInfo &lhsInfo, ArgumentInfo &rhsInfo)
{
  ObjArrayStack<CandidateSet> &builtins = env.builtinBinaryOperator[op];
  for (int i=0; i < builtins.length(); i++) {
    builtins[i]->instantiateBinary(env, *this, op, lhsInfo, rhsInfo);
  }
}


// this is a simple tournament, as suggested in footnote 123,
// cppstd 13.3.3 para 2
template <class RESOLVER, class CANDIDATE>
CANDIDATE *tournament(RESOLVER &resolver, int low, int high, CANDIDATE *dummy)
{
  xassert(low <= high);         // Scott, you should catch this!

  if (low == high) {
    // only one candidate
    return resolver.candidates[low];
  }

  // divide the pool in half and select a winner from each half
  int mid = (low+high+1)/2;
    // 1,3 -> 2
    // 1,2 -> 2
    // 2,3 -> 3
  CANDIDATE *left = tournament(resolver, low, mid-1, dummy);
  CANDIDATE *right = tournament(resolver, mid, high, dummy);

  // compare the candidates to get one that is not worse than the other
  int choice = resolver.compareCandidates(left, right);
  if (choice <= 0) {
    return left;    // left is better, or neither is better or worse
  }
  else {
    return right;   // right is better
  }
}


// tournament, plus final linear scan to ensure it's the best; the
// dummy argument is just to instantiate the 'CANDIDATE' type
template <class RESOLVER, class CANDIDATE>
CANDIDATE *selectBestCandidate(RESOLVER &resolver, CANDIDATE *dummy)
{
  // dsw: I need this to be the semantics of this function, rather
  // than an error; If you change it, change the class specialization
  // resolution code also.
  if (resolver.candidates.length() <= 0) {
    return NULL;
  }

  // use a tournament to select a candidate that is not worse
  // than any of those it faced
  CANDIDATE *winner = tournament(resolver, 0, resolver.candidates.length()-1, dummy);

  // now verify that the picked winner is in fact better than any
  // of the other candidates (since the order is not necessarily linear)
  for (int i=0; i < resolver.candidates.length(); i++) {
    if (resolver.candidates[i] == winner) {
      continue;    // skip it, no need to compare to itself
    }

    if (resolver.compareCandidates(winner, resolver.candidates[i]) == -1) {
      // ok, it's better
    }
    else {
      // not better, so there is no function that is better than
      // all others
      return NULL;
    }
  }

  // 'winner' is indeed the winner
  return winner;
}


// dsw: I put this here so that I didn't have to put the whole
// selectBestCandidate() templatized function into overload.h
Variable *selectBestCandidate_templCompoundType(TemplCandidates &resolver)
{
  Variable *dummy = NULL; 
    // dsw: this dummy idiom is dumb
    // sm: horsepucky!

  return selectBestCandidate(resolver, dummy);
}


Candidate const *OverloadResolver::resolveCandidate(bool &wasAmbig)
{
  wasAmbig = false;

  if (candidates.isEmpty()) {
    if (emptyCandidatesIsOk) {
      return NULL;      // caller is prepared to deal with this
    }

    if (errors) {
      // try to construct a meaningful error message; it does not
      // end with a newline since the usual error reporting mechanism
      // adds one
      stringBuilder sb;
      sb << "no viable candidate for "
         << ((flags & OF_OPERATOR)? "operator; " : "function call; ")
         << argInfoString();
      if (origCandidates.length()) {
        sb << " original candidates:";
        for (int i=0; i<origCandidates.length(); i++) {
          Variable *v = origCandidates[i];

          // it might be nice to go further and explain why this
          // candidate was not viable ...
          sb << "\n  " << v->loc << ": " << v->toQualifiedString();
        }
      }
      else {
        sb << " (no original candidates)";
      }

      errors->addError(new ErrorMsg(loc, sb, EF_NONE));
    }
    OVERLOADTRACE("no viable candidates");
    return NULL;
  }

  if (finalDestType) {
    // include this in the diagnostic output so that I can tell
    // when it will play a role in candidate comparison
    OVERLOADTRACE("finalDestType: " << finalDestType->toString());
  }

  // use a tournament to select a candidate that is not worse
  // than any of those it faced
  Candidate const *winner = selectBestCandidate(*this, (Candidate const*)NULL);
  if (!winner) {
    // if any of the candidates contain variables, then this
    // conclusion of ambiguity is suspect (in/t0573.cc)
    for (int i=0; i<candidates.length(); i++) {
      Variable *v = candidates[i]->var;
      if (v->type->containsVariables()) {
        goto ambig_bail;
      }
    }

    if (errors) {
      stringBuilder sb;
      sb << "ambiguous overload; " << argInfoString() << " candidates:";
      for (int i=0; i<candidates.length(); i++) {
        Variable *v = candidates[i]->var;
        sb << "\n  " << v->loc << ": " << v->toQualifiedString();
      }
      errors->addError(new ErrorMsg(loc, sb, EF_NONE));
    }

  ambig_bail:
    OVERLOADTRACE("ambiguous overload");
    wasAmbig = true;
    return NULL;
  }

  OVERLOADTRACE(toString(loc)
    << ": selected " << winner->var->toString()
    << " at " << toString(winner->var->loc));

  if (winner->hasAmbigConv()) {
    // At least one of the conversions required for the winning candidate
    // is ambiguous.  This might actually mean, had we run the algorithm
    // as specified in the spec, that there's an ambiguity among the
    // candidates, since I fold some of that into the selection of the
    // conversion, for polymorphic built-in operator candidates.  Therefore,
    // this situation should appear to the caller the same as when we
    // definitely do have ambiguity among the candidates.
    if (errors) {
      errors->addError(new ErrorMsg(
        loc, "ambiguous overload or ambiguous conversion", EF_NONE));
    }
    OVERLOADTRACE("ambiguous overload or ambiguous conversion");
    wasAmbig = true;
    return NULL;
  }

  return winner;
}


Variable *OverloadResolver::resolve(bool &wasAmbig)
{
  Candidate const *winner = resolveCandidate(wasAmbig);
  if (!winner) {
    return NULL;
  }

  // dsw: I've decided to agressively instantiate the template since
  // everything downstream from here seems to assume that it has not
  // gotten a template but a real variable with a real type etc.
  // NOTE: if you do the optimization of instantiating only the
  // function signatures and not the whole body then here is the place
  // you would actually do the whole body instantiation; for now there
  // is nothing to do here as it has already been done
  //
  // sm: TODO: Yes, we do need to delay instantiation until after
  // overload resolution selects the function, as part of the delayed
  // instantiation for class member functions.  See in/t0233.cc.
  Variable *retV = winner->var;
  if (winner->instFrom) {
    // instantiation is now done during candidate processing
    xassert(retV->templateInfo());
    xassert(retV->templateInfo()->isCompleteSpecOrInstantiation());
  } else {
    // sm: in/t0411.cc causes this to fail, because we (correctly) 
    // do overload resolution while analyzing an uninstantiated
    // template body, and the winner is a member of that template,
    // so it *is* a template but is *not* instantiated from anything
    //xassert(!retV->isTemplate());
  }

  return retV;
}

Variable *OverloadResolver::resolve()
{
  bool dummy;
  return resolve(dummy);
}


// for each parameter, determine an ICS, and return the resulting
// Candidate; return NULL if the function isn't viable; this
// implements cppstd 13.3.2
Candidate * /*owner*/ OverloadResolver::makeCandidate
  (Variable *var, Variable *instFrom)
{
  origCandidates.push(var);
  Owner<Candidate> c(new Candidate(var, instFrom, args.size()));

  FunctionType *ft = var->type->asFunctionType();

  // simultaneously iterate over parameters and arguments
  SObjListIter<Variable> paramIter(ft->params);
  int argIndex = 0;

  // handle mismatches between presence of receiver and method-ness
  if (flags & OF_METHODS) {      // receiver is present
    if (!args[argIndex].type && ft->isMethod()) {
      // no receiver object but function is a method: not viable
      return NULL;
    }
    if (!ft->isMethod()) {
      // no receiver parameter; leave the conversion as IC_NONE
      argIndex++;       // do *not* advance 'paramIter'
    }
  }

  for (; !paramIter.isDone() && argIndex < args.size();
       paramIter.adv(), argIndex++) {
    // address of overloaded function?
    if (args[argIndex].overloadSet.isNotEmpty()) {
      Variable *selVar =
        env.pickMatchingOverloadedFunctionVar(args[argIndex].overloadSet,
                                              paramIter.data()->type);
      if (selVar) {
        // just say it matches; we don't need to record *which* one was
        // chosen, because that will happen later when the arguments are
        // checked against the parameters of the chosen function
        ImplicitConversion ics;
        ics.addStdConv(SC_IDENTITY);
        c->conversions[argIndex] = ics;

        // go to next arg/param pair
        continue;
      }
      else {
        // whole thing not viable
        return NULL;
      }
    }

    bool destIsReceiver = argIndex==0 && ft->isMethod();

    if (flags & OF_NO_USER) {
      // only consider standard conversions
      StandardConversion scs =
        getStandardConversion(NULL /*errorMsg*/,
                              args[argIndex].special, args[argIndex].type,
                              paramIter.data()->type, destIsReceiver);
      if (scs != SC_ERROR) {
        ImplicitConversion ics;
        ics.addStdConv(scs);
        c->conversions[argIndex] = ics;
      }
      else {
        return NULL;
      }
    }
    else {
      // consider both standard and user-defined
      ImplicitConversion ics =
        getImplicitConversion(env, args[argIndex].special, args[argIndex].type,
                              paramIter.data()->type, destIsReceiver);
      if (ics) {
        c->conversions[argIndex] = ics;
      }
      else {
        return NULL;           // no conversion sequence possible
      }
    }
  }

  // extra arguments?
  if (argIndex < args.size()) {
    if (ft->acceptsVarargs()) {
      // fill remaining with IC_ELLIPSIS
      ImplicitConversion ellipsis;
      ellipsis.addEllipsisConv();
      while (argIndex < args.size()) {
        c->conversions[argIndex] = ellipsis;
        argIndex++;
      }
    }
    else {
      // too few arguments, cannot form a conversion
      return NULL;
    }
  }

  // extra parameters?
  if (!paramIter.isDone()) {
    if (paramIter.data()->value) {
      // the next parameter has a default value, which implies all
      // subsequent parameters have default values as well; for
      // purposes of overload resolution, we simply ignore the extra
      // parameters [cppstd 13.3.2 para 2, third bullet]
    }
    else {
      // no default value, argument must be supplied but is not,
      // so cannot form a conversion
      return NULL;
    }
  }

  return c.xfr();
}

  
// 14.5.5.2 paras 3 and 4
bool atLeastAsSpecializedAs(Env &env, Type *concrete, Type *pattern)
{
  // TODO: this isn't quite right:
  //   - I use the return type regardless of whether this is
  //     a template conversion function
  //   - I don't do "argument deduction", I just match.  Maybe
  //     that is equivalent?

  MType match(env);
  return match.matchTypeNC(concrete, pattern, MF_MATCH);
}


// compare overload candidates, returning:
//   -1 if left is better
//    0 if they are indistinguishable
//   +1 if right is better
// this is cppstd 13.3.3 para 1, second group of bullets
int OverloadResolver::compareCandidates(Candidate const *left, Candidate const *right)
{
  // decision so far
  int ret = 0;

  // is exactly one candidate a built-in operator?
  if ((int)left->var->hasFlag(DF_BUILTIN) +
      (int)right->var->hasFlag(DF_BUILTIN) == 1) {
    // 13.6 para 1 explains that if a user-written candidate and a
    // built-in candidate have the same signature, then the built-in
    // candidate is hidden; I implement this by saying that the
    // user-written candidate always wins
    if (left->var->type->equals(right->var->type, MF_IGNORE_RETURN)) {
      // same signatures; who wins?
      if (left->var->hasFlag(DF_BUILTIN)) {
        return +1;     // right is user-written, it wins
      }
      else {
        return -1;     // left is user-written, it wins
      }
    }
  }

  // iterate over parameters too, since we need to know the
  // destination type in some cases
  FunctionType const *leftFunc = left->var->type->asFunctionTypeC();
  FunctionType const *rightFunc = right->var->type->asFunctionTypeC();
  SObjListIter<Variable> leftParam(leftFunc->params);
  SObjListIter<Variable> rightParam(rightFunc->params);

  // argument index
  int i = 0;

  if (flags & OF_METHODS) {
    if (!leftFunc->isMethod() || !rightFunc->isMethod()) {
      // for nonmethods, the receiver param is ignored
      i++;
      if (leftFunc->isMethod()) {
        leftParam.adv();
      }
      if (rightFunc->isMethod()) {
        rightParam.adv();
      }
    }
  }

  // walk through list of arguments, comparing the conversions
  for (; i < args.size(); i++) {
    // get parameter types; they can be NULL if we walk off into the ellipsis
    // of a variable-argument function
    Type const *leftDest = NULL;
    if (!leftParam.isDone()) {
      leftDest = leftParam.data()->type;
      leftParam.adv();
    }
    Type const *rightDest = NULL;
    if (!rightParam.isDone()) {
      rightDest = rightParam.data()->type;
      rightParam.adv();
    }

    int choice = compareConversions(args[i], left->conversions[i], leftDest,
                                             right->conversions[i], rightDest);
    if (ret == 0) {
      // no decision so far, fold in this comparison
      ret = choice;
    }
    else if (choice == 0) {
      // this comparison offers no information
    }
    else if (choice != ret) {
      // this comparison disagrees with a previous comparison, which
      // makes two candidates indistinguishable
      return 0;
    }
  }

  if (ret != 0) {
    return ret;     // at least one of the comparisons is decisive
  }

  // the next comparison says that non-templates are better than
  // template function *specializations*.. I'm not entirely sure
  // what "specialization" means, whether it's something declared using
  // the specialization syntax or just an instance of a template..
  // I'm going to use the latter interpretation since I think it
  // makes more sense
  if (!left->instFrom && right->instFrom) {
    return -1;     // left is non-template
  } else if (left->instFrom && !right->instFrom) {
    return +1;     // right is non-template
  }

  // next rule talks about comparing templates to find out which is
  // more specialized
  if (left->instFrom && right->instFrom) {
    // sm: I think we just compare the candidates directly; there is
    // no notion of partial specialization for function templates, so
    // all the old stuff about primaries doesn't make sense

    // this section implements cppstd 14.5.5.2

    // NOTE: we use the instFrom field here instead of the var
    Type *leftType = left->instFrom->type;
    Type *rightType = right->instFrom->type;

    // who is "at least as specialized" as who?
    bool left_ALA = atLeastAsSpecializedAs(env, leftType, rightType);
    bool right_ALA = atLeastAsSpecializedAs(env, rightType, leftType);
    if (left_ALA && !right_ALA) {
      // left is "more specialized"
      return -1;
    }
    else if (!left_ALA && right_ALA) {
      // right is "more specialized"
      return +1;
    }
    else {
      // fall through to remaining tests
    }
  }

  // if we're doing "initialization by user-defined conversion", then
  // look at the conversion sequences to the final destination type
  if (finalDestType) {
    StandardConversion leftSC = getStandardConversion(
      NULL /*errorMsg*/, SE_NONE, leftFunc->retType, finalDestType);
    StandardConversion rightSC = getStandardConversion(
      NULL /*errorMsg*/, SE_NONE, rightFunc->retType, finalDestType);

    ret = compareStandardConversions(
      ArgumentInfo(SE_NONE, leftFunc->retType), leftSC, finalDestType,
      ArgumentInfo(SE_NONE, rightFunc->retType), rightSC, finalDestType
    );
    if (ret != 0) {
      return ret;
    }
  }

  // no more rules remain, candidates are indistinguishable
  return 0;
}


// compare two conversion sequences, returning the same choice code
// as above; we need to know the source type and the destination types,
// because some of the comparison criteria use them; this implements
// cppstd 13.3.3.2
int compareConversions(ArgumentInfo const &src,
  ImplicitConversion const &left, Type const *leftDest,
  ImplicitConversion const &right, Type const *rightDest)
{
  // para 2: choose based on what kind of conversion:
  //   standard < user-defined/ambiguous < ellipsis
  {
    static int const map[ImplicitConversion::NUM_KINDS] = {
      0,    // none
      1,    // standard
      2,    // user-defined
      3,    // ellipsis
      2     // ambiguous
    };

    int leftGroup = map[left.kind];
    int rightGroup = map[right.kind];
    xassert(leftGroup && rightGroup);   // make sure neither is IC_NONE

    if (leftGroup < rightGroup) return -1;
    if (rightGroup < leftGroup) return +1;
  }

  if (left.kind == ImplicitConversion::IC_AMBIGUOUS || 
      right.kind == ImplicitConversion::IC_AMBIGUOUS) {
    return 0;    // indistinguishable
  }

  // para 3: compare among same-kind conversions
  xassert(left.kind == right.kind);

  // para 3, bullet 1
  if (left.kind == ImplicitConversion::IC_STANDARD) {
    return compareStandardConversions(src, left.scs, leftDest,
                                      src, right.scs, rightDest);
  }

  // para 3, bullet 2
  if (left.kind == ImplicitConversion::IC_USER_DEFINED) {
    if (left.user != right.user) {
      // different conversion functions, incomparable
      return 0;
    }

    // compare their second conversion sequences
    ArgumentInfo src(SE_NONE, left.user->type->asFunctionTypeC()->retType);
    return compareStandardConversions(src, left.scs2, leftDest,
                                      src, right.scs2, rightDest);
  }
  
  // if ellipsis, no comparison
  xassert(left.kind == ImplicitConversion::IC_ELLIPSIS);
  return 0;
}


inline void swap(CompoundType const *&t1, CompoundType const *&t2)
{
  CompoundType const *temp = t1;
  t1 = t2;
  t2 = temp;
}


// this is a helper for 'compareStandardConversions'; it incorporates
// the knowledge of having found two more cv flag pairs in a
// simultaneous deconstruction of two types that are being compared;
// ultimately it wants to set 'ret' to -1 if all the 'lcv's are
// subsets of all the 'rcv's, and +1 if the subset goes the other way;
// it returns 'true' if the subset relation does not hold
static bool foldNextCVs(int &ret, CVFlags lcv, CVFlags rcv, int &skipCVs)
{
  if (skipCVs) {
    skipCVs--;
    return false;
  }

  if (lcv != rcv) {
    if ((lcv & rcv) == lcv) {    // left is subset, => better
      if (ret > 0) return true;  // but right was better previously, => no decision
      ret = -1;
    }
    if ((lcv & rcv) == rcv) {    // right is subset, => better
      if (ret < 0) return true;  // but left was better previously, => no decision
      ret = +1;
    }
  }
  return false;                  // no problem found
}


int compareStandardConversions
  (ArgumentInfo const &leftSrc, StandardConversion left, Type const *leftDest,
   ArgumentInfo const &rightSrc, StandardConversion right, Type const *rightDest)
{
  // if one standard conversion sequence is a proper subsequence of
  // another, excluding SC_LVAL_TO_RVAL, then the smaller one is
  // preferred
  {
    StandardConversion L = removeLval(left);
    StandardConversion R = removeLval(right);
    if (L != R) {
      if (isSubsequenceOf(L, R)) return -1;
      if (isSubsequenceOf(R, L)) return +1;
    }
  }

  // compare ranks of conversions
  SCRank leftRank = getRank(left);
  SCRank rightRank = getRank(right);
  if (leftRank < rightRank) return -1;
  if (rightRank < leftRank) return +1;

  // 13.3.3.2 para 4, bullet 1:
  //   "A conversion that is not a conversion of a pointer, or pointer
  //    to member, to bool is better than another conversion that is
  //    such a conversion."
  {
    bool L = convertsPtrToBool(leftSrc.type, leftDest);
    bool R = convertsPtrToBool(rightSrc.type, rightDest);
    if (!L && R) return -1;
    if (!R && L) return +1;
  }

  // hierarchy
  // -------------
  //   void           treated as a semantic super-root for this analysis
  //     \            .
  //      A           syntactic root, i.e. least-derived class of {A,B,C}
  //       \          .
  //        B         .
  //         \        .
  //          C       most-derived class of {A,B,C}
  //
  // (the analysis does allow for classes to appear in between these three)

  // 13.3.3.2 para 4, bullet 2:
  //   B* -> A*      is better than  B* -> void*
  //   A* -> void*   is better than  B* -> void*
  // 13.3.3.2 para 4, bullet 3:
  //   C* -> B*      is better than  C* -> A*
  //   C& -> B&      is better than  C& -> A&
  //   B::* <- A::*  is better than  C::* <- A::*
  //   C -> B        is better than  C -> A
  //   B* -> A*      is better than  C* -> A*
  //   B& -> A&      is better than  C& -> A&
  //   C::* <- B::*  is better than  C::* <- A::*
  //   B -> A        is better than  C -> A
  //
  // Q: what about cv flags?  for now I ignore them...
  {
    // first pass:  pointers, and references to pointers
    // second pass: objects, and references to objects
    // third pass:  pointers to members
    for (int pass=1; pass <= 3; pass++) {
      bool (*checkFunc)(Type const *type, CompoundType const *&ct) =
        pass==1 ? &isPointerToCompound   :
        pass==2 ? &isReferenceToCompound :
                  &isPointerToCompoundMember;

      // We're comparing conversions among pointers and references.
      // Name the participating compound types according to this scheme:
      //   left:  LS -> LD      (left source, left dest)
      //   right: RS -> RD
      CompoundType const *LS;
      CompoundType const *LD;
      CompoundType const *RS;
      CompoundType const *RD;

      // are the conversions of the right form?
      if (checkFunc(leftSrc.type, LS) &&
          checkFunc(leftDest, LD) &&
          checkFunc(rightSrc.type, RS) &&
          checkFunc(rightDest, RD)) {
        // in pass 3, the paths go the opposite way, so just swap their ends
        if (pass==3) {
          swap(LS, LD);
          swap(RS, RD);
        }

        // each of the "better than" checks above is really saying
        // that if the paths between source and destination are
        // in the "proper subpath" relation, then the shorter one is better
        if (isProperSubpath(LS, LD, RS, RD)) return -1;
        if (isProperSubpath(RS, RD, LS, LD)) return +1;
      }
    }
  }

  // 13.3.3.2 para 3, bullet 1, sub-bullets 3 and 4:
  // if the conversions yield types that differ only in cv-qualification,
  // then prefer the one with fewer such qualifiers (if one has fewer)
  {
    // preference so far
    int ret = 0;

    // will work through the type constructors simultaneously
    Type const *L = leftDest;
    Type const *R = rightDest;
    
    // 2005-08-09 (in/t0530.cc): the very first cv-flags are
    // irrelevant, because they come from parameter types, which are
    // not part of the function type and therefore do not affect
    // overload resolution
    int skipCVs = 1;

    // 2005-02-23: (in/t0395.cc) if 'L' and 'R' are pointers (either
    // one is sufficient), then the comparison of this section requires
    // that the conversions *differ* in group 3, otherwise they are
    // indistinguishable
    //
    // 2005-04-15: (in/k0029.cc) it seems I want to regard them as
    // indistinguishable if *neither* involved a qualification conversion
    if (L->isPointerType() || R->isPointerType()) {
      if (!(left & SC_GROUP_3_MASK) &&
          !(right & SC_GROUP_3_MASK)) {
        return 0;
      }
    }

    // if one is a reference and the other is not, I don't see a basis
    // for comparison in cppstd, so I skip the extra reference
    //
    // update: 13.3.3.2b.cc suggests that in fact cppstd intends
    // 'int' and 'int const &' to be indistinguishable, so I *don't*
    // strip extra references
    #if 0   // I think this was wrong
    if (L->isReference() && !R->isReference()) {
      L = L->asRvalC();
    }
    else if (!L->isReference() && R->isReference()) {
      R = R->asRvalC();
    }
    #endif // 0

    // deconstruction loop
    while (!L->isCVAtomicType() && !R->isCVAtomicType()) {
      if (L->getTag() != R->getTag()) {
        return 0;            // different types, can't compare
      }

      switch (L->getTag()) {
        default: xfailure("bad tag");

        case Type::T_POINTER:
        case Type::T_REFERENCE: {
          // assured by non-stackability of references
          xassert(L->isPointerType() == R->isPointerType());

          if (foldNextCVs(ret, L->getCVFlags(), R->getCVFlags(), skipCVs)) {
            return 0;        // not subset, therefore no decision
          }

          L = L->getAtType();
          R = R->getAtType();
          break;
        }

        case Type::T_FUNCTION:
        case Type::T_ARRAY:
          if (L->equals(R)) {
            return ret;      // decision so far is final
          }
          else {
            return 0;        // different types, can't compare
          }

        case Type::T_POINTERTOMEMBER: {
          PointerToMemberType const *lptm = L->asPointerToMemberTypeC();
          PointerToMemberType const *rptm = R->asPointerToMemberTypeC();

          if (foldNextCVs(ret, lptm->cv, rptm->cv, skipCVs)) {
            return 0;        // not subset, therefore no decision
          }

          if (lptm->inClass() != rptm->inClass()) {
            return 0;        // different types, can't compare
          }

          L = lptm->atType;
          R = rptm->atType;
          break;
        }
      }
    }

    if (!L->isCVAtomicType() || !R->isCVAtomicType()) {
      return 0;              // different types, can't compare
    }

    // finally, inspect the leaves
    CVAtomicType const *lat = L->asCVAtomicTypeC();
    CVAtomicType const *rat = R->asCVAtomicTypeC();

    if (foldNextCVs(ret, lat->cv, rat->cv, skipCVs)) {
      return 0;              // not subset, therefore no decision
    }

    if (!lat->atomic->equals(rat->atomic)) {
      return 0;              // different types, can't compare
    }

    // 'ret' is our final decision
    return ret;
  }
}


bool convertsPtrToBool(Type const *src, Type const *dest)
{
  // I believe this test is meant to transcend any reference bindings
  src = src->asRvalC();
  dest = dest->asRvalC();

  if (!dest->isBool()) {
    return false;
  }

  if (src->isPointerType() || src->isPointerToMemberType()) {
    return true;
  }

  // (in/t0526.cc) it seems this also applies to types that get
  // implicitly converted to pointers before being converted to bool
  if (src->isArrayType() || src->isFunctionType()) {
    return true;
  }

  return false;
}


// also allows void*, where 'void' is represented with
// a NULL CompoundType
bool isPointerToCompound(Type const *type, CompoundType const *&ct)
{
  type = type->asRvalC();

  if (type->isPointerType()) {
    type = type->asPointerTypeC()->atType;
    if (type->isCompoundType()) {
      ct = type->asCompoundTypeC();
      return true;
    }
    if (type->isVoid()) {
      ct = NULL;
      return true;
    }
  }

  return false;
}


// allows both C& and C, returning C in 'ct'
bool isReferenceToCompound(Type const *type, CompoundType const *&ct)
{ 
  type = type->asRvalC();

  if (type->isCompoundType()) {
    ct = type->asCompoundTypeC();
    return true;
  }

  return false;
}


bool isPointerToCompoundMember(Type const *type, CompoundType const *&ct)
{
  type = type->asRvalC();

  if (type->isPointerToMemberType()) {
    ct = type->asPointerToMemberTypeC()->inClass();
    return true;
  }

  return false;
}


// is 'low' below 'high' in the inheritance hierarchy?
bool isBelow(CompoundType const *low, CompoundType const *high)
{
  return high==NULL ||
         (low!=NULL && low->hasBaseClass(high));
}


// Is the path through the inheritance hierarchy from LS to LD a
// proper sub-path (paths go up) of that from RS to RD?  In fact we
// also require that one of the two endpoints coincide, since that's
// the form of the rules given in 13.3.3.2 para 4.  Note that NULL is
// the representation of 'void', treated as a superclass of
// everything.
bool isProperSubpath(CompoundType const *LS, CompoundType const *LD,
                     CompoundType const *RS, CompoundType const *RD)
{
  if (LS == RS && LD == RD) return false;         // same path

  if (!isBelow(LS, LD)) return false;             // LS -> LD not a path
  if (!isBelow(RS, RD)) return false;             // RS -> RD not a path

  if (LS == RS && isBelow(LD, RD)) {
    // L and R start at the same place, but left ends lower
    return true;
  }

  if (LD == RD && isBelow(RS, LS)) {
    // L and R end at the same place, but right starts lower
    return true;
  }

  return false;
}


// --------------------- ConversionResolver -----------------------
bool isCompoundType_orConstRefTo(Type const *t)
{
  if (t->isCompoundType()) { return true; }
  
  if (t->isReferenceType()) {
    t = t->asReferenceTypeC()->atType;
    return t->isConst() && t->isCompoundType();
  }
  
  return false;
}

ImplicitConversion getConversionOperator(
  Env &env,
  SourceLoc loc,
  ErrorList * /*nullable*/ errors,
  Type *srcClassType,
  Type *destType
) {
  CompoundType *srcClass = srcClassType->asRval()->asCompoundType();

  // in all cases, there is effectively one argument, the receiver
  // object of type 'srcClass'
  GrowArray<ArgumentInfo> args(1);
  args[0] = ArgumentInfo(SE_NONE, srcClassType);

  OVERLOADINDTRACE("converting " << srcClassType->toString() <<
                   " to " << destType->toString());

  // set up the resolver; since the only argument is the receiver
  // object, user-defined conversions (for the receiver; of course
  // user-defined conversions to the dest type are what are being
  // considered by this function overall) should never enter the
  // picture, but I'll supply OF_NO_USER just to be sure
  OverloadResolver resolver(env, loc, errors, OF_NO_USER,
                            // I assume conversion operators can't
                            // have explicit template arguments
                            NULL,
                            args);

  // get the conversion operators for the source class
  SObjList<Variable> &ops = srcClass->conversionOperators;

  // 13.3.1.4?
  //
  // 10/03/04: Allow conversion to 'T const &' for 'T' a class type
  // as well (in/t0334.cc).
  if (isCompoundType_orConstRefTo(destType)) {
    CompoundType *destCT = destType->asRval()->asCompoundType();

    // Where T is the destination class, "... [conversion operators
    // that] yield a type whose cv-unqualified type is the same as T
    // or is a derived class thereof are candidate functions.
    // Conversion functions that return 'reference to T' return
    // lvalues of type T and are therefore considered to yield T for
    // this process of selecting candidate functions."
    SFOREACH_OBJLIST_NC(Variable, ops, iter) {
      Variable *v = iter.data();
      Type *retType = v->type->asFunctionTypeC()->retType->asRval();
      if (!retType->containsVariables()) {
        // concrete type; easy case
        if (retType->isCompoundType() &&
            retType->asCompoundType()->hasBaseClass(destCT)) {
          // it's a candidate
          resolver.processCandidate(v);
        }
      }
      else {
        // (in/t0566.cc) templatized conversion operator; for now,
        // ignore possibility of using derived class and just do
        // direct matching
        //
        // TODO: accomodate derived-to-base conversion here too
        MType match(env);
        if (match.matchTypeNC(destType->asRval(), retType,
                              MF_MATCH | MF_IGNORE_TOP_CV)) {
          // use the bindings to instantiate the template
          Variable *inst = env.instantiateFunctionTemplate(loc, v, match);
          resolver.processCandidate(inst);
        }
      }
    }
  }

  // 13.3.1.5?
  else if (!destType->isReference()) {
    // candidates added in this case are subject to an additional
    // ranking criteria, namely that the ultimate destination type
    // is significant (13.3.3 para 1 final bullet)
    resolver.finalDestType = destType;

    // Where T is the cv-unqualified destination type,
    // "... [conversion operators that] yield type T or a type that
    // can be converted to type T via a standard conversion sequence
    // (13.3.3.1.1) are candidate functions.  Conversion functions
    // that return a cv-qualified type are considered to yield the
    // cv-unqualified version of that type for this process of
    // selecting candidate functions.  Conversion functions that
    // return 'reference to T' return lvalues of type T and are
    // therefore considered to yield T for this process of selecting
    // candidate functions."
    SFOREACH_OBJLIST_NC(Variable, ops, iter) {
      Variable *v = iter.data();
      Type *retType = v->type->asFunctionType()->retType->asRval();
      if (SC_ERROR!=getStandardConversion(NULL /*errorMsg*/,
            SE_NONE, retType, destType)) {
        // it's a candidate
        resolver.processCandidate(v);
      }
    }
  }

  // must be 13.3.1.6
  else {
    // strip the reference
    Type *underDestType = destType->asRval();

    // Where the destination type is 'cv1 T &', "... [conversion
    // operators that] yield type 'cv2 T2 &', where 'cv1 T' is
    // reference-compatible (8.5.3) with 'cv2 T2', are
    // candidate functions."
    SFOREACH_OBJLIST_NC(Variable, ops, iter) {
      Variable *v = iter.data();
      Type *retType = v->type->asFunctionType()->retType;
      if (retType->isReference()) {
        retType = retType->asRval();     // strip the reference
        if (isReferenceCompatibleWith(underDestType, retType)) {
          // it's a candidate
          resolver.processCandidate(v);
        }
      }
    }
  }

  // pick the winner
  bool wasAmbig;
  Variable *winner = resolver.resolve(wasAmbig);
  
  // return an IC with that winner
  ImplicitConversion ic;
  if (!winner) {
    if (!wasAmbig) {
      return ic;        // is IC_NONE
    }
    else {
      ic.addAmbig();
      return ic;
    }
  }

  // compute the standard conversion that obtains the destination
  // type, starting from what the conversion function yields
  StandardConversion sc = getStandardConversion(
    NULL /*errorMsg*/,
    SE_NONE, winner->type->asFunctionType()->retType,   // conversion source
    destType                                            // conversion dest
  );

  ic.addUserConv(SC_IDENTITY, winner, sc);
  return ic;
}

          

// ------------------ LUB --------------------
static CVFlags unionCV(CVFlags cv1, CVFlags cv2, bool &cvdiffers, bool toplevel)
{
  CVFlags cvu = cv1 | cv2;

  // if underlying cv flags have already differed, then at this
  // level we must have a 'const'
  if (cvdiffers) {
    if (toplevel) {
      // once at toplevel, differences are irrelevant
    }
    else {
      cvu |= CV_CONST;
    }
  }

  // did this level witness a cv difference?
  else if (cvu != cv1 || cvu != cv2) {
    cvdiffers = true;
  }

  return cvu;
}

// must have already established similarity
Type *similarLUB(Env &env, Type *t1, Type *t2, bool &cvdiffers, bool toplevel=false)
{
  // this analysis goes bottom-up, because if there are cv differences
  // at a given level, then all levels above it must have CV_CONST in
  // the LUB (otherwise t1 and t2 wouldn't be able to convert to it)

  switch (t1->getTag()) {
    default: xfailure("bad type code");

    case Type::T_ATOMIC: {
      CVAtomicType *at1 = t1->asCVAtomicType();
      CVAtomicType *at2 = t2->asCVAtomicType();
      CVFlags cvu = unionCV(at1->cv, at2->cv, cvdiffers, toplevel);
      return env.tfac.makeCVAtomicType(at1->atomic, cvu);
    }

    case Type::T_POINTER: {
      PointerType *pt1 = t1->asPointerType();
      PointerType *pt2 = t2->asPointerType();
      Type *under = similarLUB(env, pt1->atType, pt2->atType, cvdiffers);
      CVFlags cvu = unionCV(pt1->cv, pt2->cv, cvdiffers, toplevel);
      return env.tfac.makePointerType(cvu, under);
    }

    case Type::T_REFERENCE: {
      ReferenceType *rt1 = t1->asReferenceType();
      ReferenceType *rt2 = t2->asReferenceType();
      Type *under = similarLUB(env, rt1->atType, rt2->atType, cvdiffers);
      return env.tfac.makeReferenceType(under);
    }

    case Type::T_FUNCTION:
    case Type::T_ARRAY:
      // similarity implies equality, so LUB is t1==t2
      return t1;

    case Type::T_POINTERTOMEMBER: {
      PointerToMemberType *pmt1 = t1->asPointerToMemberType();
      PointerToMemberType *pmt2 = t2->asPointerToMemberType();
      Type *under = similarLUB(env, pmt1->atType, pmt2->atType, cvdiffers);
      CVFlags cvu = unionCV(pmt1->cv, pmt2->cv, cvdiffers, toplevel);
      return env.tfac.makePointerToMemberType(pmt1->inClassNAT, cvu, under);
    }
  }
}

CompoundType *ifPtrToCompound(Type *t)
{
  if (t->isPointer()) {
    PointerType *pt = t->asPointerType();
    if (pt->atType->isCompoundType()) {
      return pt->atType->asCompoundType();
    }
  }
  return NULL;
}

bool isPointerToVoid(Type *t)
{
  return t->isPointerType() &&
         t->getAtType()->isVoid();
}

CompoundType *ifPtrToMember(Type *t)
{
  if (t->isPointerToMemberType()) {
    PointerToMemberType *ptm = t->asPointerToMemberType();
    if (ptm->inClassNAT->isCompoundType()) {
      return ptm->inClassNAT->asCompoundType();
    }
  }
  return NULL;
}
 
// clear any toplevel cv-qualifications
Type *cvUnqualified(Env &env, Type *t)
{
  return env.tfac.setQualifiers(SL_UNKNOWN, CV_NONE, t, NULL /*syntax*/);
}

Type *computeLUB(Env &env, Type *t1, Type *t2, bool &wasAmbig)
{
  wasAmbig = false;

  // check for pointers-to-class first
  {
    CompoundType *ct1 = ifPtrToCompound(t1);
    CompoundType *ct2 = ifPtrToCompound(t2);
    CompoundType *lubCt = NULL;
    if (ct1 && ct2) {
      // get CV under the pointers
      CVFlags cv1 = t1->asPointerType()->atType->getCVFlags();
      CVFlags cv2 = t2->asPointerType()->atType->getCVFlags();

      // union them (LUB in cv lattice)
      CVFlags cvu = cv1 | cv2;

      // find the LUB class, if any
      lubCt = CompoundType::lub(ct1, ct2, wasAmbig);
      Type *lubCtType;
      if (!lubCt) {
        if (wasAmbig) {
          // no unique LUB
          return NULL;
        }
        else {
          // no class is the LUB, so use 'void'
          lubCtType = env.tfac.getSimpleType(ST_VOID, cvu);
        }
      }
      else {
        // Now I want to make the type 'pointer to <cvu> <lubCt>', but
        // I suspect I may frequently be able to re-use t1 or t2.
        // Given the current fact that I don't deallocate types, that
        // should be advantageous when possible.  Also, don't return
        // a type with cv flags, since that messes up the instantiation
        // of patterns.
        if (ct1==lubCt && cv1==cvu && t1->getCVFlags()==CV_NONE) return t1;
        if (ct2==lubCt && cv2==cvu && t2->getCVFlags()==CV_NONE) return t2;

        // make a type from the class
        lubCtType = env.tfac.makeCVAtomicType(lubCt, cvu);
      }

      return env.tfac.makePointerType(CV_NONE, lubCtType);
    }
  }

  // convert ptr-to-non-class to void*?
  if ((isPointerToVoid(t1) && t2->isPointerType()) ||
      (isPointerToVoid(t2) && t1->isPointerType())) {
    // since qualifier conversions can only add qualifiers, the LUB type
    // must be a ptr-to-void with the union of the atType cv flags
    CVFlags cv = t1->getAtType()->getCVFlags() | t2->getAtType()->getCVFlags();
    return env.tfac.makePointerType(CV_NONE,
      env.tfac.getSimpleType(ST_VOID, cv));
  }

  // TODO: I should check for pointer-to-members that are compatible
  // by the existence of a greatest-upper-bound in the class hierarchy,
  // for example:
  //      A   B     .
  //       \ /      .
  //        C       .
  // LUB(int A::*, int B::*) should be int C::*
  //
  // However, that's a bit of a pain to do, since it means maintaining
  // the inverse of the 'hasBaseClass' relationship.  Also, I would not
  // be able to follow the simple pattern used for pointer-to-class,
  // since pointer-to-member can have multilevel cv qualification, so I
  // need to flow into the general cv LUB analysis below.
  //
  // Since this situation should be extremely rare, I won't bother for
  // now.  (See also convertibility.txt.)
  
  // 2005-08-09: I managed to accidentally hack in/t0150.cc so that it
  // exposes the need to at least check for direct descendant
  // relationship with identical types, since GCC and ICC do so.
  {
    CompoundType *ct1 = ifPtrToMember(t1);
    CompoundType *ct2 = ifPtrToMember(t2);
    if (ct1 && ct2 && t1->getAtType()->equals(t2->getAtType())) {
      if (ct1->hasBaseClass(ct2)) {
        return cvUnqualified(env, t1);    // lower in the hierarchy
      }
      if (ct2->hasBaseClass(ct1)) {
        return cvUnqualified(env, t2);
      }
    }
  }

  // ok, inheritance is irrelevant; I need to see if types
  // are "similar" (4.4 para 4)
  if (!t1->equals(t2, MF_SIMILAR)) {
    // not similar to each other, so there's no type that is similar
    // to both (similarity is an equivalence relation)
    return NULL;
  }

  // ok, well, are they equal?  if so, then I don't have to make
  // a new type object; NOTE: this allows identical enum arguments
  // to yield out
  if (t1->equals(t2, MF_IGNORE_TOP_CV)) {
    // use 't1', but make sure we're not returning a cv-qualified type
    return cvUnqualified(env, t1);
  }
  
  // not equal, but they *are* similar, so construct the lub type; for
  // any pair of similar types, there is always a type to which both
  // can be converted
  bool cvdiffers = false;    // no difference recorded yet
  return similarLUB(env, t1, t2, cvdiffers, true /*toplevel*/);
}


void test_computeLUB(Env &env, Type *t1, Type *t2, Type *answer, int code)
{                          
  // compute the LUB
  bool wasAmbig;
  Type *a = computeLUB(env, t1, t2, wasAmbig);

  // did it do what we expected?
  bool ok = false;
  switch (code) {
    default:
      env.error("bad computeLUB code");
      return;

    case 0:
      if (!a && !wasAmbig) {
        ok = true;
      }
      break;

    case 1:
      if (a && a->equals(answer)) {
        ok = true;
      }
      break;

    case 2:
      if (!a && wasAmbig) {
        ok = true;
      }
      break;
  }

  static bool tracing = tracingSys("computeLUB");
  if (!tracing && ok) {
    return;
  }

  // describe the call
  string call = stringc << "LUB(" << t1->toString()
                        << ", " << t2->toString() << ")";

  // expected result
  string expect;
  switch (code) {
    case 0: expect = "fail"; break;
    case 1: expect = stringc << "yield `" << answer->toString() << "'"; break;
    case 2: expect = "fail with an ambiguity"; break;
  }

  // actual result
  string actual;
  if (a) {
    actual = stringc << "yielded `" << a->toString() << "'";
  }
  else if (!wasAmbig) {
    actual = "failed";
  }
  else {
    actual = "failed with an ambiguity";
  }

  if (tracing) {
    trace("computeLUB") << call << ": " << actual << "\n";
  }

  if (!ok) {
    // synthesize complete message
    env.error(stringc
      << "I expected " << call
      << " to " << expect
      << ", but instead it " << actual);
  }
}


// ------------------- InstCandidate ---------------
InstCandidate::InstCandidate(Variable *p)
  : primary(p),
    sargs()
{}

InstCandidate::~InstCandidate()
{}



// ----------------- InstCandidateResolver ---------------
InstCandidateResolver::InstCandidateResolver(Env &e)
  : env(e),
    candidates()
{}

InstCandidateResolver::~InstCandidateResolver()
{}


int InstCandidateResolver::compareCandidates(InstCandidate *left, InstCandidate *right)
{
  Type *leftType = left->primary->type;
  Type *rightType = right->primary->type;

  bool left_ALA = atLeastAsSpecializedAs(env, leftType, rightType);
  bool right_ALA = atLeastAsSpecializedAs(env, rightType, leftType);
  if (left_ALA && !right_ALA) {
    // left is "more specialized"
    return -1;
  }
  else if (!left_ALA && right_ALA) {
    // right is "more specialized"
    return +1;
  }
  else {
    // no decision
    return 0;
  }
}


InstCandidate *InstCandidateResolver::selectBestCandidate()
{
  InstCandidate *dummy = 0;
  return ::selectBestCandidate(*this, dummy);
}


// ----------------- debugging -------------------
int overloadNesting = 0;

ostream &overloadTrace()
{
  ostream &os = trace("overload");
  for (int i=0; i<overloadNesting; i++) {
    os << "  ";
  }
  return os;
}


// EOF
