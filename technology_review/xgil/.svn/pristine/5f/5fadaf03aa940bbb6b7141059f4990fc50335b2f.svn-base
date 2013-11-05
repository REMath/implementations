// mangle.cc
// code for mangle.h
// author: Daniel Wilkerson

#include "mangle.h"     // this module
#include "template.h"   // Type, TemplateInfo, etc.
#include "variable.h"   // Variable
#include "cc_print.h"   // PrintEnv
    


string mangleAtomic(AtomicType const *t)
{
  switch (t->getTag()) {
    default: xfailure("bad tag");

    case AtomicType::T_SIMPLE: {
      SimpleType const *st = t->asSimpleTypeC();
      return simpleTypeName(st->type);
    }

    case AtomicType::T_COMPOUND: {
      CompoundType const *ct = t->asCompoundTypeC();

      stringBuilder sb;

      bool hasParams = ct->templateInfo() && ct->templateInfo()->params.isNotEmpty();
      if (hasParams) {
        sb << mangleTemplateParams(ct->templateInfo()) << " ";
      }

      if (!ct->templateInfo() || hasParams) {
        // only say 'class' if this is like a class definition, or
        // if we're not a template, since template instantiations
        // usually don't include the keyword 'class' (this isn't perfect..
        // I think I need more context)
        sb << CompoundType::keywordName(ct->keyword) << " ";
      }

      // sm: I'm sure this is a bug; the class name is always part
      // of the type...
      // dsw: yup, it was a bug alright
//        if (!(tsf & TTS_CANON)) {
      sb << (ct->name? ct->name : "/*anonymous*/");
//        }

      // template arguments are now in the name
      //if (templateInfo && templateInfo->specialArguments) {
      //  sb << "<" << templateInfo->specialArgumentsRepr << ">";
      //}

      return sb;
    }

    case AtomicType::T_ENUM: {
      EnumType const *et = t->asEnumTypeC(); // unused for the moment

      stringBuilder sb;
      sb << "enum ";
      
      // sm: again, to fail to include the name is a bug
      // dsw: yup
      //if (!(tsf & TTS_CANON)) {
      sb << (et->name? et->name : "/*anonymous*/");
      //}

      return sb;
    }

    case AtomicType::T_TYPEVAR:
      return string("TVAR");      // dsw: my replacement for an actual name
      
    case AtomicType::T_PSEUDOINSTANTIATION:
      // sm: not clear what should happen here; I think in fact
      // that pseudoinstantiations should not be "linker visible"
      // so it won't matter
      return t->toString();
  }
}

                              
// cc_type.cc
string cvToString(CVFlags cv);

string mangle(Type const *t)
{
  // I'm pretty sure that it makes no sense to request a linker
  // visible string (mangled name) for a type that contains template
  // variables
  //
  // update: nope, a complete specialization contains type variables,
  // but I suppose they got resolved as typedefs when the template
  // scope provided binding for them; I'm too tired to think about
  // this so I'll leave it for now; FIX: understand this.
//    xassert(!t->containsVariables());
  if (t->isCVAtomicType()) {
    // special case a single atomic type, so as to avoid
    // printing an extra space
    CVAtomicType const *atomic = t->asCVAtomicTypeC();
    return stringc
      << mangleAtomic(atomic->atomic)
      << cvToString(atomic->cv);
  }
  else {
    return stringc << leftMangle(t) << rightMangle(t);
  }
}


string leftMangle(Type const *t, bool innerParen)
{
  switch (t->getTag()) {
    default: xfailure("bad tag");

    case Type::T_ATOMIC: {
      CVAtomicType const *at = t->asCVAtomicTypeC();

      stringBuilder s;
      s << mangleAtomic(at->atomic);
      s << cvToString(at->cv);

      // this is the only mandatory space in the entire syntax
      // for declarations; it separates the type specifier from
      // the declarator(s)
      s << " ";

      return s;
    }

    case Type::T_POINTER:
    case Type::T_REFERENCE: {
      Type *atType = t->getAtType();
      CVFlags cv = t->getCVFlags();

      stringBuilder s;
      s << leftMangle(atType, false /*innerParen*/);
      if (atType->isFunctionType() ||
          atType->isArrayType()) {
        s << "(";
      }
      s << (t->isPointerType()? "*" : "&");
      if (cv) {
        // 1/03/03: added this space so "Foo * const arf" prints right (t0012.cc)
        s << cvToString(cv) << " ";
      }
      return s;
    }
    
    case Type::T_FUNCTION: {
      FunctionType const *ft = t->asFunctionTypeC();
      
      stringBuilder sb;

      // FIX: FUNC TEMPLATE LOSS
      // template parameters
//        if (ft->templateInfo) {
//          sb << mangleTemplateParams(ft->templateInfo) << " ";
//        }

      // return type and start of enclosing type's description
      if (ft->flags & (/*FF_CONVERSION |*/ FF_CTOR | FF_DTOR)) {
        // don't print the return type, it's implicit

        // 7/18/03: changed so we print ret type for FF_CONVERSION,
        // since otherwise I can't tell what it converts to!
      }
      else {
        sb << leftMangle(ft->retType);
      }

      // NOTE: we do *not* propagate 'innerParen'!
      if (innerParen ||
          true /*(tsf & TTS_CANON)*/         // force innerParen for canonical type names
          ) {
        sb << "(";
      }

      return sb;
    }

    case Type::T_ARRAY: {
      ArrayType const *at = t->asArrayTypeC();
      
      return leftMangle(at->eltType);
    }

    case Type::T_POINTERTOMEMBER: {
      PointerToMemberType const *ptm = t->asPointerToMemberTypeC();

      stringBuilder s;
      s << leftMangle(ptm->atType, false /*innerParen*/);
      s << " ";
      if (ptm->atType->isFunctionType() ||
          ptm->atType->isArrayType()) {
        s << "(";
      }
      
      // sm: the following line fails when the 'inClass' is
      // a type variable
      //s << ptm->inClass()->name << "::*";
      // why was it not always just done like this?
      s << mangleAtomic(ptm->inClassNAT) << "::*";

      s << cvToString(ptm->cv);
      return s;
    }
  }
}


string rightMangle(Type const *t, bool innerParen)
{
  switch (t->getTag()) {
    default: xfailure("bad tag");

    case Type::T_ATOMIC: {
      //CVAtomicType const *at = t->asCVAtomicTypeC();    // unused
      return "";
    }

    case Type::T_POINTER:
    case Type::T_REFERENCE: {
      Type *atType = t->getAtType();

      stringBuilder s;
      if (atType->isFunctionType() ||
          atType->isArrayType()) {
        s << ")";
      }
      s << rightMangle(atType, false /*innerParen*/);
      return s;
    }

    case Type::T_FUNCTION: {
      FunctionType const *ft = t->asFunctionTypeC();

      // cqual qualifiers should not be part of the canonical type
      // (you can't overload functions differing only in their cqual
      // qualifiers), so I do not include the extra hooks for printing
      // such information

      // finish enclosing type
      stringBuilder sb;
      if (innerParen ||
          true /*(tsf & TTS_CANON)*/         // force innerParen for canonical type names
          ) {
        sb << ")";
      }

      // arguments
      sb << "(";
      int ct=0;
      SFOREACH_OBJLIST(Variable, ft->params, iter) {
        ct++;
        if (ft->isMethod() && ct==1) {
          // don't actually print the first parameter;
          // the 'm' stands for nonstatic member function
          // sb << "/""*m: " << iter.data()->type->toString() << " *""/ ";
	  // jk: we need this in order to not have the class name
	  sb << "/""*m*""/ ";
          continue;
        }
        if (ct >= 3 || (!ft->isMethod() && ct>=2)) {
          sb << ", ";
        }
        sb << mangleVariable(iter.data());
      }

      if (ft->acceptsVarargs()) {
        if (ct++ > 0) {
          sb << ", ";
        }
        sb << "...";
      }

      sb << ")";

      // right here is the boundary between what's normally printed
      // by FunctionType::rightStringUpToQualifiers and
      // FunctionType::rightStringAfterQualifiers

      CVFlags cv = ft->getReceiverCV();
      if (cv) {
        sb << " " << ::toString(cv);
      }

      #if 0    // TTS_CANON disables
      // exception specs
      if (exnSpec && !(tsf & TTS_CANON)) {
        sb << " throw(";
        int ct=0;
        SFOREACH_OBJLIST(Type, exnSpec->types, iter) {
          if (ct++ > 0) {
            sb << ", ";
          }
          sb << iter.data()->toString(tsf);
        }
        sb << ")";
      }
      #endif // 0

      // hook for verifier syntax
      //extraRightmostSyntax(sb, tsf);

      // finish up the return type
      sb << rightMangle(ft->retType);

      return sb;
    }

    case Type::T_ARRAY: {
      ArrayType const *at = t->asArrayTypeC();

      stringBuilder sb;

      if (at->hasSize()) {
        sb << "[" << at->size << "]";
      }
      else {
        sb << "[]";
      }

      sb << rightMangle(at->eltType);

      return sb;
    }

    case Type::T_POINTERTOMEMBER: {
      PointerToMemberType const *ptm = t->asPointerToMemberTypeC();

      stringBuilder s;
      if (ptm->atType->isFunctionType() ||
          ptm->atType->isArrayType()) {
        s << ")";
      }
      s << rightMangle(ptm->atType, false /*innerParen*/);
      return s;
    }
  }
}


string mangleVariable(Variable const *v)
{
  stringBuilder sb;
  if (v->type->isTypeVariable()) {
    if (true /*tsf & TTS_CANON*/) {
      sb << "TVAR";
    } else {
      // type variable's name, then the parameter's name
      sb << v->type->asTypeVariable()->name << " " << v->name;
    }
  }
  else {
    sb << mangle(v->type);
  }
  
  #if 0
  if (value && (!(tsf & TTS_CANON))) {
    sb << renderExpressionAsString(" = ", value);
  }    
  #endif // 0

  return sb;
}


string mangleTemplateParams(TemplateInfo const *tp)
{
  stringBuilder sb;
  sb << "template <";
  int ct=0;
  SFOREACH_OBJLIST(Variable, tp->params, iter) {
    Variable const *p = iter.data();
    if (ct++ > 0) {
      sb << ", ";
    }

    if (p->type->isTypeVariable()) {
      sb << "class " << p->type->asTypeVariable()->name;
    }
    else {
      // non-type parameter
      sb << mangleVariable(p);
    }
  }
  sb << ">";
  return sb;
}


void mangleSTemplateArgs(stringBuilder &sb, ObjList<STemplateArgument> const &args)
{
  sb << "<";
  int ct=0;
  FOREACH_OBJLIST(STemplateArgument, args, iter) {
    if (ct++) { sb << ", "; }
    switch(iter.data()->kind) {
    default:
      xfailure("Illegal STemplateArgument::kind");
      break;

    case STemplateArgument::STA_NONE:
      xfailure("STA_NONE should never occur here");
      //          sb << "-NONE"; break;
      break;

    case STemplateArgument::STA_TYPE:
      sb << "TYPE-" << mangle(iter.data()->value.t);
      break;

    case STemplateArgument::STA_INT:
      sb << "INT-" << iter.data()->value.i;
      break;

    case STemplateArgument::STA_ENUMERATOR: // reference to enumerator
    case STemplateArgument::STA_REFERENCE: // reference to global object
    case STemplateArgument::STA_POINTER: // pointer to global object
    case STemplateArgument::STA_MEMBER: // pointer to class member
      // sm: this should be mangling the *name*, not the type!
      sb << "OBJECT-" << mangle(iter.data()->value.v->type);
      break;

    case STemplateArgument::STA_DEPEXPR: { // value-dependent expression
      sb << "DEPEXPR-";
      StringBuilderOutStream out0(sb);
      CodeOutStream codeOut(out0);
      TypePrinterC typePrinter;
      PrintEnv penv(typePrinter, &codeOut);
      iter.data()->value.e->print(penv);
      break;
    }

    case STemplateArgument::STA_TEMPLATE: // template argument (not implemented)
      xfailure("STA_TEMPLATE is not implemented");
      break;

    }
  }
  sb << ">";
}


// EOF
