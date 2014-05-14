// astgen.cc            see license.txt for copyright and terms of use
// program to generate C++ code from an AST specification

#include "agrampar.h"      // readAbstractGrammar
#include "test.h"          // ARGS_MAIN
#include "trace.h"         // TRACE_ARGS
#include "owner.h"         // Owner
#include "ckheap.h"        // checkHeap
#include "strutil.h"       // replace, translate, localTimeString
#include "sobjlist.h"      // SObjList
#include "stringset.h"     // StringSet
#include "srcloc.h"        // SourceLocManager
#include "strtokp.h"       // StrtokParse
#include "exc.h"           // xfatal
#include "strdict.h"       // StringDict

#include <string.h>        // strncmp
#include <ctype.h>         // isalnum

// propertly a member of ListClass below, but I don't like nested
// things
enum ListKind {
  LK_NONE,
  LK_ASTList,
  LK_FakeList,
};

// a product type of the information relevant to a list member of a
// class; used to construct the traverse calls and visitors to the
// fictional list classes
struct ListClass {
  ListKind lkind;
  string classAndMemberName;
  string elementClassName;
  explicit ListClass(ListKind lkind0, rostring classAndMemberName0, rostring elementClassName0)
    : lkind(lkind0)
    , classAndMemberName(classAndMemberName0)
    , elementClassName(elementClassName0)
  {}
  char const * kindName() const;
};

char const * ListClass::kindName() const {
  if (lkind == LK_ASTList) return "ASTList";
  else if (lkind == LK_FakeList) return "FakeList";
  else xfailure("illegal ListKind");
}

// this is the name of the visitor interface class, or ""
// if the user does not want a visitor
string visitorName;
inline bool wantVisitor() { return visitorName.length() != 0; }

// this is the name of the delegator-visitor, or ""
// if the user does not want a delegator-visitor
string dvisitorName;
inline bool wantDVisitor() { return dvisitorName.length() != 0; }

// this is the name of the xml-visitor, or ""
// if the user does not want a delegator-visitor
string xmlVisitorName;
inline bool wantXmlVisitor() { return xmlVisitorName.length() != 0; }

// this is the prefix of the filenames rendered for xml lexing and
// parsing
string xmlParserName;
inline bool wantXmlParser() { return xmlParserName.length() != 0; }

// similar for the modification visitor ("mvisitor")
string mvisitorName;
inline bool wantMVisitor() { return mvisitorName.length() != 0; }

// entire input
ASTSpecFile *wholeAST = NULL;

// list of all TF_classes in the input, useful for certain
// applications which don't care about other forms
SObjList<TF_class> allClasses;

// list of all ASTList "list classes"
StringSet listClassesSet;
ASTList<ListClass> listClasses;

// true if the user wants the xmlPrint stuff
bool wantXMLPrint = false;

// true if the user wants the gdb() functions
bool wantGDB = false;

// true if we should use a hack to work around the absence of
// support for covariant return types in MSVC; see
//   http://support.microsoft.com/kb/240862/EN-US/
// The approach is to use
//   virtual Super *nocvr_clone() const;
//   Sub *clone() const { return static_cast<Sub*>(nocvr_clone()); }
// in place of
//   virtual Sub *clone() const;
bool nocvr = false;


// ------------------ shared gen functions ----------------------
enum TreeNodeKind { TKN_NONE, TKN_SUPERCLASS, TKN_SUBCLASS };

class Gen {
protected:        // data
  string srcFname;                  // name of source file
  ObjList<string> const &modules;   // extension modules
  string destFname;                 // name of output file
  ofstream out;                     // output stream
  ASTSpecFile const &file;          // AST specification

public:           // funcs
  Gen(rostring srcFname, ObjList<string> const &modules,
      rostring destFname, ASTSpecFile const &file);
  ~Gen();

  // shared output sequences
  void headerComments();
  void doNotEdit();
  void emitFiltered(ASTList<Annotation> const &decls, AccessCtl mode,
                    rostring indent);
};


Gen::Gen(rostring srcfn, ObjList<string> const &mods,
         rostring destfn, ASTSpecFile const &f)
  : srcFname(srcfn),
    modules(mods),
    destFname(destfn),
    out(toCStr(destfn)),
    file(f)
{
  if (out.IsError()) {
    throw_XOpen(destfn);
  }
}

Gen::~Gen()
{}


// type queries
TreeNodeKind getTreeNodeKind(rostring type);
TreeNodeKind getTreeNodePtrKind(rostring type);

bool isTreeNode(rostring type)
{ return getTreeNodeKind(type) != TKN_NONE; }
bool isTreeNodePtr(rostring type)
{ return getTreeNodePtrKind(type) != TKN_NONE; }
bool isSuperclassTreeNode(rostring type)
{ return getTreeNodeKind(type) == TKN_SUPERCLASS; }
bool isSuperclassTreeNodePtr(rostring type)
{ return getTreeNodePtrKind(type) == TKN_SUPERCLASS; }
bool isSubclassTreeNode(rostring type)
{ return getTreeNodeKind(type) == TKN_SUBCLASS; }
bool isSubclassTreeNodePtr(rostring type)
{ return getTreeNodePtrKind(type) == TKN_SUBCLASS; }

string extractNodeType(rostring type);
string getSuperTypeOf(rostring sub);

bool isListType(rostring type);
bool isFakeListType(rostring type);
bool isTreeListType(rostring type);
string extractListType(rostring type);


// dsw: I just need to know if the thing is an object or not
bool isPtrKind(rostring type)
{
  return type[strlen(type)-1] == '*';
}


TreeNodeKind getTreeNodePtrKind(rostring type)
{
  if (isPtrKind(type)) {
    // is pointer type; get base type; dsw: FIX: I think this is
    // wrong; you might want to consider the same replacement in other
    // places where trimWhitespace() is used.
//      string base = trimWhitespace(substring(type, strlen(type)-1));
    string base = firstAlphanumToken(substring(type, strlen(type)-1));

    return getTreeNodeKind(base);
  }

  // not a pointer type
  return TKN_NONE;
}


TreeNodeKind getTreeNodeKind(rostring base)
{
  // search among defined classes for this name
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();

    if (c->super->name.equals(base)) {
      // found it in a superclass
      return TKN_SUPERCLASS;
    }

    // check the subclasses
    FOREACH_ASTLIST(ASTClass, c->ctors, ctor) {
      if (ctor.data()->name.equals(base)) {
        // found it in a subclass
        return TKN_SUBCLASS;
      }
    }
  }

  return TKN_NONE;
}


string getSuperTypeOf(rostring sub)
{
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();

    // look among the subclasses
    FOREACH_ASTLIST(ASTClass, c->ctors, ctor) {
      if (ctor.data()->name.equals(sub)) {
        // found it
        return c->super->name;
      }
    }
  }

  xfailure("getSuperTypeOf: invalid subclass name");
  return "";    // silence warning
}


// get just the first alphanumeric word
string extractNodeType(rostring type)
{
  char const *end = toCStr(type);
  while (isalnum(*end) || *end=='_') {
    end++;
  }
  return substring(type, end-toCStr(type));
}


// is this type a use of my ASTList template?
bool isListType(rostring type)
{
  // do a fairly coarse analysis.. (the space before "<" is
  // there because the type string is actually parsed by the
  // grammar, and as it assembles it back into a string it
  // inserts a space after every name-like token)
  return prefixEquals(type, "ASTList <");
}

// similar for FakeList
bool isFakeListType(rostring type)
{
  return prefixEquals(type, "FakeList <");
}

// is it a list type, with the elements being tree nodes?
bool isTreeListType(rostring type)
{
  return isListType(type) && isTreeNode(extractListType(type));
}

// given a type for which 'is[Fake]ListType' returns true, extract
// the type in the template argument angle brackets; this is used
// to get the name of the type so we can pass it to the macros
// which print list contents
string extractListType(rostring type)
{
  xassert(isListType(type) || isFakeListType(type));
  char const *langle = strchr(toCStr(type), '<');
  char const *rangle = strchr(toCStr(type), '>');
  xassert(langle && rangle);
  return trimWhitespace(substring(langle+1, rangle-langle-1));
}


// given a string that comes from a user's declaration of a field
// of a class, extract the type and the name; this assumes that,
// syntactically, they separate cleanly (without the name in the
// middle of the type syntax)
void parseFieldDecl(string &type, string &name, rostring decl)
{
  // it's not trivial to extract the name of the field from
  // its declaration.. so let's use a simple heuristic: it's
  // probably the last sequence of non-whitespace alphanum chars
  StrtokParse tok(decl, " \t*()[]<>,");
  
  // now, find the offset of the start of the last token
  int ofs = tok.offset(tok.tokc()-1);
  
  // extract the parts
  type = trimWhitespace(substring(decl, ofs));
  name = trimWhitespace(toCStr(decl)+ofs);
}

string extractFieldType(rostring decl)
{
  string t, n;
  parseFieldDecl(t, n, decl);
  return t;
}

string extractFieldName(rostring decl)
{
  string t, n;
  parseFieldDecl(t, n, decl);
  return n;
}


// I scatter this throughout the generated code as pervasive
// reminders that these files shouldn't be edited -- I often
// accidentally edit them and then have to backtrack and reapply
// the changes to where they were supposed to go ..
void Gen::doNotEdit()
{
  out << "// *** DO NOT EDIT ***\n";
}


void Gen::headerComments()
{
  out << "// " << sm_basename(destFname) << "\n";
  doNotEdit();
  out << "// generated automatically by astgen, from " << sm_basename(srcFname) << "\n";
  
  if (modules.count()) {
    out << "// active extension modules:";
    FOREACH_OBJLIST(string, modules, iter) {
      out << " " << *(iter.data());
    }
    out << "\n";
  }

  // the inclusion of the date introduces gratuitous changes when the
  // tool is re-run for whatever reason
  //out << "//   on " << localTimeString() << "\n";
  
  out << "\n";
}


void Gen::emitFiltered(ASTList<Annotation> const &decls, AccessCtl mode,
                       rostring indent)
{
  FOREACH_ASTLIST(Annotation, decls, iter) {
    if (iter.data()->kind() == Annotation::USERDECL) {
      UserDecl const &decl = *( iter.data()->asUserDeclC() );
      if (decl.access() == mode) {
        out << indent << decl.code << ";\n";
      }                                                     
    }
  }
}


// ------------------ generation of the header -----------------------
// translation-wide state
class HGen : public Gen {
private:        // funcs
  void emitVerbatim(TF_verbatim const &v);
  void emitTFClass(TF_class const &cls);
  void emitBaseClassDecls(ASTClass const &cls, int ct);
  static char const *virtualIfChildren(TF_class const &cls);
  void emitCtorFields(ASTList<CtorArg> const &args,
                      ASTList<CtorArg> const &lastArgs);
  void innerEmitCtorFields(ASTList<CtorArg> const &args);
  void emitCtorFormal(int &ct, CtorArg const *arg);
  void emitCtorFormals(int &ct, ASTList<CtorArg> const &args);
  void emitCtorDefn(ASTClass const &cls, ASTClass const *parent);
  void passParentCtorArgs(int &ct, ASTList<CtorArg> const &args);
  void initializeMyCtorArgs(int &ct, ASTList<CtorArg> const &args);
  void emitCommonFuncs(rostring virt);
  void emitUserDecls(ASTList<Annotation> const &decls);
  void emitCtor(ASTClass const &ctor, ASTClass const &parent);

  void emitVisitorInterfacePrelude(rostring visitorName);
  void emitVisitorInterface();
  void emitDVisitorInterface();
  void emitXmlVisitorInterface();
  void emitMVisitorInterface();

public:         // funcs
  HGen(rostring srcFname, ObjList<string> const &modules,
       rostring destFname, ASTSpecFile const &file)
    : Gen(srcFname, modules, destFname, file)
  {}
  void emitFile();
};


// emit header code for an entire AST spec file
void HGen::emitFile()
{
  string includeLatch = translate(sm_basename(destFname), "a-z.", "A-Z_");

  headerComments();

  out << "#ifndef " << includeLatch << "\n";
  out << "#define " << includeLatch << "\n";
  out << "\n";
  out << "#include \"asthelp.h\"        // helpers for generated code\n";
  if (wantDVisitor()) {
    out << "#include \"sobjset.h\"        // SObjSet\n";
  }
  out << "\n";

  // forward-declare all the classes
  out << "// fwd decls\n";
  FOREACH_ASTLIST(ToplevelForm, file.forms, form) {
    TF_class const *c = form.data()->ifTF_classC();
    if (c) {
      out << "class " << c->super->name << ";\n";

      FOREACH_ASTLIST(ASTClass, c->ctors, ctor) {
        out << "class " << ctor.data()->name << ";\n";
      }
    }
  }
  out << "\n\n";

  if (wantVisitor()) {
    out << "// visitor interface class\n"
        << "class " << visitorName << ";\n\n";
  }
  if (wantDVisitor()) {
    // dsw: this seems necessary and here seems as good a place as any
    // to do it
    if (!wantVisitor()) {
      xfatal("If you specify the 'dvisitor' option, you must also specify the 'visitor' option");
    }
    out << "// delegator-visitor interface class\n"
        << "class " << dvisitorName << ";\n\n";
  }
  if (wantXmlVisitor()) {
    // dsw: this seems necessary and here seems as good a place as any
    // to do it
    if (!wantVisitor()) {
      xfatal("If you specify the 'xmlVisitor' option, you must also specify the 'visitor' option");
    }
    out << "// xml-visitor interface class\n"
        << "class " << xmlVisitorName << ";\n\n";
  }
  if (wantMVisitor()) {
    out << "class " << mvisitorName << ";\n\n";
  }

  // do all the enums first; this became necessary when I had an
  // enum in an extension, since the use of the enum ended up
  // before the enum itself, due to the use being in a class that
  // was defined in the base module          
  {
    FOREACH_ASTLIST(ToplevelForm, file.forms, form) {
      if (form.data()->isTF_enum()) {
        TF_enum const *e = form.data()->asTF_enumC();
        out << "enum " << e->name << " {\n";
        FOREACH_ASTLIST(string, e->enumerators, iter) {
          out << "  " << *(iter.data()) << ",\n";
        }
        out << "};\n"
            << "\n"
            << "char const *toString(" << e->name << ");\n"
            << "\n"
            << "\n"
            ;
      }
    }
  }

  // process each (non-enum) directive
  FOREACH_ASTLIST(ToplevelForm, file.forms, form) {
    switch (form.data()->kind()) {
      case ToplevelForm::TF_VERBATIM:
        emitVerbatim(*( form.data()->asTF_verbatimC() ));
        break;

      case ToplevelForm::TF_IMPL_VERBATIM:
        // nop
        break;

      case ToplevelForm::TF_CLASS:
        emitTFClass(*( form.data()->asTF_classC() ));
        break;

      default:
        // ignore other toplevel forms (e.g. TF_option)
        break;
    }

    out << "\n";
  }

  if (wantVisitor()) {
    emitVisitorInterface();
  }
  if (wantDVisitor()) {
    emitDVisitorInterface();
  }
  if (wantXmlVisitor()) {
    emitXmlVisitorInterface();
  }
  if (wantMVisitor()) {
    emitMVisitorInterface();
  }

  out << "#endif // " << includeLatch << "\n";
}


// emit a verbatim section
void HGen::emitVerbatim(TF_verbatim const &v)
{
  doNotEdit();
  out << v.code;
}


STATICDEF char const *HGen::virtualIfChildren(TF_class const &cls)
{
  if (cls.hasChildren()) {
    // since this class has children, make certain functions virtual
    return "virtual ";
  }
  else {
    // no children, no need to introduce a vtable
    return "";
  }
}


// emit declaration for a class ("phylum")
void HGen::emitTFClass(TF_class const &cls)
{
  doNotEdit();
  out << "class " << cls.super->name;
  emitBaseClassDecls(*(cls.super), 0 /*ct*/);
  out << " {\n";

  // the xml visitor needs to be able to see the internals of the
  // classes
  if (wantXmlVisitor()) {
    out << "  friend class " << xmlVisitorName << ";\n";
    out << "  friend class ASTXmlReader;\n";
  }

  emitCtorFields(cls.super->args, cls.super->lastArgs);
  emitCtorDefn(*(cls.super), NULL /*parent*/);

  // destructor
  char const *virt = virtualIfChildren(cls);
  out << "  " << virt << "~" << cls.super->name << "();\n";
  out << "\n";

  // declare the child kind selector
  if (cls.hasChildren()) {
    out << "  enum Kind { ";
    FOREACH_ASTLIST(ASTClass, cls.ctors, ctor) {
      out << ctor.data()->classKindName() << ", ";
    }
    out << "NUM_KINDS };\n";

    out << "  virtual Kind kind() const = 0;\n";
    out << "\n";
    out << "  static char const * const kindNames[NUM_KINDS];\n";
    out << "  char const *kindName() const { return kindNames[kind()]; }\n";
    out << "\n";
  }
  else {
    // even if the phylum doesn't have children, it's nice to be able
    // to ask an AST node for its name (e.g. in templatized code that
    // deals with arbitrary AST node types), so define the
    // 'kindName()' method anyway
    out << "  char const *kindName() const { return \"" << cls.super->name << "\"; }\n";
  }

  // declare checked downcast functions
  {
    FOREACH_ASTLIST(ASTClass, cls.ctors, ctor) {
      // declare the const downcast
      ASTClass const &c = *(ctor.data());
      out << "  DECL_AST_DOWNCASTS(" << c.name << ", " << c.classKindName() << ")\n";
    }
    out << "\n";
  }

  // declare clone function
  if (cls.hasChildren()) {
    if (!nocvr) {
      // normal case
      out << "  virtual " << cls.super->name << "* clone() const=0;\n";
    }
    else {
      // msvc hack case
      out << "  virtual " << cls.super->name << "* nocvr_clone() const=0;\n";
      out << "  " << cls.super->name << "* clone() const { return nocvr_clone(); }\n";
    }
  }
  else {
    // not pure or virtual
    out << "  " << cls.super->name << " *clone() const;\n";
  }
  out << "\n";

  emitCommonFuncs(virt);

  if (wantGDB) {
    out << "  void gdb() const;\n\n";
  }

  emitUserDecls(cls.super->decls);

  // close the declaration of the parent class
  out << "};\n";
  out << "\n";

  // print declarations for all child classes
  {
    FOREACH_ASTLIST(ASTClass, cls.ctors, ctor) {
      emitCtor(*(ctor.data()), *(cls.super));
    }
  }

  out << "\n";
}


void HGen::emitBaseClassDecls(ASTClass const &cls, int ct)
{
  FOREACH_ASTLIST(BaseClass, cls.bases, iter) {
    out << ((ct++ > 0)? ", " : " : ")
        << toString(iter.data()->access) << " "
        << iter.data()->name
        ;
  }
}


// emit data fields implied by the constructor
void HGen::emitCtorFields(ASTList<CtorArg> const &args,
                          ASTList<CtorArg> const &lastArgs)
{
  out << "public:      // data\n";
  innerEmitCtorFields(args);
  innerEmitCtorFields(lastArgs);
  out << "\n";
}

void HGen::innerEmitCtorFields(ASTList<CtorArg> const &args)
{
  // go over the arguments in the ctor and declare fields for them
  {
    FOREACH_ASTLIST(CtorArg, args, arg) {
      char const *star = "";
      if (isTreeNode(arg.data()->type)) {
        // make it a pointer in the concrete representation
        star = "*";
      }

      out << "  " << arg.data()->type << " " << star << arg.data()->name << ";\n";
    }
  }
}


// emit the declaration of a formal argument to a constructor
void HGen::emitCtorFormal(int &ct, CtorArg const *arg)
{
  // put commas between formals
  if (ct++ > 0) {
    out << ", ";
  }

  string const &type = arg->type;
  out << type << " ";
  if (isListType(type) ||
      isTreeNode(type) ||
      type.equals("LocString")) {
    // lists and subtrees and LocStrings are constructed by passing pointers
    trace("putStar") << "putting star for " << type << endl;
    out << "*";
  }
  else {
    trace("putStar") << "NOT putting star for " << type << endl;
  }

  out << "_" << arg->name;      // prepend underscore to param's name

  // emit default value, if any
  if (arg->defaultValue.length() > 0) {
    out << " = " << arg->defaultValue;
  }
}

void HGen::emitCtorFormals(int &ct, ASTList<CtorArg> const &args)
{
  FOREACH_ASTLIST(CtorArg, args, arg) {
    emitCtorFormal(ct, arg.data());
  }
}

 
// true if 'ud' seems to declare a function, as opposed to data
bool isFuncDecl(UserDecl const *ud)
{
  return ud->amod->hasMod("virtual") ||
         ud->amod->hasMod("func");
}

// emit the definition of the constructor itself
void HGen::emitCtorDefn(ASTClass const &cls, ASTClass const *parent)
{
  // declare the constructor
  {
    out << "public:      // funcs\n";
    out << "  " << cls.name << "(";

    // list of formal parameters to the constructor
    {
      int ct = 0;
      if (parent) {
        emitCtorFormals(ct, parent->args);
      }
      emitCtorFormals(ct, cls.args);
      emitCtorFormals(ct, cls.lastArgs);
      if (parent) {
        emitCtorFormals(ct, parent->lastArgs);
      }
    }
    out << ")";

    // pass args to superclass, and initialize fields
    {
      int ct = 0;

      if (parent) {
        out << " : " << parent->name << "(";
        passParentCtorArgs(ct, parent->args);
        passParentCtorArgs(ct, parent->lastArgs);
        ct++;     // make sure we print a comma, below
        out << ")";
      }

      initializeMyCtorArgs(ct, cls.args);
      initializeMyCtorArgs(ct, cls.lastArgs);

      // initialize fields that have initializers
      FOREACH_ASTLIST(Annotation, cls.decls, ann) {
        if (!ann.data()->isUserDecl()) continue;
        UserDecl const *ud = ann.data()->asUserDeclC();
        if (ud->init.length() == 0) continue;
        if (isFuncDecl(ud)) continue;       // don't do this for functions!

        if (ct++ > 0) {
          out << ", ";
        }
        else {
          out << " : ";
        }

        out << extractFieldName(ud->code) << "(" << ud->init << ")";
      }
    }

    // insert user's ctor code
    out << " {\n";
    emitFiltered(cls.decls, AC_CTOR, "    ");
    out << "  }\n";
  }
}

void HGen::passParentCtorArgs(int &ct, ASTList<CtorArg> const &args)
{
  FOREACH_ASTLIST(CtorArg, args, parg) {
    if (ct++ > 0) {
      out << ", ";
    }
    // pass the formal arg to the parent ctor
    out << "_" << parg.data()->name;
  }
}

void HGen::initializeMyCtorArgs(int &ct, ASTList<CtorArg> const &args)
{
  FOREACH_ASTLIST(CtorArg, args, arg) {
    if (ct++ > 0) {
      out << ", ";
    }
    else {
      out << " : ";    // only used when 'parent' is NULL
    }

    // initialize the field with the formal argument
    out << arg.data()->name << "(_" << arg.data()->name << ")";
  }
}

// emit functions that are declared in every tree node
void HGen::emitCommonFuncs(rostring virt)
{
  // declare the functions they all have
  out << "  " << virt << "void debugPrint(ostream &os, int indent, char const *subtreeName = \"tree\") const;\n";
  if (wantXMLPrint) {
    out << "  " << virt << "void xmlPrint(ostream &os, int indent) const;\n";
  }

  if (wantVisitor()) {
    // visitor traversal entry point
    out << "  " << virt << "void traverse(" << visitorName << " &vis);\n";
  }

  out << "\n";
}

// emit user-supplied declarations
void HGen::emitUserDecls(ASTList<Annotation> const &decls)
{
  FOREACH_ASTLIST(Annotation, decls, iter) {
    // in the header, we only look at userdecl annotations
    if (iter.data()->kind() == Annotation::USERDECL) {
      UserDecl const &decl = *( iter.data()->asUserDeclC() );
      if (decl.access() == AC_PUBLIC ||
          decl.access() == AC_PRIVATE ||
          decl.access() == AC_PROTECTED) {
        out << "  " << toString(decl.access()) << ": ";

        if (decl.amod->hasMod("virtual")) {
          out << "virtual ";
        }
        out << decl.code;

        if (isFuncDecl(&decl) && decl.init.length() > 0) {
          out << " = " << decl.init;     // the "=0" of a pure virtual function
        }
        out << ";";

        // emit field flags as comments, to help debug astgen
        if (decl.amod->mods.count()) {
          out << "   //";
          FOREACH_ASTLIST(string, decl.amod->mods, mod) {
            out << " " << *(mod.data());
          }
        }
        out << "\n";
      }
      if (decl.access() == AC_PUREVIRT) {
        // this is the parent class: declare it pure virtual
        out << "  public: virtual " << decl.code << "=0;\n";
      }
    }
  }
}

// emit declaration for a specific class instance constructor
void HGen::emitCtor(ASTClass const &ctor, ASTClass const &parent)
{
  out << "class " << ctor.name << " : public " << parent.name;
  emitBaseClassDecls(ctor, 1 /*ct*/);
  out << " {\n";

  emitCtorFields(ctor.args, ctor.lastArgs);
  emitCtorDefn(ctor, &parent);

  // destructor
  out << "  virtual ~" << ctor.name << "();\n";
  out << "\n";

  // type tag
  out << "  virtual Kind kind() const { return " << ctor.classKindName() << "; }\n";
  out << "  enum { TYPE_TAG = " << ctor.classKindName() << " };\n";
  out << "\n";

  // common functions
  emitCommonFuncs("virtual ");

  // clone function (take advantage of covariant return types)
  if (!nocvr) {
    // normal case
    out << "  virtual " << ctor.name << " *clone() const;\n";
  }
  else {
    // msvc hack case
    out << "  virtual " << parent.name << "* nocvr_clone() const;\n";
    out << "  " << ctor.name << "* clone() const\n"
        << "    { return static_cast<" << ctor.name << "*>(nocvr_clone()); }\n";
  }

  out << "\n";
  emitUserDecls(ctor.decls);

  // emit implementation declarations for parent's pure virtuals
  FOREACH_ASTLIST(Annotation, parent.decls, iter) {
    UserDecl const *decl = iter.data()->ifUserDeclC();
    if (!decl) continue;

    if (decl->access() == AC_PUREVIRT) {
      out << "  public: virtual " << decl->code << ";\n";
    }
    else if (decl->amod->hasMod("virtual")) {
      out << "  " << toString(decl->access())
          << ": virtual " << decl->code << ";\n";
    }
  }

  // close the decl
  out << "};\n";
  out << "\n";
}


// --------------------- generation of C++ code file --------------------------
class CGen : public Gen {
public:
  string hdrFname;      // name of associated .h file

public:
  CGen(rostring srcFname, ObjList<string> const &modules,
       rostring destFname, ASTSpecFile const &file,
       rostring hdr)
    : Gen(srcFname, modules, destFname, file),
      hdrFname(hdr)
  {}

  void emitFile();
  void emitTFClass(TF_class const &cls);
  void emitDestructor(ASTClass const &cls);
  void emitDestroyField(bool isOwner, rostring type, rostring name);
  void emitPrintCtorArgs(ASTList<CtorArg> const &args);
  void emitPrintFields(ASTList<Annotation> const &decls);
  void emitPrintField(rostring print,
                      bool isOwner, rostring type, rostring name);

  void emitXmlPrintCtorArgs(ASTList<CtorArg> const &args);
  bool emitCustomCode(ASTList<Annotation> const &list, rostring tag);

  void emitCloneCtorArg(CtorArg const *arg, int &ct);
  void emitCloneCtorArgs(int &ct, ASTList<CtorArg> const &args);
  void emitCloneCode(ASTClass const *super, ASTClass const *sub);

  void emitVisitorImplementation();

  private:
  void emitDVisitorImplVisitedCheck(char const *name);
  public:
  void emitDVisitorImplementation();

  private:
  void emitXmlCtorArgs(ASTList<CtorArg> const &args, char const *baseName, string const &className);
  void emitXmlFields(ASTList<Annotation> const &decls, char const *baseName, string const &className);
  void emitXmlField(rostring type, rostring name, char const *baseName,
                    string const &className, AccessMod *amod);
  void emitXmlVisitorImplVisitedCheck(char const *name);
  public:
  void emitXmlVisitorImplementation();

  void emitTraverse(ASTClass const *c, ASTClass const * /*nullable*/ super,
                    bool hasChildren);
  private:
  void emitOneTraverseCall(rostring className, string name, string type);

  public:
  void emitMVisitorImplementation();
  void emitMTraverse(ASTClass const *c, rostring obj, rostring ident);
  void emitMTraverseCall(rostring i, rostring eltType, rostring argVar);
};


// generation of xml parser
class XmlParserGen {
  StringSet attributeNames;     // names of attributes of AST nodes

  ofstream tokensOutH;
  ofstream tokensOutCC;
  ofstream lexerOut;

  ofstream parser0_decls;
  ofstream parser1_defs;
  ofstream parser2_ctorCalls;
  ofstream parser3_registerCalls;

  public:
  XmlParserGen(string &xmlParserName)
    : tokensOutH(stringc << xmlParserName << "_tokens1_mid.gen.h")
    , tokensOutCC(stringc << xmlParserName << "_lexer1_mid.gen.cc")
    , lexerOut(stringc << xmlParserName << "_lexer1_mid.gen.lex")

    , parser0_decls(stringc << xmlParserName << "_parse1_0decl.gen.cc")
    , parser1_defs (stringc << xmlParserName << "_parse1_1defn.gen.cc")
    , parser2_ctorCalls    (stringc << xmlParserName << "_parse1_2ctrc.gen.cc")
    , parser3_registerCalls(stringc << xmlParserName << "_parse1_3regc.gen.cc")
  {}

  private:
  void collectXmlParserCtorArgs(ASTList<CtorArg> const &args, char const *baseName);
  void collectXmlParserFields(ASTList<Annotation> const &decls, char const *baseName);
  void collectXmlParserField
    (rostring type, rostring name, char const *baseName, AccessMod *amod);

  void emitXmlCtorArgs_AttributeParseRule(ASTList<CtorArg> const &args, string &baseName);
  void emitXmlFields_AttributeParseRule(ASTList<Annotation> const &decls, string &baseName);
  void emitXmlField_AttributeParseRule
    (rostring type, rostring name, string &baseName, AccessMod *amod);

  void emitXmlParser_objCtorArgs
    (ASTList<CtorArg> const &args, bool &firstTime);

  void emitXmlParser_Node
    (ASTClass const *clazz,
     ASTList<CtorArg> const *args,
     ASTList<Annotation> const *decls,
     ASTList<CtorArg> const *lastArgs,
     ASTList<CtorArg> const *childArgs = NULL,
     ASTList<Annotation> const *childDecls = NULL);
  void emitXmlParser_Node_registerAttr
    (ASTClass const *clazz,
     ASTList<CtorArg> const *args,
     ASTList<Annotation> const *decls,
     ASTList<CtorArg> const *lastArgs,
     ASTList<CtorArg> const *childArgs = NULL,
     ASTList<Annotation> const *childDecls = NULL);
  void emitXmlParser_ASTList(ListClass const *type);
//    void emitXmlParser_FakeList(ListClass const *type);

  public:
  void emitXmlParserImplementation();
};


void CGen::emitFile()
{
  headerComments();

  out << "#include \"" << hdrFname << "\"      // this module\n";
  if (wantXmlVisitor()) {
    out << "#include \"strutil.h\"      // quoted, parseQuotedString\n";
    out << "#include \"xmlhelp.h\"      // to/fromXml_bool/int\n";
  }
  out << "\n";
  out << "\n";

  FOREACH_ASTLIST(ToplevelForm, file.forms, form) {
    ASTSWITCHC(ToplevelForm, form.data()) {
      //ASTCASEC(TF_verbatim, v) {
      //  // nop
      //}
      ASTCASEC(TF_impl_verbatim, v) {
        doNotEdit();
        out << v->code;
      }
      ASTNEXTC(TF_class, c) {
        emitTFClass(*c);
      }
      ASTNEXTC(TF_enum, e) {
        out << "char const *toString(" << e->name << " x)\n"
            << "{\n"
            << "  static char const * const map[] = {\n";
        FOREACH_ASTLIST(string, e->enumerators, iter) {
          out << "    \"" << *(iter.data()) << "\",\n";
        }     
        out << "  };\n"
            << "  xassert((unsigned)x < TABLESIZE(map));\n"
            << "  return map[x];\n"
            << "};\n"
            << "\n"
            << "\n"
            ;
        break;
      }
      ASTENDCASECD
    }
  }
  out << "\n\n";

  if (wantVisitor()) {
    emitVisitorImplementation();
  }
  if (wantDVisitor()) {
    emitDVisitorImplementation();
  }
  if (wantXmlVisitor()) {
    emitXmlVisitorImplementation();
  }
  if (wantMVisitor()) {
    emitMVisitorImplementation();
  }
}


void CGen::emitTFClass(TF_class const &cls)
{
  out << "// ------------------ " << cls.super->name << " -------------------\n";
  doNotEdit();

  // class destructor
  emitDestructor(*(cls.super));

  // kind name map
  if (cls.hasChildren()) {
    out << "char const * const " << cls.super->name << "::kindNames["
        <<   cls.super->name << "::NUM_KINDS] = {\n";
    FOREACH_ASTLIST(ASTClass, cls.ctors, ctor) {
      out << "  \"" << ctor.data()->name << "\",\n";
    }
    out << "};\n";
    out << "\n";
  }


  // debugPrint
  out << "void " << cls.super->name << "::debugPrint(ostream &os, int indent, char const *subtreeName) const\n";
  out << "{\n";
  if (!cls.hasChildren()) {
    // childless superclasses get the preempt in the superclass;
    // otherwise it goes into the child classes
    emitCustomCode(cls.super->decls, "preemptDebugPrint");

    // childless superclasses print headers; otherwise the subclass
    // prints the header
    out << "  PRINT_HEADER(subtreeName, " << cls.super->name << ");\n";
    out << "\n";
  }

  // 10/31/01: decided I wanted custom debug print first, since it's
  // often much shorter (and more important) than the subtrees
  emitCustomCode(cls.super->decls, "debugPrint");
  emitPrintCtorArgs(cls.super->args);
  if (cls.super->lastArgs.isNotEmpty()) {
    out << "  // (lastArgs are printed by subclasses)\n";
  }
  emitPrintFields(cls.super->decls);

  out << "}\n";
  out << "\n";

  // gdb()
  if (wantGDB) {
    out << "void " << cls.super->name << "::gdb() const\n"
        << "  { debugPrint(cout, 0); }\n"
        << "\n"
        ;
  }

  // dsw: xmlPrint
  if (wantXMLPrint) {
    out << "void " << cls.super->name << "::xmlPrint(ostream &os, int indent) const\n";
    out << "{\n";
    if (!cls.hasChildren()) {
      // dsw: Haven't figured out what this subsection means yet.
//        // childless superclasses get the preempt in the superclass;
//        // otherwise it goes into the child classes
//        emitCustomCode(cls.super->decls, "preemptDebugPrint");

//        // childless superclasses print headers; otherwise the subclass
//        // prints the header
      out << "  XMLPRINT_HEADER(" << cls.super->name << ");\n";
      out << "\n";
    }

    // dsw: This must be in case the client .ast code overrides it.
    // 10/31/01: decided I wanted custom debug print first, since it's
    // often much shorter (and more important) than the subtrees
//      emitCustomCode(cls.super->decls, "xmlPrint");
    emitXmlPrintCtorArgs(cls.super->args);

    if (!cls.hasChildren()) {
      out << "  XMLPRINT_FOOTER(" << cls.super->name << ");\n";
    }
    out << "}\n";
    out << "\n";
  }


  // clone for childless superclasses
  if (!cls.hasChildren()) {
    emitCloneCode(cls.super, NULL /*sub*/);
  }


  // constructors (class hierarchy children)
  FOREACH_ASTLIST(ASTClass, cls.ctors, ctoriter) {
    ASTClass const &ctor = *(ctoriter.data());

    // downcast function
    out << "DEFN_AST_DOWNCASTS(" << cls.super->name << ", "
                                 << ctor.name << ", "
                                 << ctor.classKindName() << ")\n";
    out << "\n";

    // subclass destructor
    emitDestructor(ctor);

    // subclass debugPrint
    out << "void " << ctor.name << "::debugPrint(ostream &os, int indent, char const *subtreeName) const\n";
    out << "{\n";

    // the debug print preempter is declared in the outer "class",
    // but inserted into the print methods of the inner "constructors"
    emitCustomCode(cls.super->decls, "preemptDebugPrint");

    // do same if it's declared only in the subclass
    emitCustomCode(ctor.decls, "preemptDebugPrint");

    out << "  PRINT_HEADER(subtreeName, " << ctor.name << ");\n";
    out << "\n";

    // call the superclass's fn to get its data members
    out << "  " << cls.super->name << "::debugPrint(os, indent, subtreeName);\n";
    out << "\n";

    emitCustomCode(ctor.decls, "debugPrint");
    emitPrintCtorArgs(ctor.args);
    emitPrintFields(ctor.decls);
    
    // superclass 'last' args come after all subclass things
    emitPrintCtorArgs(cls.super->lastArgs);

    out << "}\n";
    out << "\n";

    if (wantXMLPrint) {
      // subclass xmlPrint
      out << "void " << ctor.name << "::xmlPrint(ostream &os, int indent) const\n";
      out << "{\n";

      // the xml print preempter is declared in the outer "class",
      // but inserted into the print methods of the inner "constructors"
      emitCustomCode(cls.super->decls, "preemptXmlPrint");

      out << "  XMLPRINT_HEADER(" << ctor.name << ");\n";
      out << "\n";

      // call the superclass's fn to get its data members
      out << "  " << cls.super->name << "::xmlPrint(os, indent);\n";
      out << "\n";

      // dsw: I assume this is not vital in the generic case, so I
      // leave it out for now.
//        emitCustomCode(ctor.decls, "xmlPrint");
      emitXmlPrintCtorArgs(ctor.args);
      emitXmlPrintCtorArgs(cls.super->lastArgs);

      // dsw: probably don't need the name; take it out later if not
      out << "  XMLPRINT_FOOTER(" << ctor.name << ");\n";
      out << "\n";

      out << "}\n";
      out << "\n";
    }

    // clone for subclasses
    emitCloneCode(cls.super, &ctor);
  }

  out << "\n";
}


bool CGen::emitCustomCode(ASTList<Annotation> const &list, rostring tag)
{
  bool emitted = false;

  FOREACH_ASTLIST(Annotation, list, iter) {
    CustomCode const *cc = iter.data()->ifCustomCodeC();
    if (cc && cc->qualifier.equals(tag)) {
      out << "  " << cc->code << ";\n";
      emitted = true;

      // conceptually mutable..
      const_cast<bool&>(cc->used) = true;
    }
  }

  return emitted;
}


void CGen::emitDestructor(ASTClass const &cls)
{
  out << cls.name << "::~" << cls.name << "()\n";
  out << "{\n";

  // user's code first
  emitFiltered(cls.decls, AC_DTOR, "  ");
  
  // constructor arguments
  FOREACH_ASTLIST(CtorArg, cls.args, argiter) {
    CtorArg const &arg = *(argiter.data());
    emitDestroyField(arg.isOwner, arg.type, arg.name);
  }
                          
  // owner fields
  FOREACH_ASTLIST(Annotation, cls.decls, iter) {
    if (!iter.data()->isUserDecl()) continue;
    UserDecl const *ud = iter.data()->asUserDeclC();
    if (!ud->amod->hasMod("owner")) continue;

    emitDestroyField(true /*isOwner*/,
                     extractFieldType(ud->code),
                     extractFieldName(ud->code));
  }

  out << "}\n";
  out << "\n";
}

void CGen::emitDestroyField(bool isOwner, rostring type, rostring name)
{
  if (isTreeListType(type)) {
    // explicitly destroy list elements, because it's easy to do, and
    // because if there is a problem, it's much easier to see its
    // role in a debugger backtrace
    out << "  " << name << ".deleteAll();\n";
  }
  else if (isListType(type)) {
    if (streq(extractListType(type), "LocString")) {
      // these are owned even though they aren't actually tree nodes
      out << "  " << name << ".deleteAll();\n";

      // TODO: this analysis is duplicated below, during cloning;
      // the astgen tool should do a better job of encapsulating
      // the relationships (particularly owning/non-owning) between
      // its parts, instead of doing ad-hoc type inspection in random
      // places during emission
    }
    else {
      // we don't own the list elements; it's *essential* to
      // explicitly remove the elements; this is a hack, since the
      // ideal solution is to make a variant of ASTList which is
      // explicitly serf pointers.. the real ASTList doesn't have
      // a removeAll method (since it's an owner list), and rather
      // than corrupting that interface I'll emit the code each time..
      out << "  while (" << name << ".isNotEmpty()) {\n"
          << "    " << name << ".removeFirst();\n"
          << "  }\n";
      //out << "  " << name << ".removeAll();\n";
    }
  }
  else if (isOwner || isTreeNode(type)) {
    out << "  delete " << name << ";\n";
  }
}


void CGen::emitPrintCtorArgs(ASTList<CtorArg> const &args)
{
  FOREACH_ASTLIST(CtorArg, args, argiter) {
    CtorArg const &arg = *(argiter.data());

    emitPrintField("PRINT", arg.isOwner, arg.type, arg.name);
  }
}

void CGen::emitPrintFields(ASTList<Annotation> const &decls)
{
  FOREACH_ASTLIST(Annotation, decls, iter) {
    if (!iter.data()->isUserDecl()) continue;
    UserDecl const *ud = iter.data()->asUserDeclC();
    if (!ud->amod->hasMod("field")) continue;

    emitPrintField("PRINT",
                   ud->amod->hasMod("owner"),
                   extractFieldType(ud->code),
                   extractFieldName(ud->code));
  }
}

void CGen::emitPrintField(rostring print,
                          bool isOwner, rostring type, rostring name)
{
  if (streq(type, "string")) {
    out << "  " << print << "_STRING(" << name << ");\n";
  }
  else if (streq(type, "StringRef")) {
    out << "  " << print << "_CSTRING(" << name << ");\n";
  }
  else if (streq(type, "bool")) {
    out << "  " << print << "_BOOL(" << name << ");\n";
  }
  else if (isListType(type)) {
    // for now, I'll continue to assume that any class that appears
    // in ASTList<> is compatible with the printing regime here
    out << "  " << print << "_LIST(" << extractListType(type) << ", "
        << name << ");\n";
  }
  else if (isFakeListType(type)) {
    // similar printing approach for FakeLists
    out << "  " << print << "_FAKE_LIST(" << extractListType(type) << ", "
        << name << ");\n";
  }
  else if (isTreeNode(type) ||
           (isTreeNodePtr(type) && isOwner)) {
    // don't print subtrees that are possibly shared or circular
    out << "  " << print << "_SUBTREE(" << name << ");\n";
  }
  else {
    // catch-all ..
    out << "  " << print << "_GENERIC(" << name << ");\n";
  }
}


void CGen::emitXmlPrintCtorArgs(ASTList<CtorArg> const &args)
{
  FOREACH_ASTLIST(CtorArg, args, argiter) {
    CtorArg const &arg = *(argiter.data());
    
    emitPrintField("XMLPRINT", arg.isOwner, arg.type, arg.name);
  }
}


void CGen::emitCloneCtorArg(CtorArg const *arg, int &ct)
{
  if (ct++ > 0) {
    out << ",";
  }
  out << "\n    ";

  string argName = arg->name;
  if (argName == "ret") {     
    // avoid clash with local variable name
    argName = "this->ret";                 
    
    // NOTE: I do not simply want to make the local variable name
    // something ugly like __astgen_ret because in the user-defined
    // clone() augmentation functions, the user is supposed to be
    // able to use 'ret' to refer to the tree constructed so far.
  }

  if (isTreeListType(arg->type)) {
    // clone an ASTList of tree nodes
    out << "cloneASTList(" << argName << ")";
  }
  else if (isListType(arg->type)) {
    if (streq(extractListType(arg->type), "LocString")) {
      // these are owned, so clone deeply
      out << "cloneASTList(" << argName << ")";
    }
    else {
      // clone an ASTList of non-tree nodes
      out << "shallowCloneASTList(" << argName << ")";
    }
  }
  else if (isFakeListType(arg->type)) {
    // clone a FakeList (of tree nodes, we assume..)
    out << "cloneFakeList(" << argName << ")";
  }
  else if (isTreeNode(arg->type)) {
    // clone a tree node
    out << argName << "? " << argName << "->clone() : NULL";
  }
  else if (streq(arg->type, "LocString")) {
    // clone a LocString; we store objects, but pass pointers
    out << argName << ".clone()";
  }
  else {
    // pass the non-tree node's value directly
    out << argName;
  }
}

void CGen::emitCloneCtorArgs(int &ct, ASTList<CtorArg> const &args)
{
  FOREACH_ASTLIST(CtorArg, args, iter) {
    emitCloneCtorArg(iter.data(), ct);
  }
}


void CGen::emitCloneCode(ASTClass const *super, ASTClass const *sub)
{
  ASTClass const *myClass = sub? sub : super;
  string const &name = myClass->name;

  if (!nocvr || !sub) {
    // normal case, or childless superclass case
    out << name << " *" << name << "::clone() const\n";
  }
  else {
    // msvc hack case
    out << super->name << " *" << name << "::nocvr_clone() const\n";
  }
  out << "{\n";

  if (!emitCustomCode(myClass->decls, "substituteClone")) {
    out << "  " << name << " *ret = new " << name << "(";

    // clone each of the superclass ctor arguments
    int ct=0;
    emitCloneCtorArgs(ct, super->args);

    // and likewise for the subclass ctor arguments
    if (sub) {
      emitCloneCtorArgs(ct, sub->args);
      emitCloneCtorArgs(ct, sub->lastArgs);
    }

    emitCloneCtorArgs(ct, super->lastArgs);

    out << "\n"
        << "  );\n";

    // custom clone code
    emitCustomCode(super->decls, "clone");
    if (sub) {
      emitCustomCode(sub->decls, "clone");
    }

    out << "  return ret;\n";
  }

  out << "}\n"
      << "\n";
}


// -------------------------- visitor ---------------------------
void emitTF_custom(ofstream &out, rostring qualifierName, bool addNewline)
{
  FOREACH_ASTLIST_NC(ToplevelForm, wholeAST->forms, iter) {
    if (iter.data()->isTF_custom()) {
      CustomCode *cc = iter.data()->asTF_customC()->cust;
      if (cc->qualifier == qualifierName) {
        out << cc->code;
        if (addNewline) {
          out << "\n";
        }
        cc->used = true;
      }
    }
  }
}


void HGen::emitVisitorInterfacePrelude(rostring visitorName)
{
  // custom additions to this visitor
  emitTF_custom(out, visitorName, true /*addNewline*/);

  out << "private:     // disallowed, not implemented\n"
      << "  " << visitorName << "(" << visitorName << "&);\n"
      << "  void operator= (" << visitorName << "&);\n"
      << "\n"
      << "public:      // funcs\n"
      << "  " << visitorName << "() {"
      ;

  // custom additions to the visitor's constructor
  emitTF_custom(out, stringc << visitorName << "_ctor", false /*addNewline*/);

  out << "}\n"
      << "  virtual ~" << visitorName << "();   // silence gcc warning...\n"
      << "\n"
      ;
}

void HGen::emitVisitorInterface()
{
  out << "// the visitor interface class\n"
      << "class " << visitorName << " {\n";
  emitVisitorInterfacePrelude(visitorName);

  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();

    out << "  virtual bool visit" << c->super->name << "("
        <<   c->super->name << " *obj);\n"
        << "  virtual void postvisit" << c->super->name << "("
        <<   c->super->name << " *obj);\n"
        ;
  }

  out << "\n  // List 'classes'\n";
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    out << "  virtual bool visitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">*);\n";
    out << "  virtual void postvisitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">*);\n";
  }

  StringSet listItemClassesSet; // set of list item classes printed so far
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    xassert(!listItemClassesSet.contains(cls->classAndMemberName)); // should not repeat
    listItemClassesSet.add(cls->classAndMemberName);
    out << "  virtual bool visitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << "*);\n";
    out << "  virtual void postvisitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << "*);\n";
  }

  out << "};\n\n";
}


void CGen::emitVisitorImplementation()
{
  out << "// ---------------------- " << visitorName << " ---------------------\n";
  out << "// default no-op visitor\n";
  out << visitorName << "::~" << visitorName << "() {}\n";
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();

    out << "bool " << visitorName << "::visit" << c->super->name << "("
        <<   c->super->name << " *obj) { return true; }\n"
        << "void " << visitorName << "::postvisit" << c->super->name << "("
        <<   c->super->name << " *obj) {}\n";
  }

  out << "\n// List 'classes'\n";
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    out << "bool " << visitorName << "::visitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">*) { return true; }\n";
    out << "void " << visitorName << "::postvisitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">*) {}\n";
  }

  StringSet listItemClassesSet; // set of list item classes printed so far
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    xassert(!listItemClassesSet.contains(cls->classAndMemberName)); // should not repeat
    listItemClassesSet.add(cls->classAndMemberName);
    out << "bool " << visitorName << "::visitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << "*) { return true; }\n";
    out << "void " << visitorName << "::postvisitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << "*) {}\n";
  }

  out << "\n\n";

  // implementations of traversal functions
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();

    // superclass traversal
    emitTraverse(c->super, NULL /*super*/, c->hasChildren());

    // subclass traversal
    FOREACH_ASTLIST(ASTClass, c->ctors, iter) {
      ASTClass const *sub = iter.data();

      emitTraverse(sub, c->super, false /*hasChildren*/);
    }
  }
  out << "\n";
}


void CGen::emitOneTraverseCall(rostring className, string name, string type)
{
  if (isTreeNode(type) || isTreeNodePtr(type)) {
    // traverse it directly
//      cout << "emitOneTraverseCall, name:" << name << ", type: " << type << endl;
    out << "  if (" << name << ") { " << name << "->traverse(vis); }\n";
  }

  else if ((isListType(type) || isFakeListType(type)) &&
           isTreeNode(extractListType(type))) {
    // list of tree nodes: iterate and traverse
    string eltType = extractListType(type);

    // could add an assertion here that the elt type is one of the
    // list types extracted earlier during getListClasses()

    // compute list accessor names
    char const *iterMacroName = "FOREACH_ASTLIST_NC";
    char const *iterElt = ".data()";
    char const *argNamePrefix = "&";
    if (isFakeListType(type)) {
      iterMacroName = "FAKELIST_FOREACH_NC";
      iterElt = "";
      argNamePrefix = "";
    }

    // emit the pre-visit call to the fantasy "list class"
    out << "  if (vis.visitList_" << className << "_" << name
        << "(" << argNamePrefix << name << ")) {\n";
    out << "    " << iterMacroName << "(" << eltType << ", " << name << ", iter) {\n";

    out << "      if (vis.visitListItem_" << className << "_" << name
        << "(iter" << iterElt << ")) {\n";
    out << "        iter" << iterElt << "->traverse(vis);\n";
    out << "        vis.postvisitListItem_" << className << "_" << name
        << "(iter" << iterElt << ");\n";
    out << "      }\n";         // end of if

    out << "    }\n";           // end of iter
    out << "    vis.postvisitList_" << className << "_" << name
        << "(" << argNamePrefix << name << ");\n";
    out << "  }\n";             // end of if
  }
}

void CGen::emitTraverse(ASTClass const *c, ASTClass const * /*nullable*/ super,
                        bool hasChildren)
{
  out << "void " << c->name << "::traverse("
      <<   visitorName << " &vis)\n"
      << "{\n";

  // do any initial traversal action specified by the user
  emitCustomCode(c->decls, "preemptTraverse");

  // name of the 'visit' method that applies to this class;
  // these methods are always named according to the least-derived
  // class in the hierarchy
  string visitName = stringc << "visit" << (super? super : c)->name;

  // we only call 'visit' in the most-derived classes; this of course
  // assumes that classes with children are never themselves instantiated
  if (!hasChildren) {
    // visit this node; if the visitor doesn't want to traverse
    // the children, then bail
    out << "  if (!vis." << visitName << "(this)) { return; }\n\n";
  }
  else {
    out << "  // no 'visit' because it's handled by subclasses\n\n";
  }

  if (super) {
    // traverse superclass ctor args, if this class has one
    out << "  " << super->name << "::traverse(vis);\n"
        << "\n";
  }

  // traverse into the ctor arguments
  FOREACH_ASTLIST(CtorArg, c->args, iter) {
    CtorArg const *arg = iter.data();
    emitOneTraverseCall(c->name, arg->name, arg->type);
  }

  // dsw: I need a way to make fields traversable
  FOREACH_ASTLIST(Annotation, c->decls, iter) {
    if (!iter.data()->isUserDecl()) continue;
    UserDecl const *ud = iter.data()->asUserDeclC();
    if (!ud->amod->hasMod("traverse")) continue;
    emitOneTraverseCall(c->name, extractFieldName(ud->code), extractFieldType(ud->code));
  }

  // do any final traversal action specified by the user
  emitCustomCode(c->decls, "traverse");

  // traverse into the ctor last arguments
  FOREACH_ASTLIST(CtorArg, c->lastArgs, iter) {
    CtorArg const *arg = iter.data();
    emitOneTraverseCall(c->name, arg->name, arg->type);
  }

  if (!hasChildren) {
    // if we did the preorder visit on the way in, do the
    // postorder visit now
    out << "  vis.post" << visitName << "(this);\n";
  }
  else {
    out << "  // no 'postvisit' either\n";
  }

  out << "}\n\n";
}


// ------------------- delegation visitor --------------------
void HGen::emitDVisitorInterface()
{
  out << "// the delegator-visitor interface class\n"
      << "class " << dvisitorName << " : public " << visitorName << " {\n";

  out << "protected:   // data\n";
  out << "  " << visitorName << " *client;      // visitor to delegate to\n";
  out << "  bool ensureOneVisit;                // check for visiting at most once?\n";
  out << "  SObjSet<void*> wasVisitedASTNodes;  // set of visited nodes\n";
  out << "  SObjSet<void*> wasVisitedList_ASTListNodes; // set of visited ASTLists\n";
  out << "  SObjSet<void*> wasVisitedList_FakeListNodes; // set of visited FakeLists\n";
  out << "\n";

  out << "protected:   // funcs\n";
  out << "  bool wasVisitedAST(void *ast);\n";
  out << "  bool wasVisitedList_ASTList(void *ast);\n";
  out << "  bool wasVisitedList_FakeList(void *ast);\n";
  out << "\n";

  // ctor
  out << "public:      // funcs\n";
  out << "  explicit " << dvisitorName << "("
      << visitorName << " *client0 = NULL, "
      << "bool ensureOneVisit0 = true"
      << ")\n";
  out << "    : client(client0)\n";
  out << "    , ensureOneVisit(ensureOneVisit0)\n";
  out << "  {}\n";
  out << "\n";

  // visitor methods
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();
    out << "  virtual bool visit" << c->super->name << "("
        <<   c->super->name << " *obj);\n"
        << "  virtual void postvisit" << c->super->name << "("
        <<   c->super->name << " *obj);\n";
  }

  out << "\n  // List 'classes'\n";
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    out << "  virtual bool visitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">*);\n";
    out << "  virtual void postvisitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">*);\n";
  }

  StringSet listItemClassesSet; // set of list item classes printed so far
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    xassert(!listItemClassesSet.contains(cls->classAndMemberName)); // should not repeat
    listItemClassesSet.add(cls->classAndMemberName);
    out << "  virtual bool visitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << "*);\n";
    out << "  virtual void postvisitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << "*);\n";
  }

  // we are done
  out << "};\n\n";
}


void CGen::emitDVisitorImplVisitedCheck(char const *name) {
  out << "bool " << dvisitorName << "::" << name << "(void *ast)\n";
  out << "{\n";
  out << "  // do not bother to check if the user does not want us to\n";
  out << "  if (!ensureOneVisit) {\n";
  out << "    return false;\n";
  out << "  }\n\n";
  out << "  if (!ast) {return false;} // avoid NULL; actually happens for FakeLists\n";
  out << "  if (" << name << "Nodes.contains(ast)) {\n";
  out << "    return true;\n";
  out << "  } else {\n";
  out << "    " << name << "Nodes.add(ast);\n";
  out << "    return false;\n";
  out << "  }\n";
  out << "}\n\n";
}


void CGen::emitDVisitorImplementation()
{
  out << "// ---------------------- " << dvisitorName << " ---------------------\n";

  emitDVisitorImplVisitedCheck("wasVisitedAST");
  emitDVisitorImplVisitedCheck("wasVisitedList_ASTList");
  emitDVisitorImplVisitedCheck("wasVisitedList_FakeList");

  out << "// default no-op delegator-visitor\n";
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();

    out << "bool " << dvisitorName << "::visit" << c->super->name
        << "(" << c->super->name << " *obj) {\n"
      // dsw: I changed this back to xassert() from xassertdb()
      // because NDEBUG just gets turned on more often than I like.
        << "  xassert(!wasVisitedAST(obj));\n"
        << "  return client ? client->visit" << c->super->name << "(obj) : true;\n"
        << "}\n";

    out << "void " << dvisitorName << "::postvisit" << c->super->name
        << "(" << c->super->name << " *obj) {\n"
        << "  if (client) {\n"
        << "    client->postvisit" << c->super->name << "(obj);\n"
        << "  }\n"
        << "}\n";
  }

  out << "\n// List 'classes'\n";
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    // visit
    out << "bool " << dvisitorName << "::visitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">* obj) {\n";
    out << "  xassert(!wasVisitedList_" << cls->kindName() << "(obj));\n";
    out << "  return client ? client->visitList_" << cls->classAndMemberName << "(obj) : true;\n";
    out << "}\n";

    // post visit
    out << "void " << dvisitorName << "::postvisitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">* obj) {\n";
    out << "  if (client) {\n";
    out << "    client->postvisitList_" << cls->classAndMemberName << "(obj);\n";
    out << "  }\n";
    out << "}\n";
  }

  StringSet listItemClassesSet; // set of list item classes printed so far
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    xassert(!listItemClassesSet.contains(cls->classAndMemberName)); // should not repeat
    listItemClassesSet.add(cls->classAndMemberName);

    // visit item
    out << "bool " << dvisitorName << "::visitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << " *obj) {\n";
    // NOTE: we do NOT check that it has been visited before; this is
    // the point of list items: that they are visited multiple times
    // even if the contained item itself is not
    out << "  return client ? client->visitListItem_" << cls->classAndMemberName << "(obj) : true;\n";
    out << "}\n";

    // post visit item
    out << "void " << dvisitorName << "::postvisitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << " *obj) {\n";
    out << "  if (client) {\n";
    out << "    client->postvisitListItem_" << cls->classAndMemberName << "(obj);\n";
    out << "  }\n";
    out << "}\n";
  }

  out << "\n\n";
}

// ------------------- xml visitor --------------------

void CGen::emitXmlCtorArgs(ASTList<CtorArg> const &args, char const *baseName,
                           string const &className) {
  FOREACH_ASTLIST(CtorArg, args, argiter) {
    CtorArg const &arg = *(argiter.data());
    emitXmlField(arg.type, arg.name, baseName, className, NULL);
  }
}

void CGen::emitXmlFields(ASTList<Annotation> const &decls, char const *baseName,
                         string const &className) {
  FOREACH_ASTLIST(Annotation, decls, iter) {
    if (!iter.data()->isUserDecl()) continue;
    UserDecl const *ud = iter.data()->asUserDeclC();
    if (!ud->amod->hasModPrefix("xml")) continue;
    emitXmlField(extractFieldType(ud->code),
                 extractFieldName(ud->code),
                 baseName,
                 className,
                 ud->amod);
  }
}

void CGen::emitXmlField(rostring type, rostring name, char const *baseName,
                        string const &className, AccessMod *amod) {
  if (streq(name, "arraySize")) {
    breaker();
  }
  // FIX: there is a problem with coming up with a way to serialize a
  // NULL string: 1) the value must be quoted, 2) any string you use
  // to represent NULL is also a valid string value, 3) quoting twice
  // is expensive; For now, I simply omit mention of it: it will
  // default to NULL.
  if (streq(type, "string") || streq(type, "StringRef")) {
    out << "  if (" << baseName << "->" << name << ") {\n";
    out << "    out << \"\\n\";\n";
    out << "    if (indent) printIndentation();\n";
    out << "    out << \"" << name << "\" << \"=\";\n";
    out << "    out << quoted(" << baseName << "->" << name << ");\n";
    out << "  } else {\n";
    // print nothing; the default value is NULL
//      out << "    out << \"\\\"0\\\"\";\n";
    out << "  }\n";
  }
  else if (streq(type, "bool")) {
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"" << name << "\" << \"=\";\n";
    out << "  out << quoted(toXml_bool(" << baseName << "->" << name << "));\n";
  }
  else if (streq(type, "int")) {
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"" << name << "\" << \"=\";\n";
    out << "  out << quoted(toXml_int(" << baseName << "->" << name << "));\n";
  }
  else if (streq(type, "unsigned int")) {
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"" << name << "\" << \"=\";\n";
    out << "  out << quoted(toXml_unsigned_int(" << baseName << "->" << name << "));\n";
  }
  else if (streq(type, "long")) {
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"" << name << "\" << \"=\";\n";
    out << "  out << quoted(toXml_long(" << baseName << "->" << name << "));\n";
  }
  else if (streq(type, "unsigned long")) {
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"" << name << "\" << \"=\";\n";
    out << "  out << quoted(toXml_unsigned_long(" << baseName << "->" << name << "));\n";
  }
  else if (streq(type, "double")) {
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"" << name << "\" << \"=\";\n";
    out << "  out << quoted(toXml_double(" << baseName << "->" << name << "));\n";
  }
  else if (streq(type, "SourceLoc")) {
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"" << name << "\" << \"=\";\n";
    out << "  out << quoted(toXml_SourceLoc(" << baseName << "->" << name << "));\n";
  }
  else if (isListType(type)) {
    out << "  if (" << baseName << ") {\n";
    out << "    out << \"\\n\";\n";
    out << "    if (indent) printIndentation();\n";
    out << "    out << \"" << name << "\" << \"=\\\"\";\n";
    out << "    xmlPrintPointer(out, \"AL\", &(" << baseName << "->" << name << "));\n";
    out << "    out << \"\\\"\";\n";
    out << "  }\n";
  }
  else if (isFakeListType(type)) {
    out << "  if (" << baseName << " && " << baseName << "->" << name << ") {\n";
    out << "    out << \"\\n\";\n";
    out << "    if (indent) printIndentation();\n";
    out << "    out << \"" << name << "\" << \"=\\\"\";\n";
    out << "    xmlPrintPointer(out, \"FL\", " << baseName << "->" << name << ");\n";
    out << "    out << \"\\\"\";\n";
    out << "  }\n";
  }
  else if (isTreeNode(type) || (isTreeNodePtr(type))) {
    out << "  if (" << baseName << " && " << baseName << "->" << name << ") {\n";
    out << "    out << \"\\n\";\n";
    out << "    if (indent) printIndentation();\n";
    out << "    out << \"" << name << "\" << \"=\\\"\";\n";
    out << "    xmlPrintPointer(out, \"AST\", " << baseName << "->" << name << ");\n";
    out << "    out << \"\\\"\";\n";
    out << "  }\n";
  } else if (amod && amod->hasModPrefix("xmlEmbed") && amod->hasModPrefix("xml_")) {
    rostring idPrefix = amod->getModSuffixFromPrefix("xml_");
    out << "  if (" << baseName << ") {\n";
    out << "    out << \"\\n\";\n";
    out << "    if (indent) printIndentation();\n";
    out << "    out << \"" << name << "\" << \"=\\\"\";\n";
    out << "    xmlPrintPointer(out, \"" << idPrefix << "\", ";
    out << "&";
    out << baseName << "->" << name << ");\n";
    out << "    out << \"\\\"\";\n";
    out << "  }\n";
  }

    // FIX: relace the below with this; see note at "crap" below.
//    else if (isPtrKind(type) && amod && amod->hasModPrefix("xml_")) {
  else if (
           (!amod && isPtrKind(type))
           || (amod && amod->hasModPrefix("xml_"))
           ) {
    // catch-all for xml objects
    string idPrefix;
    if (amod) {
      idPrefix = amod->getModSuffixFromPrefix("xml_");
    } else {
      // FIX: get rid of this piece of crap when we get a way to put
      // an access specifier onto a ctor argument in the ast language
      idPrefix = stringc << "TY";
    }
    out << "  if (" << baseName << " && " << baseName << "->" << name << ") {\n";
    out << "    out << \"\\n\";\n";
    out << "    if (indent) printIndentation();\n";
    out << "    out << \"" << name << "\" << \"=\\\"\";\n";
    out << "    xmlPrintPointer(out, \"" << idPrefix << "\", ";
    out << baseName << "->" << name << ");\n";
    out << "    out << \"\\\"\";\n";
    out << "  }\n";

  } else {
    // catch-all for non-objects
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"" << name << "\" << \"=\";\n";
    out << "  out << quoted(toXml(" << baseName << "->" << name << "));\n";
  }
}

void HGen::emitXmlVisitorInterface()
{
  out << "// the xml-visitor interface class\n"
      << "class " << xmlVisitorName << " : public " << visitorName << " {\n";

  out << "protected:   // data\n";
  out << "  ostream &out;                       // output stream to print to\n";
  out << "  int &depth;                         // current depth\n";
  out << "  bool indent;                        // should the xml be indented\n";
  out << "  bool ensureOneVisit;                // check for visiting at most once?\n";
  out << "  SObjSet<void*> wasVisitedASTNodes;  // set of visited nodes\n";
  out << "  SObjSet<void*> wasVisitedList_ASTListNodes; // set of visited ASTLists\n";
  out << "  SObjSet<void*> wasVisitedList_FakeListNodes; // set of visited FakeLists\n";
  out << "\n";

  out << "protected:   // funcs\n";
  out << "  bool wasVisitedAST(void *ast);\n";
  out << "  bool wasVisitedList_ASTList(void *ast);\n";
  out << "  bool wasVisitedList_FakeList(void *ast);\n";
  out << "  void printIndentation();\n";
  out << "\n";

  // ctor
  out << "public:      // funcs\n";
  out << "  explicit " << xmlVisitorName << "("
      << "ostream &out0, "
      << "int &depth0, "
      << "bool indent0 = false, "
      << "bool ensureOneVisit0 = true"
      << ")\n";
  out << "    : out(out0)\n";
  out << "    , depth(depth0)\n";
  out << "    , indent(indent0)\n";
  out << "    , ensureOneVisit(ensureOneVisit0)\n";
  out << "  {}\n";
  out << "\n";

  // visitor methods
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();
    out << "  virtual bool visit" << c->super->name << "("
        <<   c->super->name << " *obj);\n"
        << "  virtual void postvisit" << c->super->name << "("
        <<   c->super->name << " *obj);\n";
  }

  out << "\n  // List 'classes'\n";
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    out << "  virtual bool visitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">*);\n";
    out << "  virtual void postvisitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">*);\n";
  }

  StringSet listItemClassesSet; // set of list item classes printed so far
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    xassert(!listItemClassesSet.contains(cls->classAndMemberName)); // should not repeat
    listItemClassesSet.add(cls->classAndMemberName);
    out << "  virtual bool visitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << "*);\n";
    out << "  virtual void postvisitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << "*);\n";
  }

  // we are done
  out << "};\n\n";
}


void CGen::emitXmlVisitorImplVisitedCheck(char const *name) {
  out << "bool " << xmlVisitorName << "::" << name << "(void *ast)\n";
  out << "{\n";
  out << "  // do not bother to check if the user does not want us to\n";
  out << "  if (!ensureOneVisit) {\n";
  out << "    return false;\n";
  out << "  }\n\n";
  out << "  if (!ast) {return false;} // avoid NULL; actually happens for FakeLists\n";
  out << "  if (" << name << "Nodes.contains(ast)) {\n";
  out << "    return true;\n";
  out << "  } else {\n";
  out << "    " << name << "Nodes.add(ast);\n";
  out << "    return false;\n";
  out << "  }\n";
  out << "}\n\n";
}


void CGen::emitXmlVisitorImplementation()
{
  out << "// ---------------------- " << xmlVisitorName << " ---------------------\n";

  emitXmlVisitorImplVisitedCheck("wasVisitedAST");
  emitXmlVisitorImplVisitedCheck("wasVisitedList_ASTList");
  emitXmlVisitorImplVisitedCheck("wasVisitedList_FakeList");

  out << "void " << xmlVisitorName << "::printIndentation()\n";
  out << "{\n";
  out << "  for(int i=0; i<depth; ++i) out << \" \";\n";
  out << "}\n\n";

  out << "// default xml-visitor\n";
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();

    out << "bool " << xmlVisitorName << "::visit" << c->super->name;
    out << "(" << c->super->name << " *obj) {\n";
    out << "  if(wasVisitedAST(obj)) return false;\n";
    // for now everything is a container tag
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"<\" << obj->kindName();\n";

    // print the attributes of the superclass
    out << "  ++depth;\n";      // indent them one level

    // emit the id property
    // put it on the same line as the tag
//      out << "  out << \"\\n\";\n";
//      out << "  if (indent) printIndentation();\n";
    out << "  out << \" _id=\\\"\";\n";
    out << "  xmlPrintPointer(out, \"AST\", obj);\n";
    out << "  out << \"\\\"\";\n";

    // emit other properties
    emitXmlCtorArgs(c->super->args, "obj", c->super->name);
    emitXmlFields(c->super->decls, "obj", c->super->name);

    // print the attributes of the subclasses
    if (c->hasChildren()) {
      out << "  switch(obj->kind()) {\n";
      out << "  default: xfailure(\"bad tag\"); break;\n";
      FOREACH_ASTLIST(ASTClass, c->ctors, iter) {
        ASTClass const *clazz = iter.data();
        out << "  case " << c->super->name << "::" << clazz->classKindName() << ": {\n";
        // prevent unused variable warning when compiling client code;
        // FIX: turn on when take away the '= NULL' code below.
//          if (clazz->args.isNotEmpty() || clazz->decls.isNotEmpty()) {
        out << "    " << clazz->name << " *obj0 = obj->as" << clazz->name << "();\n";
//          }
        emitXmlCtorArgs(clazz->args, "obj0", clazz->name);
        emitXmlFields(clazz->decls, "obj0", clazz->name);

        // prevent unused variable warning when compiling client code;
        // FIX: remove when all kinds of fields are printed
        out << "    obj0 = NULL;\n";

        out << "    break;\n";
        out << "    }\n";
      }
      out << "  }\n";
    }

    // print the 'last' attributes of the superclass, which come after
    // all subclass things
    emitXmlCtorArgs(c->super->lastArgs, "obj", c->super->name);

    out << "  --depth;\n";      // outdent temporarily so close bracket lines up with open
    // commenting out these two lines puts the closing angle bracket
    // on the same line as the last attribute, or if none, on the same
    // line as the tag
//      out << "  out << \"\\n\";\n";
//      out << "  if (indent) printIndentation();\n";
    out << "  out << \">\";\n";
    out << "  ++depth;\n";      // indent for nested children
    out << "  return true;\n";
    out << "}\n\n";;

    out << "void " << xmlVisitorName << "::postvisit" << c->super->name;
    out << "(" << c->super->name << " *obj) {\n";
    out << "  --depth;\n";
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"</\" << obj->kindName() << \">\";\n";
    out << "}\n\n";
  }

  out << "\n// List 'classes'\n";
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    // visit
    out << "bool " << xmlVisitorName << "::visitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">* obj) {\n";
    out << "  if (obj->isNotEmpty()) {\n";
    out << "    if(wasVisitedList_" << cls->kindName() << "(obj)) return false;\n";
    out << "    out << \"\\n\";\n";
    out << "    if (indent) printIndentation();\n";
    out << "    out << \"<List_" << cls->classAndMemberName << " _id=\\\"\";\n";
    out << "    xmlPrintPointer(out, \"";
    if (cls->lkind == LK_ASTList) {
      out << "AL";
    } else if (cls->lkind == LK_FakeList) {
      out << "FL";
    } else xfailure("illegal list kind");
    out << "\", obj);\n";
    out << "    out << \"\\\">\";\n";
    out << "    ++depth;\n";
    out << "  };\n";
    out << "  return true;\n";
    out << "}\n\n";

    // post visit
    out << "void " << xmlVisitorName << "::postvisitList_" << cls->classAndMemberName
        << "(" << cls->kindName() << "<" << cls->elementClassName << ">* obj) {\n";
    out << "  if (obj->isNotEmpty()) {\n";
    out << "    --depth;\n";
    out << "    out << \"\\n\";\n";
    out << "    if (indent) printIndentation();\n";
    out << "    out << \"</List_" << cls->classAndMemberName << ">\";\n";
    out << "  }\n";
    out << "}\n\n";

    // visit item
    out << "bool " << xmlVisitorName << "::visitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << " *obj) {\n";
    out << "  xassert(obj);\n";
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"<_List_Item\" << \" item=\\\"\";\n";
    out << "  xmlPrintPointer(out, \"AST\", obj);\n";
    out << "  out << \"\\\">\";\n";
    out << "  ++depth;\n";
    out << "  return true;\n";
    out << "}\n\n";

    // post visit item
    out << "void " << xmlVisitorName << "::postvisitListItem_" << cls->classAndMemberName
        << "(" << cls->elementClassName << " *obj) {\n";
    out << "  xassert(obj);\n";
    out << "  --depth;\n";
    out << "  out << \"\\n\";\n";
    out << "  if (indent) printIndentation();\n";
    out << "  out << \"</_List_Item>\";\n";
    out << "}\n\n";
  }

  out << "\n\n";
}


// ------------------- modification visitor --------------------
void HGen::emitMVisitorInterface()
{
  out << "// the modification visitor interface class\n"
      << "class " << mvisitorName << " {\n";
  emitVisitorInterfacePrelude(mvisitorName);

  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();

    out << "  virtual bool visit" << c->super->name << "("
        <<   c->super->name << " *&obj);\n"
        << "  void mtraverse(" << c->super->name << " *&obj);\n"
        ;
  }
  out << "};\n\n";
}


// The generated code does:
//   - any actions specified for the superclass in the .ast file
//   - invoke the visitor method, returning if it returns false
//   - recursively traverse superclass fields
//   - switch on subclass type, if there are any
//   - do actions specified for the subclass in the .ast file
//   - recursively visit the subclass fields
// There is a slightly nonideal aspect to the above, in that the
// subclass 'mtraverse' action is done *after* the superclass fields
// are traversed, so the former can't skip the latter, but I'll leave
// it for now (would require emitting two switch blocks to fix).
void CGen::emitMVisitorImplementation()
{
  out << "// ---------------------- " << mvisitorName << " ---------------------\n";

  out << mvisitorName << "::~" << mvisitorName << "() {}\n\n";

  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();

    out << "bool " << mvisitorName << "::visit" << c->super->name << "("
        <<   c->super->name << " *&obj) { return true; }\n"
        << "\n"
        ;

    out << "void " << mvisitorName << "::mtraverse(" << c->super->name << " *&obj)\n"
        << "{\n"
        ;

    // invoke visitor function
    out << "  if (!visit" << c->super->name << "(obj)) { return; }\n"
        << "\n"
        ;

    // superclass action specified in .ast file
    emitCustomCode(c->super->decls, "mtraverse");

    // superclass field traversal
    emitMTraverse(c->super, "obj", "  ");

    if (c->hasChildren()) {
      out << "  switch (obj->kind()) {\n";

      // subclass traversal
      FOREACH_ASTLIST(ASTClass, c->ctors, iter) {
        ASTClass const *sub = iter.data();

        out << "    case " << c->super->name << "::" << sub->classKindName() << ": {\n"
            << "      " << sub->name << " *sub = (" << sub->name << "*)obj;\n"
            << "      (void)sub;\n"      // silence warning if unused
            ;

        // subclass action specified in .ast file
        emitCustomCode(sub->decls, "mtraverse");

        // subclass field traversal
        emitMTraverse(sub, "sub", "      ");

        out << "      break;\n"
            << "    }\n"
            ;
      }

      out << "    default:;\n"       // silence warning
          << "  }\n";
    }

    out << "}\n"
        << "\n"
        << "\n"
        ;
  }
  out << "\n";
}


// emit mtraverse calls for the fields
void CGen::emitMTraverse(ASTClass const *c, rostring obj, rostring i)
{
  // traverse into the ctor arguments
  FOREACH_ASTLIST(CtorArg, c->args, iter) {
    CtorArg const *arg = iter.data();
    string argVar = stringc << obj << "->" << arg->name;

    if (isTreeNode(arg->type) || isTreeNodePtr(arg->type)) {
      string eltType = extractNodeType(arg->type);

      out << i << "if (" << argVar << ") {\n";
      emitMTraverseCall(stringc << i << "  ", eltType, argVar);
      out << i << "}\n";
    }

    else if (isListType(arg->type) &&
             isTreeNode(extractListType(arg->type))) {
      string eltType = extractListType(arg->type);

      // list of tree nodes: iterate and traverse
      out << i << "FOREACH_ASTLIST_NC(" << eltType << ", " << argVar << ", iter) {\n";
      emitMTraverseCall(stringc << i << "  ", eltType, "iter.dataRef()");
      out << i << "}\n";
    }

    else if (isFakeListType(arg->type) &&
             isTreeNode(extractListType(arg->type))) {
      string eltType = extractListType(arg->type);

      // fakelist mtraversal is a little complicated because I
      // need to break apart the 'FakeList' abstraction so I can
      // modify elements, iterate into the substituted part, etc.
      out << i << "// fakelist mtraversal: " << argVar << "\n"
          << i << "{\n"
          << i << "  " << eltType << " **iter = "
               <<   "(" << eltType << "**)&(" << argVar << ");\n"
          << i << "  while (*iter) {\n"
          ;

      emitMTraverseCall(stringc << i << "    ", eltType, "*iter");

      out << i << "    iter = &( (*iter)->next );\n"
          << i << "  }\n"
          << i << "}\n"
          ;
    }
  }
}


void CGen::emitMTraverseCall(rostring i, rostring eltType, rostring argVar)
{
  if (isSuperclassTreeNode(eltType)) {
    // easy case
    out << i << "mtraverse(" << argVar << ");\n";
    return;
  }

  // because the field is declared to be a specific subclass type, we
  // invoke mtraverse but then check that the result has that type

  xassert(isSubclassTreeNode(eltType));
  string superType = getSuperTypeOf(eltType);
  out << i << superType << "* tmp = " << argVar << ";\n"
      << i << "mtraverse(tmp);\n"
      << i << "if (tmp != " << argVar << ") {\n"
      << i << "  " << argVar << " = tmp->as" << eltType << "();\n"
      << i << "}\n"
      ;
}


// ------------------- xml parser --------------------

// FIX: an iterator desing pattern over the fields/ctor_args of an AST
// node would be better than this repeated copies of the DFS

void XmlParserGen::collectXmlParserCtorArgs(ASTList<CtorArg> const &args, char const *baseName)
{
  FOREACH_ASTLIST(CtorArg, args, argiter) {
    CtorArg const &arg = *(argiter.data());
    collectXmlParserField(arg.type, arg.name, baseName, NULL);
  }
}

void XmlParserGen::collectXmlParserFields(ASTList<Annotation> const &decls, char const *baseName)
{
  FOREACH_ASTLIST(Annotation, decls, iter) {
    if (!iter.data()->isUserDecl()) continue;
    UserDecl const *ud = iter.data()->asUserDeclC();
    if (!ud->amod->hasModPrefix("xml")) continue;
    collectXmlParserField(extractFieldType(ud->code),
                          extractFieldName(ud->code),
                          baseName,
                          ud->amod);
  }
}

// FIX: this is now very redundant, but we can still change it to
// exclude some fields of some types, so lets keep it for now.
void XmlParserGen::collectXmlParserField
  (rostring type, rostring name, char const *baseName, AccessMod*)
{
  if (streq(type, "string")) {
    attributeNames.add(name);
  }
  else if (streq(type, "StringRef")) {
    attributeNames.add(name);
  }
  else if (streq(type, "bool")) {
    attributeNames.add(name);
  }

  else if (isListType(type)) {
    attributeNames.add(name);
  }
  else if (isFakeListType(type)) {
    attributeNames.add(name);
  }
  else if (isTreeNode(type) || (isTreeNodePtr(type))) {
    attributeNames.add(name);
  }

  // If you start being more selective, be sure to include the names
  // for things marked "xml"

  else {
    // catch-all ..
//      out << "  " << print << "_GENERIC(" << name << ");\n";
    attributeNames.add(name);
  }
}


void XmlParserGen::emitXmlCtorArgs_AttributeParseRule
  (ASTList<CtorArg> const &args, string &baseName)
{
  FOREACH_ASTLIST(CtorArg, args, argiter) {
    CtorArg const &arg = *(argiter.data());
    emitXmlField_AttributeParseRule(arg.type, arg.name, baseName, NULL);
  }
}

void XmlParserGen::emitXmlFields_AttributeParseRule
  (ASTList<Annotation> const &decls, string &baseName)
{
  FOREACH_ASTLIST(Annotation, decls, iter) {
    if (!iter.data()->isUserDecl()) continue;
    UserDecl const *ud = iter.data()->asUserDeclC();
    if (!ud->amod->hasModPrefix("xml")) continue;
    emitXmlField_AttributeParseRule(extractFieldType(ud->code),
                                    extractFieldName(ud->code),
                                    baseName,
                                    ud->amod);
  }
}

void XmlParserGen::emitXmlField_AttributeParseRule
  (rostring type0, rostring name, string &baseName, AccessMod *amod)
{
  string type = trimWhitespace(type0);
  //  cout << "emitXmlField_AttributeParseRule() name:" << name << ", type:" << type << endl;
  if (streq(type, "string")) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    obj->" << name << " = strdup(parseQuotedString(strValue));\n";
    parser1_defs << "    break;\n";
  }
  else if (streq(type, "StringRef")) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    obj->" << name << " = manager->strTable(parseQuotedString(strValue));\n";
    parser1_defs << "    break;\n";
  }
  else if (streq(type, "bool")) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    fromXml_bool(obj->" << name << ", parseQuotedString(strValue));\n";
    parser1_defs << "    break;\n";
  }
  else if (streq(type, "int")) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    fromXml_int(obj->" << name << ", parseQuotedString(strValue));\n";
    parser1_defs << "    break;\n";
  }
  else if (streq(type, "unsigned int")) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    fromXml_unsigned_int(obj->" << name
                 << ", parseQuotedString(strValue));\n";
    parser1_defs << "    break;\n";
  }
  else if (streq(type, "long")) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    fromXml_long(obj->" << name << ", parseQuotedString(strValue));\n";
    parser1_defs << "    break;\n";
  }
  else if (streq(type, "unsigned long")) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    fromXml_unsigned_long(obj->" << name
                 << ", parseQuotedString(strValue));\n";
    parser1_defs << "    break;\n";
  }
  else if (streq(type, "double")) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    fromXml_double(obj->" << name << ", parseQuotedString(strValue));\n";
    parser1_defs << "    break;\n";
  }
  else if (streq(type, "SourceLoc")) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    // FIX: we don't parse SourceLoc-s yet
    parser1_defs << "    // fromXml_SourceLoc(obj->" << name << ", parseQuotedString(strValue));\n";
    parser1_defs << "    break;\n";
  }
  else if (isListType(type)) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    manager->unsatLinks_List.append(new UnsatLink("
                 << "(void*) &(obj->" << name << "), parseQuotedString(strValue), "
                 << "XTOK_List_" << baseName << "_" << name << ", true));\n";
    parser1_defs << "    break;\n";
  }
  else if (isFakeListType(type)) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    manager->unsatLinks_List.append(new UnsatLink("
                 << "(void*) &(obj->" << name << "), parseQuotedString(strValue), "
                 << "XTOK_List_" << baseName << "_" << name << ", true));\n";
    parser1_defs << "    break;\n";
  }
  else if (isTreeNode(type) || (isTreeNodePtr(type))) {
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    manager->unsatLinks.append(new UnsatLink("
                 << "(void*) &(obj->" << name << "), parseQuotedString(strValue),"
                 << "XTOK_" << extractNodeType(type) << ", false));\n";
    parser1_defs << "    break;\n";
  }
  else if (isPtrKind(type)) {
    // catch-all for objects
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    manager->unsatLinks.append(new UnsatLink("
                 << "(void*) &(obj->" << name << "), parseQuotedString(strValue),"
                 << "XTOK_" << extractNodeType(type) << ", false));\n";
    parser1_defs << "    break;\n";
  } else if (amod && amod->hasModPrefix("xmlEmbed")) {
    // embedded thing
    rostring kind = amod->getModSuffixFromPrefix("xmlEmbed");
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    manager->unsatLinks" << kind << ".append(new UnsatLink("
                 << "(void*) &(obj->" << name << "), parseQuotedString(strValue),"
                 << "XTOK" << kind << "_" << baseName << "_" << name << ", true));\n";
    parser1_defs << "    break;\n";
  } else {
    // catch-all for non-objects
    parser1_defs << "  case XTOK_" << name << ":\n";
    parser1_defs << "    fromXml(obj->" << name << ", parseQuotedString(strValue));\n";
    parser1_defs << "    break;\n";
  }
}

void XmlParserGen::emitXmlParser_objCtorArgs
  (ASTList<CtorArg> const &args, bool &firstTime)
{
  FOREACH_ASTLIST(CtorArg, args, argiter) {
    CtorArg const &arg = *(argiter.data());
    if (firstTime) { firstTime = false; }
    else { parser2_ctorCalls << ", "; }
    if (strlen(arg.defaultValue.c_str())>0) {
      parser2_ctorCalls << arg.defaultValue;
    } else {
      // dsw: this is Scott's idea of how to initialize a type that we
      // know nothing about with no information
      string type = arg.type;
      if (isListType(arg.type)) {
        // need to put a pointer onto the end of ASTList types
        type = stringc << type << "*";
      } else if (isTreeNode(arg.type)) {
        // dsw: FIX: I should probably have something like this here
        // (isTreeNodePtr(type) && isOwner)
        //
        // also for AST node types
        type = stringc << type << "*";
      }
      parser2_ctorCalls << "(" << type << ")0";
    }
  }
}

void XmlParserGen::emitXmlParser_Node
  (ASTClass const *clazz,

   ASTList<CtorArg> const *args,
   ASTList<Annotation> const *decls,
   ASTList<CtorArg> const *lastArgs,

   // these two default to NULL, which is used in the case of a top
   // level class with no subclasses
   ASTList<CtorArg> const *childArgs,
   ASTList<Annotation> const *childDecls)
{
  string name = clazz->name;

  parser0_decls
    << "void registerAttr_" << name
    << "(" << name << " *obj, int attr, char const *strValue);\n";

  parser3_registerCalls
    << "      case XTOK_" << name << ":\n"
    << "        registerAttr_" << name
    << "((" << name << "*)target, attr, yytext0);\n"
    << "      break;\n";

  // we need to supply however many NULL args here as there are ctor args.
  parser2_ctorCalls << "    case XTOK_" << name << ":\n"
                    << "      return new " << name << "(";
  bool firstTime = true;
  if (args)      {emitXmlParser_objCtorArgs(*args, firstTime);}
  if (childArgs) {emitXmlParser_objCtorArgs(*childArgs, firstTime);}
  if (lastArgs)  {emitXmlParser_objCtorArgs(*lastArgs, firstTime);}
  parser2_ctorCalls << ");\n"
                    << "      break;\n";
}

void XmlParserGen::emitXmlParser_Node_registerAttr
  (ASTClass const *clazz,

   ASTList<CtorArg> const *args,
   ASTList<Annotation> const *decls,
   ASTList<CtorArg> const *lastArgs,

   // these two default to NULL, which is used in the case of a top
   // level class with no subclasses
   ASTList<CtorArg> const *childArgs,
   ASTList<Annotation> const *childDecls)
{
  string name = clazz->name;

  parser1_defs
    << "\nvoid ASTXmlReader::registerAttr_" << name
    << "(" << name << " *obj, int attr, char const *strValue) {\n";
  parser1_defs << "  switch(attr) {\n";
  parser1_defs << "  default:\n";
  parser1_defs << "    userError(\"illegal attribute for a " << name << "\");\n";
  parser1_defs << "    break;\n";

  // for each attribute, emit a rule to parse it as an attribute of this tag
  emitXmlCtorArgs_AttributeParseRule(*args, name);
  emitXmlFields_AttributeParseRule(*decls, name);
  emitXmlCtorArgs_AttributeParseRule(*lastArgs, name);
  if (childArgs) {
    xassert(childDecls);
    emitXmlCtorArgs_AttributeParseRule(*childArgs, name);
    emitXmlFields_AttributeParseRule(*childDecls, name);
  }

  parser1_defs << "  }\n";
  parser1_defs << "}\n";
}

void XmlParserGen::emitXmlParser_ASTList(ListClass const *cls)
{
  string name = stringc << "List_" << cls->classAndMemberName;
  // only one rule as lists are homogeneous
  xassert(isTreeNode(cls->elementClassName));
  parser2_ctorCalls << "    case XTOK_" << name << ":\n"
    // NOTE: yes, this should say 'new ASTList' even in the case of
    // FakeLists; ASTLists are also used as "generic lists".
                    << "      return new ASTList<" << cls->elementClassName << ">();\n"
                    << "      break;\n";
}

void XmlParserGen::emitXmlParserImplementation()
{
  tokensOutH  << "  // AST nodes\n";
  tokensOutCC << "  // AST nodes\n";
  lexerOut    << "  /* AST nodes */\n";

  parser1_defs << "bool ASTXmlReader::kind2kindCat(int kind, KindCategory *kindCat) {\n";
  parser1_defs << "  switch(kind) {\n";
  parser1_defs << "  default: return false; // don't know this kind\n";

  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();

    tokensOutH  << "  XTOK_" << c->super->name << ", // \"" << c->super->name << "\"\n";
    tokensOutCC << "  \"XTOK_" << c->super->name << "\",\n";
    lexerOut  << "\"" << c->super->name << "\" return tok(XTOK_" << c->super->name << ");\n";
    parser1_defs << "  case XTOK_" << c->super->name << ": *kindCat = KC_Node; break;\n";

    collectXmlParserCtorArgs(c->super->args, "obj");
    collectXmlParserFields(c->super->decls, "obj");
    collectXmlParserCtorArgs(c->super->lastArgs, "obj");

    if (c->hasChildren()) {
      FOREACH_ASTLIST(ASTClass, c->ctors, iter) {
        ASTClass const *clazz = iter.data();

        tokensOutH  << "    XTOK_" << clazz->name << ", // \"" << clazz->name << "\"\n";
        tokensOutCC << "    \"XTOK_" << clazz->name << "\",\n";
        lexerOut  << "\"" << clazz->name << "\" return tok(XTOK_" << clazz->name << ");\n";
        parser1_defs << "  case XTOK_" << clazz->name << ": *kindCat = KC_Node; break;\n";

        collectXmlParserCtorArgs(clazz->args, "obj0");
        collectXmlParserFields(clazz->decls, "obj0");
        emitXmlParser_Node(clazz,
                           &c->super->args, &c->super->decls, &c->super->lastArgs,
                           &clazz->args, &clazz->decls);
      }
    } else {
      emitXmlParser_Node(c->super,
                         &c->super->args, &c->super->decls, &c->super->lastArgs);
    }
  }

  tokensOutH  << "\n  // List 'classes'\n";
  tokensOutCC << "\n  // List 'classes'\n";
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    tokensOutH  << "  XTOK_List_" << cls->classAndMemberName
                << ", // \"List_" << cls->classAndMemberName << "\"\n";
    tokensOutCC << "  \"XTOK_List_" << cls->classAndMemberName << "\",\n";
    lexerOut  << "\"List_" << cls->classAndMemberName
              << "\" return tok(XTOK_List_" << cls->classAndMemberName << ");\n";
    parser1_defs << "  case XTOK_List_" << cls->classAndMemberName << ": *kindCat = ";
    if (cls->lkind == LK_FakeList) {
      parser1_defs << "KC_FakeList";
    } else if (cls->lkind == LK_ASTList) {
      parser1_defs << "KC_ASTList";
    } else xfailure("illegal list kind");
    parser1_defs << "; break;\n";
    emitXmlParser_ASTList(cls);
  }

  parser1_defs << "  }\n";
  parser1_defs << "  return true;\n";
  parser1_defs << "}\n";

  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();
    if (c->hasChildren()) {
      FOREACH_ASTLIST(ASTClass, c->ctors, iter) {
        ASTClass const *clazz = iter.data();
        emitXmlParser_Node_registerAttr
          (clazz,
           &c->super->args, &c->super->decls, &c->super->lastArgs,
           &clazz->args, &clazz->decls);
      }
    } else {
      emitXmlParser_Node_registerAttr
        (c->super,
         &c->super->args, &c->super->decls, &c->super->lastArgs);
    }
  }

  // generate the method that says we should not record the kind of
  // any tag that is parsed as there is no multiple inheritance going
  // on in the AST
  parser1_defs << "\nbool ASTXmlReader::recordKind(int kind, bool& answer) {\n";
  parser1_defs << "  switch(kind) {\n";
  parser1_defs << "  default: return false; break;\n";
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();
    if (c->hasChildren()) {
      FOREACH_ASTLIST(ASTClass, c->ctors, iter) {
        string name = iter.data()->name;
        parser1_defs << "  case XTOK_" << name << ": answer = false; return true; break;\n";
      }
    } else {
      string name = c->super->name;
      parser1_defs << "  case XTOK_" << name << ": answer = false; return true; break;\n";
    }
  }

  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    parser1_defs << "  case XTOK_List_" << cls->classAndMemberName << ": answer = false; return true; break;\n";
  }
  parser1_defs << "  }\n";
  parser1_defs << "}\n";

  // generate the method that says we should not record the kind of
  // any tag that is parsed as there is no multiple inheritance going
  // on in the AST
  parser1_defs << "\nbool ASTXmlReader::upcastToWantedType";
  parser1_defs << "(void *obj, int kind, void **target, int targetKind) {\n";
  parser1_defs << "  switch(kind) {\n";
  parser1_defs << "  default: return false; break;\n";
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();
    if (c->hasChildren()) {
      FOREACH_ASTLIST(ASTClass, c->ctors, iter) {
        parser1_defs << "  case XTOK_" << iter.data()->name << ":\n";
      }
    } else {
      parser1_defs << "  case XTOK_" << c->super->name << ":\n";
    }
  }
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    parser1_defs << "  case XTOK_List_" << iter.data()->classAndMemberName << ":\n";
  }
  parser1_defs << "    xfailure(\"should never be called\"); return true; break;\n";
  parser1_defs << "  }\n";
  parser1_defs << "}\n";

  // generate the method that says we should not have to call
  // operator=() on any objects because no AST nodes embed into one
  // another
  parser1_defs << "\nbool ASTXmlReader::callOpAssignToEmbeddedObj";
  parser1_defs << "(void *obj, int kind, void *target) {\n";
  parser1_defs << "  switch(kind) {\n";
  parser1_defs << "  default: return false; break;\n";
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *c = iter.data();
    if (c->hasChildren()) {
      FOREACH_ASTLIST(ASTClass, c->ctors, iter) {
        parser1_defs << "  case XTOK_" << iter.data()->name << ":\n";
      }
    } else {
      parser1_defs << "  case XTOK_" << c->super->name << ":\n";
    }
  }
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    parser1_defs << "  case XTOK_List_" << iter.data()->classAndMemberName << ":\n";
  }
  parser1_defs << "    xfailure(\"should never be called\"); return true; break;\n";
  parser1_defs << "  }\n";
  parser1_defs << "}\n";

  // generate generic FakeList reverse
  parser1_defs << "bool ASTXmlReader::convertList2FakeList";
  parser1_defs << "(ASTList<char> *list, int listKind, void **target) {\n";
  parser1_defs << "  switch(listKind) {\n";
  parser1_defs << "  default: return false; // we did not find a matching tag\n";
  FOREACH_ASTLIST(ListClass, listClasses, iter) {
    ListClass const *cls = iter.data();
    if (cls->lkind != LK_FakeList) continue;
    parser1_defs << "  case XTOK_List_" << cls->classAndMemberName << ": {\n";
    parser1_defs << "    xassert(list);\n";
    parser1_defs << "    FakeList<" << cls->elementClassName << "> *ret = NULL;\n";
    parser1_defs << "    FakeList<" << cls->elementClassName << "> *prev = NULL;\n";
    parser1_defs << "    FOREACH_ASTLIST_NC(" << cls->elementClassName << ",\n";
    parser1_defs << "                       reinterpret_cast<ASTList<" << cls->elementClassName << ">&>(*list),\n";
    parser1_defs << "                       iter) {\n";
    parser1_defs << "      if (prev) {\n";
    parser1_defs << "        prev->first()->next = iter.data();\n";
    parser1_defs << "        prev = FakeList<" << cls->elementClassName << ">::makeList(prev->first()->next);\n";
    parser1_defs << "      } else {\n";
    parser1_defs << "        ret = FakeList<" << cls->elementClassName << ">::makeList(iter.data());\n";
    parser1_defs << "        prev = ret;\n";
    parser1_defs << "      }\n";
    parser1_defs << "    }\n";
    parser1_defs << "    *target = ret;";
    parser1_defs << "    break;\n";
    parser1_defs << "  }\n";
  }
  parser1_defs << "  }\n";
  parser1_defs << "  return true;\n";
  parser1_defs << "}\n";

  tokensOutH  << "\n";
  tokensOutH  << "  // metadata tags that do not occur in the AST itself\n";
  tokensOutH  << "  XTOK__List_Item, // \"_List_Item\"\n";
  tokensOutH  << "  // metadata attributes that do not occur in the AST itself\n";
  tokensOutH  << "  XTOK_DOT_ID, // \"_id\"\n";
  tokensOutH  << "  XTOK_item, // \"item\"\n";

  tokensOutCC << "\n";
  tokensOutCC << "  // metadata tags that do not occur in the AST itself\n";
  tokensOutCC << "  \"XTOK__List_Item\", // \"_List_Item\"\n";
  tokensOutCC << "  // metadata attributes that do not occur in the AST itself\n";
  tokensOutCC << "  \"XTOK_item\", // \"item\"\n";
  tokensOutCC << "  \"XTOK_DOT_ID\", // \"_id\"\n";

  lexerOut << "\n";
  lexerOut << "  /* metadata tags that do not occur in the AST itself */\n";
  lexerOut << "\"_List_Item\" return tok(XTOK__List_Item);\n";
  lexerOut << "  /* metadata attributes that do not occur in the AST itself */\n";
  lexerOut << "\"item\" return tok(XTOK_item);\n";
  lexerOut << "\"_id\" return tok(XTOK_DOT_ID);\n";

  tokensOutH  << "\n";
  tokensOutH  << "  // child attribute names\n";
  tokensOutCC << "\n";
  tokensOutCC << "  // child attribute names\n";
  lexerOut << "\n";
  lexerOut << "  /* child attribute names */\n";

  FOREACH_STRINGSET(attributeNames, attrIter) {
    string const &attr = attrIter.data();
    tokensOutH  << "  XTOK_" << attr << ", // \"" << attr << "\"\n";
    tokensOutCC << "  \"XTOK_" << attr << "\",\n";
    lexerOut  << "\"" << attr << "\" return tok(XTOK_" << attr << ");\n";
  }
}


// -------------------- extension merging ------------------
// the 'allClasses' list is filled in after merging, so I
// can't use it in this section
#define allClasses NO!

void mergeClass(ASTClass *base, ASTClass *ext)
{
  xassert(base->name.equals(ext->name));
  trace("merge") << "merging class: " << ext->name << endl;

  // move all ctor args to the base
  while (ext->args.isNotEmpty()) {
    base->args.append(ext->args.removeFirst());
  }

  // and same for annotations
  while (ext->decls.isNotEmpty()) {
    base->decls.append(ext->decls.removeFirst());
  }
}


void mergeEnum(TF_enum *base, TF_enum *ext)
{
  xassert(base->name.equals(ext->name));
  trace("merge") << "merging enum: " << ext->name << endl;

  while (ext->enumerators.isNotEmpty()) {
    base->enumerators.append(ext->enumerators.removeFirst());
  }
}


ASTClass *findClass(TF_class *base, rostring name)
{
  FOREACH_ASTLIST_NC(ASTClass, base->ctors, iter) {
    if (iter.data()->name.equals(name)) {
      return iter.data();
    }
  }
  return NULL;   // not found
}

void mergeSuperclass(TF_class *base, TF_class *ext)
{
  // should only get here for same-named classes
  xassert(base->super->name.equals(ext->super->name));
  trace("merge") << "merging superclass: " << ext->super->name << endl;

  // merge the superclass ctor args and annotations
  mergeClass(base->super, ext->super);

  // for each subclass, either add it or merge it
  while (ext->ctors.isNotEmpty()) {
    ASTClass * /*owner*/ c = ext->ctors.removeFirst();

    ASTClass *prev = findClass(base, c->name);
    if (prev) {
      mergeClass(prev, c);
      delete c;
    }
    else {
      // add it wholesale
      trace("merge") << "adding subclass: " << c->name << endl;
      base->ctors.append(c);
    }
  }
}


TF_class *findSuperclass(ASTSpecFile *base, rostring name)
{
  // I can *not* simply iterate over 'allClasses', because that
  // list is created *after* merging!
  FOREACH_ASTLIST_NC(ToplevelForm, base->forms, iter) {
    ToplevelForm *tf = iter.data();
    if (tf->isTF_class() &&
        tf->asTF_class()->super->name.equals(name)) {
      return tf->asTF_class();
    }
  }
  return NULL;    // not found
}

TF_enum *findEnum(ASTSpecFile *base, rostring name)
{
  FOREACH_ASTLIST_NC(ToplevelForm, base->forms, iter) {
    ToplevelForm *tf = iter.data();
    if (tf->isTF_enum() &&
        tf->asTF_enum()->name.equals(name)) {
      return tf->asTF_enum();
    }
  }
  return NULL;    // not found
}

void mergeExtension(ASTSpecFile *base, ASTSpecFile *ext)
{
  // for each toplevel form, either add it or merge it
  int ct = 0;
  while (ext->forms.isNotEmpty()) {
    ToplevelForm * /*owner*/ tf = ext->forms.removeFirst();

    if (tf->isTF_class()) {
      TF_class *c = tf->asTF_class();

      // is the superclass name something present in the
      // base specification?
      TF_class *prev = findSuperclass(base, c->super->name);
      if (prev) {
        mergeSuperclass(prev, c);
        delete c;
      }
      else {
        // add the whole class
        trace("merge") << "adding new superclass: " << c->super->name << endl;
        base->forms.append(c);
      }
    }

    else if (tf->isTF_enum()) {
      TF_enum *e = tf->asTF_enum();

      // is the enum present in the base?
      TF_enum *prev = findEnum(base, e->name);
      if (prev) {
        mergeEnum(prev, e);
        delete e;
      }
      else {
        // add the whole enum
        trace("merge") << "adding new enum: " << e->name << endl;
        base->forms.append(e);
      }
    }

    else {
      // verbatim or option: just add it directly

      if (ct == 0) {
        // *first* verbatim: goes into a special place in the
        // base, before any classes but after any base verbatims
        int i;
        for (i=0; i < base->forms.count(); i++) {
          ToplevelForm *baseForm = base->forms.nth(i);

          if (baseForm->isTF_class()) {
            // ok, this is the first class, so stop here
            // and we'll insert at 'i', thus inserting
            // just before this class
            break;
          }
        }

        // insert the base so it becomes position 'i'
        trace("merge") << "inserting extension verbatim near top\n";
        base->forms.insertAt(tf, i);
      }

      else {
        // normal processing: append everything
        trace("merge") << "appending extension verbatim/option section\n";
        base->forms.append(tf);
      }
    }

    ct++;
  }
}

// re-enable allClasses
#undef allClasses

void recordListClass(ListKind lkind, rostring className, CtorArg const *arg) {
  rostring argName = arg->name;
  ListClass *cls = new ListClass
    (lkind, stringc << className << "_" << argName, extractListType(arg->type));
  if (!listClassesSet.contains(cls->classAndMemberName)) {
    listClassesSet.add(cls->classAndMemberName);
    listClasses.append(cls);
  } else {
    delete cls;
  }
}

void getListClasses(rostring className, CtorArg const *arg) {
  // I would rather visit all the lists, but we don't seem to generate
  // visit() traversals for non-tree nodes, so there is nothing to put
  // inside the nesting
  if (isListType(arg->type) && isTreeNode(extractListType(arg->type))) {
    recordListClass(LK_ASTList, className, arg);
  }
  if (isFakeListType(arg->type) && isTreeNode(extractListType(arg->type))) {
    recordListClass(LK_FakeList, className, arg);
  }
}

void getListClasses(ASTClass const *c) {
  rostring className = c->name;
  FOREACH_ASTLIST(CtorArg, c->args, ctorIter) {
    getListClasses(className, ctorIter.data());
  }
  FOREACH_ASTLIST(CtorArg, c->lastArgs, ctorIter) {
    getListClasses(className, ctorIter.data());
  }
}

void getListClasses() {
  SFOREACH_OBJLIST(TF_class, allClasses, iter) {
    TF_class const *cls = iter.data();
    getListClasses(cls->super);
    FOREACH_ASTLIST(ASTClass, cls->ctors, ctorIter) {
      getListClasses(ctorIter.data());
    }
  }
}


// --------------------- toplevel control ----------------------
void checkUnusedCustoms(ASTClass const *c)
{
  FOREACH_ASTLIST(Annotation, c->decls, iter) {
    Annotation const *a = iter.data();

    if (a->isCustomCode()) {
      CustomCode const *cc = a->asCustomCodeC();
      if (cc->used == false) {
        cout << "warning: unused custom code `" << cc->qualifier << "'\n";
      }
    }
  }
}

        
void grabOptionName(rostring opname, string &oparg, TF_option const *op)
{
  if (op->args.count() != 1) {
    xfatal("'" << opname << "' option requires one argument");
  }

  if (oparg.length() > 0) {
    // It would be conceivable to allow multiple visitors, but
    // I don't see any advantage to doing so.  If the extension
    // simply changes the name, then the resulting error messages
    // (compilation errors from parts of the system using the
    // old name) are not obvious to diagnose.
    xfatal("there is already " << a_or_an(opname) <<
           " class, called " << oparg << ";\n" <<
           "you should use (subclass) that one");
  }

  // name of the visitor interface class
  oparg = *( op->args.firstC() );
}


void entry(int argc, char **argv)
{
  TRACE_ARGS();
  checkHeap();
  SourceLocManager mgr;

  if (argc < 2) {
    cout << "usage: " << argv[0] << " [options] file.ast [extension.ast [...]]\n"
         << "  options:\n"
         << "    -o<name>   output filenames are name.{h,cc}\n"
         << "               (default is \"file\" for \"file.ast\")\n"
         << "    -v         verbose operation, particularly for merging\n"
         << "    -nocvr     do not use covariant return types in clone()\n"
         ;

    return;
  }

  char const *basename = NULL;      // nothing set

  argv++;
  while (argv[0][0] == '-') {
    if (argv[0][1] == 'b' ||        // 'b' is for compatibility
        argv[0][1] == 'o') {
      if (argv[0][2]) {
        // name specified directly after the -o
        basename = argv[0]+2;
      }
      else if (argv[1]) {
        // name follows the -o option
        basename = argv[1];
        argv++;
      }
    }
    else if (argv[0][1] == 'v') {
      traceAddSys("merge");
    }
    else if (streq(argv[0], "-nocvr")) {
      nocvr = true;
    }
    else {
      xfatal("unknown option: " << argv[0]);
    }
    argv++;
  }
  if (!argv[0]) {
    xfatal("missing ast spec file name");
  }

  char const *srcFname = argv[0];
  argv++;

  // parse the grammar spec
  Owner<ASTSpecFile> ast;
  ast = readAbstractGrammar(srcFname);
  wholeAST = ast;

  // parse and merge extension modules
  ObjList<string> modules;
  while (*argv) {
    char const *fname = *argv;
    argv++;
    
    modules.append(new string(fname));

    Owner<ASTSpecFile> extension;
    extension = readAbstractGrammar(fname);

    mergeExtension(ast, extension);
  }

  // scan options, and fill 'allClasses'
  {
    FOREACH_ASTLIST_NC(ToplevelForm, ast->forms, iter) {
      if (iter.data()->isTF_option()) {
        TF_option const *op = iter.data()->asTF_optionC();

        if (op->name.equals("visitor")) {
          grabOptionName("visitor", visitorName, op);
        }
        else if (op->name.equals("dvisitor")) {
          grabOptionName("dvisitor", dvisitorName, op);
        }
        else if (op->name.equals("xmlVisitor")) {
          grabOptionName("xmlVisitor", xmlVisitorName, op);
        }
        else if (op->name.equals("xmlParser")) {
          grabOptionName("xmlParser", xmlParserName, op);
        }
        else if (op->name.equals("mvisitor")) {
          grabOptionName("mvisitor", mvisitorName, op);
        }
        else if (op->name.equals("xmlPrint")) {
          wantXMLPrint = true;
        }
        else if (op->name.equals("gdb")) {
          wantGDB = true;
        }
        else {
          xfatal("unknown option: " << op->name);
        }
      }

      else if (iter.data()->isTF_class()) {
        allClasses.prepend(iter.data()->asTF_class());
      }
    }
  }

  // I built it in reverse for O(n) performance
  allClasses.reverse();

  // generate the header
  string base = replace(srcFname, ".ast", "");
  if (basename) {
    base = basename;
  }

  // get all of the list classes
  getListClasses();

  // dsw: I want a way to generate just the parser and nothing else;
  // this separation into two blocks suggests that parsing the ast
  // file and generating something from it should perhaps be separated
  // into two parts
  if (!tracingSys("no_ast.gen")) {
    string hdrFname = base & ".h";
    HGen hg(srcFname, modules, hdrFname, *ast);
    cout << "writing " << hdrFname << "...\n";
    hg.emitFile();

    // generated the c++ code
    string codeFname = base & ".cc";
    CGen cg(srcFname, modules, codeFname, *ast, hdrFname);
    cout << "writing " << codeFname << "...\n";
    cg.emitFile();

    // dsw: the xml parser stuff won't use the custom sections, so
    // this generates a lot of spurious warnings if I put it outside
    // of this block
    //
    // check for any unused 'custom' sections; a given section is only
    // used if one of the generation routines asks for it by name, so
    // a mistyped custom section name would not yet have been noticed
    {
      SFOREACH_OBJLIST(TF_class, allClasses, iter) {
        TF_class const *c = iter.data();
        checkUnusedCustoms(c->super);
      
        FOREACH_ASTLIST(ASTClass, c->ctors, subIter) {
          checkUnusedCustoms(subIter.data());
        }
      }
      
      FOREACH_ASTLIST(ToplevelForm, ast->forms, iter2) {
        if (iter2.data()->isTF_custom()) {
          CustomCode const *cc = iter2.data()->asTF_customC()->cust;
          if (cc->used == false) {
            cout << "warning: unused custom code `" << cc->qualifier << "'\n";
          }
        }
      }
    }
  }

  // dsw: this is really completely independent of the other generated
  // files
  if (tracingSys("xmlParser") && wantXmlParser()) {
    XmlParserGen xgen(xmlParserName);
    xgen.emitXmlParserImplementation();
  }
}

ARGS_MAIN
