// ast.ast.h
// *** DO NOT EDIT ***
// generated automatically by astgen, from ast.ast

#ifndef AST_AST_H
#define AST_AST_H

#include "asthelp.h"        // helpers for generated code

// fwd decls
class ASTSpecFile;
class ToplevelForm;
class TF_verbatim;
class TF_impl_verbatim;
class TF_class;
class TF_option;
class TF_custom;
class TF_enum;
class ASTClass;
class AccessMod;
class Annotation;
class UserDecl;
class CustomCode;
class CtorArg;
class BaseClass;


// *** DO NOT EDIT ***

  #include "str.h"         // string

  // this signals to ast.hand.cc that ast.ast.cc is nonempty,
  // so none of the bootstrap code in ast.hand.cc should be used
  #define GENERATED_AST_PRESENT

// *** DO NOT EDIT ***
class ASTSpecFile {
public:      // data
  ASTList <ToplevelForm > forms;

public:      // funcs
  ASTSpecFile(ASTList <ToplevelForm > *_forms) : forms(_forms) {
  }
  ~ASTSpecFile();

  char const *kindName() const { return "ASTSpecFile"; }

  ASTSpecFile *clone() const;

  void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

};



// *** DO NOT EDIT ***
class ToplevelForm {
public:      // data

public:      // funcs
  ToplevelForm() {
  }
  virtual ~ToplevelForm();

  enum Kind { TF_VERBATIM, TF_IMPL_VERBATIM, TF_CLASS, TF_OPTION, TF_CUSTOM, TF_ENUM, NUM_KINDS };
  virtual Kind kind() const = 0;

  static char const * const kindNames[NUM_KINDS];
  char const *kindName() const { return kindNames[kind()]; }

  DECL_AST_DOWNCASTS(TF_verbatim, TF_VERBATIM)
  DECL_AST_DOWNCASTS(TF_impl_verbatim, TF_IMPL_VERBATIM)
  DECL_AST_DOWNCASTS(TF_class, TF_CLASS)
  DECL_AST_DOWNCASTS(TF_option, TF_OPTION)
  DECL_AST_DOWNCASTS(TF_custom, TF_CUSTOM)
  DECL_AST_DOWNCASTS(TF_enum, TF_ENUM)

  virtual ToplevelForm* clone() const=0;

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

};

class TF_verbatim : public ToplevelForm {
public:      // data
  string code;

public:      // funcs
  TF_verbatim(string _code) : ToplevelForm(), code(_code) {
  }
  virtual ~TF_verbatim();

  virtual Kind kind() const { return TF_VERBATIM; }
  enum { TYPE_TAG = TF_VERBATIM };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual TF_verbatim *clone() const;

};

class TF_impl_verbatim : public ToplevelForm {
public:      // data
  string code;

public:      // funcs
  TF_impl_verbatim(string _code) : ToplevelForm(), code(_code) {
  }
  virtual ~TF_impl_verbatim();

  virtual Kind kind() const { return TF_IMPL_VERBATIM; }
  enum { TYPE_TAG = TF_IMPL_VERBATIM };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual TF_impl_verbatim *clone() const;

};

class TF_class : public ToplevelForm {
public:      // data
  ASTClass *super;
  ASTList <ASTClass > ctors;

public:      // funcs
  TF_class(ASTClass *_super, ASTList <ASTClass > *_ctors) : ToplevelForm(), super(_super), ctors(_ctors) {
  }
  virtual ~TF_class();

  virtual Kind kind() const { return TF_CLASS; }
  enum { TYPE_TAG = TF_CLASS };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual TF_class *clone() const;

  public:  bool hasChildren() const { return ctors.isNotEmpty(); };
};

class TF_option : public ToplevelForm {
public:      // data
  string name;
  ASTList <string > args;

public:      // funcs
  TF_option(string _name, ASTList <string > *_args) : ToplevelForm(), name(_name), args(_args) {
  }
  virtual ~TF_option();

  virtual Kind kind() const { return TF_OPTION; }
  enum { TYPE_TAG = TF_OPTION };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual TF_option *clone() const;

};

class TF_custom : public ToplevelForm {
public:      // data
  CustomCode *cust;

public:      // funcs
  TF_custom(CustomCode *_cust) : ToplevelForm(), cust(_cust) {
  }
  virtual ~TF_custom();

  virtual Kind kind() const { return TF_CUSTOM; }
  enum { TYPE_TAG = TF_CUSTOM };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual TF_custom *clone() const;

};

class TF_enum : public ToplevelForm {
public:      // data
  string name;
  ASTList <string > enumerators;

public:      // funcs
  TF_enum(string _name, ASTList <string > *_enumerators) : ToplevelForm(), name(_name), enumerators(_enumerators) {
  }
  virtual ~TF_enum();

  virtual Kind kind() const { return TF_ENUM; }
  enum { TYPE_TAG = TF_ENUM };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual TF_enum *clone() const;

};



// *** DO NOT EDIT ***
class ASTClass {
public:      // data
  string name;
  ASTList <CtorArg > args;
  ASTList <CtorArg > lastArgs;
  ASTList <BaseClass > bases;
  ASTList <Annotation > decls;

public:      // funcs
  ASTClass(string _name, ASTList <CtorArg > *_args, ASTList <CtorArg > *_lastArgs, ASTList <BaseClass > *_bases, ASTList <Annotation > *_decls) : name(_name), args(_args), lastArgs(_lastArgs), bases(_bases), decls(_decls) {
  }
  ~ASTClass();

  char const *kindName() const { return "ASTClass"; }

  ASTClass *clone() const;

  void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  public:  string classKindName() const;
};



// *** DO NOT EDIT ***

  // specifies what kind of userdecl this is; pub/priv/prot are uninterpreted
  // class members with the associated access control; ctor and dtor are
  // code to be inserted into the ctor or dtor, respectively
  enum AccessCtl {
    AC_PUBLIC,      // access
    AC_PRIVATE,     //   control
    AC_PROTECTED,   //     keywords
    AC_CTOR,        // insert into ctor
    AC_DTOR,        // insert into dtor
    AC_PUREVIRT,    // declare pure virtual in superclass, and impl in subclass
    NUM_ACCESSCTLS
  };

  // map the enum value to a string like "public"
  string toString(AccessCtl acc);      // defined in ast.cc

// *** DO NOT EDIT ***
class AccessMod {
public:      // data
  AccessCtl acc;
  ASTList <string > mods;

public:      // funcs
  AccessMod(AccessCtl _acc, ASTList <string > *_mods) : acc(_acc), mods(_mods) {
  }
  ~AccessMod();

  char const *kindName() const { return "AccessMod"; }

  AccessMod *clone() const;

  void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  public:  bool hasMod(char const *mod) const;
  public:  bool hasModPrefix(char const *mod) const;
  public:  string getModSuffixFromPrefix(char const *mod) const;
};



// *** DO NOT EDIT ***
class Annotation {
public:      // data

public:      // funcs
  Annotation() {
  }
  virtual ~Annotation();

  enum Kind { USERDECL, CUSTOMCODE, NUM_KINDS };
  virtual Kind kind() const = 0;

  static char const * const kindNames[NUM_KINDS];
  char const *kindName() const { return kindNames[kind()]; }

  DECL_AST_DOWNCASTS(UserDecl, USERDECL)
  DECL_AST_DOWNCASTS(CustomCode, CUSTOMCODE)

  virtual Annotation* clone() const=0;

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

};

class UserDecl : public Annotation {
public:      // data
  AccessMod *amod;
  string code;
  string init;

public:      // funcs
  UserDecl(AccessMod *_amod, string _code, string _init) : Annotation(), amod(_amod), code(_code), init(_init) {
  }
  virtual ~UserDecl();

  virtual Kind kind() const { return USERDECL; }
  enum { TYPE_TAG = USERDECL };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual UserDecl *clone() const;

  public:  AccessCtl access() const { return amod->acc; };
};

class CustomCode : public Annotation {
public:      // data
  string qualifier;
  string code;

public:      // funcs
  CustomCode(string _qualifier, string _code) : Annotation(), qualifier(_qualifier), code(_code) {
     used=false;
  }
  virtual ~CustomCode();

  virtual Kind kind() const { return CUSTOMCODE; }
  enum { TYPE_TAG = CUSTOMCODE };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual CustomCode *clone() const;

  public:  bool used;
};



// *** DO NOT EDIT ***
class CtorArg {
public:      // data
  bool isOwner;
  string type;
  string name;
  string defaultValue;

public:      // funcs
  CtorArg(bool _isOwner, string _type, string _name, string _defaultValue) : isOwner(_isOwner), type(_type), name(_name), defaultValue(_defaultValue) {
  }
  ~CtorArg();

  char const *kindName() const { return "CtorArg"; }

  CtorArg *clone() const;

  void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

};



// *** DO NOT EDIT ***
class BaseClass {
public:      // data
  AccessCtl access;
  string name;

public:      // funcs
  BaseClass(AccessCtl _access, string _name) : access(_access), name(_name) {
  }
  ~BaseClass();

  char const *kindName() const { return "BaseClass"; }

  BaseClass *clone() const;

  void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

};




#endif // AST_AST_H
