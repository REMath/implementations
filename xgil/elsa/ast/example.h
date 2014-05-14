// example.h
// *** DO NOT EDIT ***
// generated automatically by astgen, from example.ast

#ifndef EXAMPLE_H
#define EXAMPLE_H

#include "asthelp.h"        // helpers for generated code
#include "sobjset.h"        // SObjSet

// fwd decls
class Node;
class NodeList;
class AnotherList;
class Super;
class Sub1;
class Sub2;
class SubWithDefault;
class Sub3;
class UsesEnum;
class UE_a;
class UE_b;
class InheritsSomething;
class IS_a;
class IS_b;
class IS_c;
class IS_d;
class HasLastArgs;
class Hla1;
class Hla2;
class SomethingElse;


// visitor interface class
class ExampleVisitor;

// delegator-visitor interface class
class ExampleDVisitor;

class ExampleMVisitor;

enum AnEnum {
  AE_ONE,
  AE_TWO,
  AE_THREE,
};

char const *toString(AnEnum);


enum AnotherEnum {
  anotherone,
  anothertwo,
  anotherthree,
};

char const *toString(AnotherEnum);


// *** DO NOT EDIT ***

  // first verbatim in example.ast








// *** DO NOT EDIT ***
class Node {
public:      // data
  int x;
  int y;

public:      // funcs
  Node(int _x, int _y) : x(_x), y(_y), w( 3), listptr( NULL) {
     next=NULL;
  }
  ~Node();

  char const *kindName() const { return "Node"; }

  Node *clone() const;

  void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  void xmlPrint(ostream &os, int indent) const;
  void traverse(ExampleVisitor &vis);

  void gdb() const;

  public:  Node *next;
  public:  int w ;   // field
  public:  FakeList<Node> *listptr ;
};



// *** DO NOT EDIT ***
class NodeList {
public:      // data
  FakeList <Node >* list;

public:      // funcs
  NodeList(FakeList <Node >* _list) : list(_list) {
  }
  ~NodeList();

  char const *kindName() const { return "NodeList"; }

  NodeList *clone() const;

  void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  void xmlPrint(ostream &os, int indent) const;
  void traverse(ExampleVisitor &vis);

  void gdb() const;

};



// *** DO NOT EDIT ***
class AnotherList {
public:      // data
  ASTList <Node > list2;
  LocString str;

public:      // funcs
  AnotherList(ASTList <Node > *_list2, LocString *_str) : list2(_list2), str(_str) {
  }
  ~AnotherList();

  char const *kindName() const { return "AnotherList"; }

  AnotherList *clone() const;

  void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  void xmlPrint(ostream &os, int indent) const;
  void traverse(ExampleVisitor &vis);

  void gdb() const;

};



// *** DO NOT EDIT ***
class Super {
public:      // data
  int x;

public:      // funcs
  Super(int _x) : x(_x), p( NULL) {
  }
  virtual ~Super();

  enum Kind { SUB1, SUB2, SUBWITHDEFAULT, SUB3, NUM_KINDS };
  virtual Kind kind() const = 0;

  static char const * const kindNames[NUM_KINDS];
  char const *kindName() const { return kindNames[kind()]; }

  DECL_AST_DOWNCASTS(Sub1, SUB1)
  DECL_AST_DOWNCASTS(Sub2, SUB2)
  DECL_AST_DOWNCASTS(SubWithDefault, SUBWITHDEFAULT)
  DECL_AST_DOWNCASTS(Sub3, SUB3)

  virtual Super* clone() const=0;

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  void gdb() const;

  protected: virtual  int foo();   // virtual
  public:  int *p ;   // owner
  public: virtual  int onlyInSubclasses()  =  0;   // virtual
  public: virtual  int everywhere();   // virtual
};

class Sub1 : public Super {
public:      // data
  int y;

public:      // funcs
  Sub1(int _x, int _y) : Super(_x), y(_y) {
  }
  virtual ~Sub1();

  virtual Kind kind() const { return SUB1; }
  enum { TYPE_TAG = SUB1 };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual Sub1 *clone() const;

  protected: virtual  int foo();
  public: virtual  int onlyInSubclasses() ;
  public: virtual  int everywhere();
};

class Sub2 : public Super {
public:      // data
  int z;

public:      // funcs
  Sub2(int _x, int _z) : Super(_x), z(_z) {
  }
  virtual ~Sub2();

  virtual Kind kind() const { return SUB2; }
  enum { TYPE_TAG = SUB2 };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual Sub2 *clone() const;

  protected: virtual  int foo();
  public: virtual  int onlyInSubclasses() ;
  public: virtual  int everywhere();
};

class SubWithDefault : public Super {
public:      // data
  int q;

public:      // funcs
  SubWithDefault(int _x, int _q = 5) : Super(_x), q(_q) {
  }
  virtual ~SubWithDefault();

  virtual Kind kind() const { return SUBWITHDEFAULT; }
  enum { TYPE_TAG = SUBWITHDEFAULT };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual SubWithDefault *clone() const;

  protected: virtual  int foo();
  public: virtual  int onlyInSubclasses() ;
  public: virtual  int everywhere();
};

class Sub3 : public Super {
public:      // data
  Super *s1;
  Sub2 *s2;

public:      // funcs
  Sub3(int _x, Super *_s1, Sub2 *_s2) : Super(_x), s1(_s1), s2(_s2) {
  }
  virtual ~Sub3();

  virtual Kind kind() const { return SUB3; }
  enum { TYPE_TAG = SUB3 };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual Sub3 *clone() const;

  protected: virtual  int foo();
  public: virtual  int onlyInSubclasses() ;
  public: virtual  int everywhere();
};





// *** DO NOT EDIT ***
class UsesEnum {
public:      // data

public:      // funcs
  UsesEnum() {
  }
  virtual ~UsesEnum();

  enum Kind { UE_A, UE_B, NUM_KINDS };
  virtual Kind kind() const = 0;

  static char const * const kindNames[NUM_KINDS];
  char const *kindName() const { return kindNames[kind()]; }

  DECL_AST_DOWNCASTS(UE_a, UE_A)
  DECL_AST_DOWNCASTS(UE_b, UE_B)

  virtual UsesEnum* clone() const=0;

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  void gdb() const;

};

class UE_a : public UsesEnum {
public:      // data
  AnEnum x;

public:      // funcs
  UE_a(AnEnum _x) : UsesEnum(), x(_x) {
  }
  virtual ~UE_a();

  virtual Kind kind() const { return UE_A; }
  enum { TYPE_TAG = UE_A };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual UE_a *clone() const;

};

class UE_b : public UsesEnum {
public:      // data
  int y;

public:      // funcs
  UE_b(int _y) : UsesEnum(), y(_y) {
  }
  virtual ~UE_b();

  virtual Kind kind() const { return UE_B; }
  enum { TYPE_TAG = UE_B };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual UE_b *clone() const;

};



// *** DO NOT EDIT ***

  class Base1 {};
  class Base2 {};
  class Base3 {};

// *** DO NOT EDIT ***
class InheritsSomething : public Base1 {
public:      // data

public:      // funcs
  InheritsSomething() {
  }
  virtual ~InheritsSomething();

  enum Kind { IS_A, IS_B, IS_C, IS_D, NUM_KINDS };
  virtual Kind kind() const = 0;

  static char const * const kindNames[NUM_KINDS];
  char const *kindName() const { return kindNames[kind()]; }

  DECL_AST_DOWNCASTS(IS_a, IS_A)
  DECL_AST_DOWNCASTS(IS_b, IS_B)
  DECL_AST_DOWNCASTS(IS_c, IS_C)
  DECL_AST_DOWNCASTS(IS_d, IS_D)

  virtual InheritsSomething* clone() const=0;

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  void gdb() const;

};

class IS_a : public InheritsSomething, public Base2 {
public:      // data
  int z;

public:      // funcs
  IS_a(int _z) : InheritsSomething(), z(_z) {
  }
  virtual ~IS_a();

  virtual Kind kind() const { return IS_A; }
  enum { TYPE_TAG = IS_A };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual IS_a *clone() const;

};

class IS_b : public InheritsSomething, public Base3 {
public:      // data
  int q;

public:      // funcs
  IS_b(int _q) : InheritsSomething(), q(_q) {
  }
  virtual ~IS_b();

  virtual Kind kind() const { return IS_B; }
  enum { TYPE_TAG = IS_B };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual IS_b *clone() const;

  public:  float f;
};

class IS_c : public InheritsSomething {
public:      // data
  int ret;

public:      // funcs
  IS_c(int _ret) : InheritsSomething(), ret(_ret) {
  }
  virtual ~IS_c();

  virtual Kind kind() const { return IS_C; }
  enum { TYPE_TAG = IS_C };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual IS_c *clone() const;

};

class IS_d : public InheritsSomething {
public:      // data
  UsesEnum *ret;

public:      // funcs
  IS_d(UsesEnum *_ret) : InheritsSomething(), ret(_ret) {
  }
  virtual ~IS_d();

  virtual Kind kind() const { return IS_D; }
  enum { TYPE_TAG = IS_D };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual IS_d *clone() const;

};



// *** DO NOT EDIT ***
class HasLastArgs {
public:      // data
  int x;
  int w;

public:      // funcs
  HasLastArgs(int _x, int _w) : x(_x), w(_w) {
  }
  virtual ~HasLastArgs();

  enum Kind { HLA1, HLA2, NUM_KINDS };
  virtual Kind kind() const = 0;

  static char const * const kindNames[NUM_KINDS];
  char const *kindName() const { return kindNames[kind()]; }

  DECL_AST_DOWNCASTS(Hla1, HLA1)
  DECL_AST_DOWNCASTS(Hla2, HLA2)

  virtual HasLastArgs* clone() const=0;

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  void gdb() const;

};

class Hla1 : public HasLastArgs {
public:      // data
  int y;

public:      // funcs
  Hla1(int _x, int _y, int _w) : HasLastArgs(_x, _w), y(_y) {
  }
  virtual ~Hla1();

  virtual Kind kind() const { return HLA1; }
  enum { TYPE_TAG = HLA1 };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual Hla1 *clone() const;

};

class Hla2 : public HasLastArgs {
public:      // data
  int y;
  int z;

public:      // funcs
  Hla2(int _x, int _y, int _z, int _w) : HasLastArgs(_x, _w), y(_y), z(_z) {
  }
  virtual ~Hla2();

  virtual Kind kind() const { return HLA2; }
  enum { TYPE_TAG = HLA2 };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  virtual void xmlPrint(ostream &os, int indent) const;
  virtual void traverse(ExampleVisitor &vis);

  virtual Hla2 *clone() const;

};



// *** DO NOT EDIT ***
class SomethingElse {
public:      // data
  int x;
  int y;

public:      // funcs
  SomethingElse(int _x, int _y) : x(_x), y(_y) {
  }
  ~SomethingElse();

  char const *kindName() const { return "SomethingElse"; }

  SomethingElse *clone() const;

  void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;
  void xmlPrint(ostream &os, int indent) const;
  void traverse(ExampleVisitor &vis);

  void gdb() const;

};



// the visitor interface class
class ExampleVisitor {

public:
  int someVisitorField;

private:     // disallowed, not implemented
  ExampleVisitor(ExampleVisitor&);
  void operator= (ExampleVisitor&);

public:      // funcs
  ExampleVisitor() { someVisitorField = 0; }
  virtual ~ExampleVisitor();   // silence gcc warning...

  virtual bool visitNode(Node *obj);
  virtual void postvisitNode(Node *obj);
  virtual bool visitNodeList(NodeList *obj);
  virtual void postvisitNodeList(NodeList *obj);
  virtual bool visitAnotherList(AnotherList *obj);
  virtual void postvisitAnotherList(AnotherList *obj);
  virtual bool visitSuper(Super *obj);
  virtual void postvisitSuper(Super *obj);
  virtual bool visitUsesEnum(UsesEnum *obj);
  virtual void postvisitUsesEnum(UsesEnum *obj);
  virtual bool visitInheritsSomething(InheritsSomething *obj);
  virtual void postvisitInheritsSomething(InheritsSomething *obj);
  virtual bool visitHasLastArgs(HasLastArgs *obj);
  virtual void postvisitHasLastArgs(HasLastArgs *obj);
  virtual bool visitSomethingElse(SomethingElse *obj);
  virtual void postvisitSomethingElse(SomethingElse *obj);

  // List 'classes'
  virtual bool visitList_NodeList_list(FakeList<Node>*);
  virtual void postvisitList_NodeList_list(FakeList<Node>*);
  virtual bool visitList_AnotherList_list2(ASTList<Node>*);
  virtual void postvisitList_AnotherList_list2(ASTList<Node>*);
  virtual bool visitListItem_NodeList_list(Node*);
  virtual void postvisitListItem_NodeList_list(Node*);
  virtual bool visitListItem_AnotherList_list2(Node*);
  virtual void postvisitListItem_AnotherList_list2(Node*);
};

// the delegator-visitor interface class
class ExampleDVisitor : public ExampleVisitor {
protected:   // data
  ExampleVisitor *client;      // visitor to delegate to
  bool ensureOneVisit;                // check for visiting at most once?
  SObjSet<void*> wasVisitedASTNodes;  // set of visited nodes
  SObjSet<void*> wasVisitedList_ASTListNodes; // set of visited ASTLists
  SObjSet<void*> wasVisitedList_FakeListNodes; // set of visited FakeLists

protected:   // funcs
  bool wasVisitedAST(void *ast);
  bool wasVisitedList_ASTList(void *ast);
  bool wasVisitedList_FakeList(void *ast);

public:      // funcs
  explicit ExampleDVisitor(ExampleVisitor *client0 = NULL, bool ensureOneVisit0 = true)
    : client(client0)
    , ensureOneVisit(ensureOneVisit0)
  {}

  virtual bool visitNode(Node *obj);
  virtual void postvisitNode(Node *obj);
  virtual bool visitNodeList(NodeList *obj);
  virtual void postvisitNodeList(NodeList *obj);
  virtual bool visitAnotherList(AnotherList *obj);
  virtual void postvisitAnotherList(AnotherList *obj);
  virtual bool visitSuper(Super *obj);
  virtual void postvisitSuper(Super *obj);
  virtual bool visitUsesEnum(UsesEnum *obj);
  virtual void postvisitUsesEnum(UsesEnum *obj);
  virtual bool visitInheritsSomething(InheritsSomething *obj);
  virtual void postvisitInheritsSomething(InheritsSomething *obj);
  virtual bool visitHasLastArgs(HasLastArgs *obj);
  virtual void postvisitHasLastArgs(HasLastArgs *obj);
  virtual bool visitSomethingElse(SomethingElse *obj);
  virtual void postvisitSomethingElse(SomethingElse *obj);

  // List 'classes'
  virtual bool visitList_NodeList_list(FakeList<Node>*);
  virtual void postvisitList_NodeList_list(FakeList<Node>*);
  virtual bool visitList_AnotherList_list2(ASTList<Node>*);
  virtual void postvisitList_AnotherList_list2(ASTList<Node>*);
  virtual bool visitListItem_NodeList_list(Node*);
  virtual void postvisitListItem_NodeList_list(Node*);
  virtual bool visitListItem_AnotherList_list2(Node*);
  virtual void postvisitListItem_AnotherList_list2(Node*);
};

// the modification visitor interface class
class ExampleMVisitor {
private:     // disallowed, not implemented
  ExampleMVisitor(ExampleMVisitor&);
  void operator= (ExampleMVisitor&);

public:      // funcs
  ExampleMVisitor() {}
  virtual ~ExampleMVisitor();   // silence gcc warning...

  virtual bool visitNode(Node *&obj);
  void mtraverse(Node *&obj);
  virtual bool visitNodeList(NodeList *&obj);
  void mtraverse(NodeList *&obj);
  virtual bool visitAnotherList(AnotherList *&obj);
  void mtraverse(AnotherList *&obj);
  virtual bool visitSuper(Super *&obj);
  void mtraverse(Super *&obj);
  virtual bool visitUsesEnum(UsesEnum *&obj);
  void mtraverse(UsesEnum *&obj);
  virtual bool visitInheritsSomething(InheritsSomething *&obj);
  void mtraverse(InheritsSomething *&obj);
  virtual bool visitHasLastArgs(HasLastArgs *&obj);
  void mtraverse(HasLastArgs *&obj);
  virtual bool visitSomethingElse(SomethingElse *&obj);
  void mtraverse(SomethingElse *&obj);
};

#endif // EXAMPLE_H
