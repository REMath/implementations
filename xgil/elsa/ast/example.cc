// example.cc
// *** DO NOT EDIT ***
// generated automatically by astgen, from example.ast

#include "example.h"      // this module


// ------------------ Node -------------------
// *** DO NOT EDIT ***
Node::~Node()
{
}

void Node::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, Node);

  PRINT_GENERIC(x);
  PRINT_GENERIC(y);
  PRINT_GENERIC(w);
}

void Node::gdb() const
  { debugPrint(cout, 0); }

void Node::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(Node);

  XMLPRINT_GENERIC(x);
  XMLPRINT_GENERIC(y);
  XMLPRINT_FOOTER(Node);
}

Node *Node::clone() const
{
  Node *ret = new Node(
    x,
    y
  );
  return ret;
}


// ------------------ NodeList -------------------
// *** DO NOT EDIT ***
NodeList::~NodeList()
{
}

void NodeList::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, NodeList);

  PRINT_FAKE_LIST(Node, list);
}

void NodeList::gdb() const
  { debugPrint(cout, 0); }

void NodeList::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(NodeList);

  XMLPRINT_FAKE_LIST(Node, list);
  XMLPRINT_FOOTER(NodeList);
}

NodeList *NodeList::clone() const
{
  NodeList *ret = new NodeList(
    cloneFakeList(list)
  );
  return ret;
}


// ------------------ AnotherList -------------------
// *** DO NOT EDIT ***
AnotherList::~AnotherList()
{
  list2.deleteAll();
}

void AnotherList::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, AnotherList);

  PRINT_LIST(Node, list2);
  PRINT_GENERIC(str);
}

void AnotherList::gdb() const
  { debugPrint(cout, 0); }

void AnotherList::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(AnotherList);

  XMLPRINT_LIST(Node, list2);
  XMLPRINT_GENERIC(str);
  XMLPRINT_FOOTER(AnotherList);
}

AnotherList *AnotherList::clone() const
{
  AnotherList *ret = new AnotherList(
    cloneASTList(list2),
    str.clone()
  );
  return ret;
}


// ------------------ Super -------------------
// *** DO NOT EDIT ***
Super::~Super()
{
  delete p;
}

char const * const Super::kindNames[Super::NUM_KINDS] = {
  "Sub1",
  "Sub2",
  "SubWithDefault",
  "Sub3",
};

void Super::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_GENERIC(x);
}

void Super::gdb() const
  { debugPrint(cout, 0); }

void Super::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_GENERIC(x);
}

DEFN_AST_DOWNCASTS(Super, Sub1, SUB1)

Sub1::~Sub1()
{
}

void Sub1::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, Sub1);

  Super::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(y);
}

void Sub1::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(Sub1);

  Super::xmlPrint(os, indent);

  XMLPRINT_GENERIC(y);
  XMLPRINT_FOOTER(Sub1);

}

Sub1 *Sub1::clone() const
{
  Sub1 *ret = new Sub1(
    x,
    y
  );
  return ret;
}

DEFN_AST_DOWNCASTS(Super, Sub2, SUB2)

Sub2::~Sub2()
{
}

void Sub2::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, Sub2);

  Super::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(z);
}

void Sub2::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(Sub2);

  Super::xmlPrint(os, indent);

  XMLPRINT_GENERIC(z);
  XMLPRINT_FOOTER(Sub2);

}

Sub2 *Sub2::clone() const
{
  Sub2 *ret = new Sub2(
    x,
    z
  );
  return ret;
}

DEFN_AST_DOWNCASTS(Super, SubWithDefault, SUBWITHDEFAULT)

SubWithDefault::~SubWithDefault()
{
}

void SubWithDefault::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, SubWithDefault);

  Super::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(q);
}

void SubWithDefault::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(SubWithDefault);

  Super::xmlPrint(os, indent);

  XMLPRINT_GENERIC(q);
  XMLPRINT_FOOTER(SubWithDefault);

}

SubWithDefault *SubWithDefault::clone() const
{
  SubWithDefault *ret = new SubWithDefault(
    x,
    q
  );
  return ret;
}

DEFN_AST_DOWNCASTS(Super, Sub3, SUB3)

Sub3::~Sub3()
{
  delete s1;
  delete s2;
}

void Sub3::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, Sub3);

  Super::debugPrint(os, indent, subtreeName);

  PRINT_SUBTREE(s1);
  PRINT_SUBTREE(s2);
}

void Sub3::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(Sub3);

  Super::xmlPrint(os, indent);

  XMLPRINT_SUBTREE(s1);
  XMLPRINT_SUBTREE(s2);
  XMLPRINT_FOOTER(Sub3);

}

Sub3 *Sub3::clone() const
{
  Sub3 *ret = new Sub3(
    x,
    s1? s1->clone() : NULL,
    s2? s2->clone() : NULL
  );
  return ret;
}


char const *toString(AnEnum x)
{
  static char const * const map[] = {
    "AE_ONE",
    "AE_TWO",
    "AE_THREE",
  };
  xassert((unsigned)x < TABLESIZE(map));
  return map[x];
};


char const *toString(AnotherEnum x)
{
  static char const * const map[] = {
    "anotherone",
    "anothertwo",
    "anotherthree",
  };
  xassert((unsigned)x < TABLESIZE(map));
  return map[x];
};


// ------------------ UsesEnum -------------------
// *** DO NOT EDIT ***
UsesEnum::~UsesEnum()
{
}

char const * const UsesEnum::kindNames[UsesEnum::NUM_KINDS] = {
  "UE_a",
  "UE_b",
};

void UsesEnum::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
}

void UsesEnum::gdb() const
  { debugPrint(cout, 0); }

void UsesEnum::xmlPrint(ostream &os, int indent) const
{
}

DEFN_AST_DOWNCASTS(UsesEnum, UE_a, UE_A)

UE_a::~UE_a()
{
}

void UE_a::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, UE_a);

  UsesEnum::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(x);
}

void UE_a::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(UE_a);

  UsesEnum::xmlPrint(os, indent);

  XMLPRINT_GENERIC(x);
  XMLPRINT_FOOTER(UE_a);

}

UE_a *UE_a::clone() const
{
  UE_a *ret = new UE_a(
    x
  );
  return ret;
}

DEFN_AST_DOWNCASTS(UsesEnum, UE_b, UE_B)

UE_b::~UE_b()
{
}

void UE_b::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, UE_b);

  UsesEnum::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(y);
}

void UE_b::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(UE_b);

  UsesEnum::xmlPrint(os, indent);

  XMLPRINT_GENERIC(y);
  XMLPRINT_FOOTER(UE_b);

}

UE_b *UE_b::clone() const
{
  UE_b *ret = new UE_b(
    y
  );
  return ret;
}


// ------------------ InheritsSomething -------------------
// *** DO NOT EDIT ***
InheritsSomething::~InheritsSomething()
{
}

char const * const InheritsSomething::kindNames[InheritsSomething::NUM_KINDS] = {
  "IS_a",
  "IS_b",
  "IS_c",
  "IS_d",
};

void InheritsSomething::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
}

void InheritsSomething::gdb() const
  { debugPrint(cout, 0); }

void InheritsSomething::xmlPrint(ostream &os, int indent) const
{
}

DEFN_AST_DOWNCASTS(InheritsSomething, IS_a, IS_A)

IS_a::~IS_a()
{
}

void IS_a::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, IS_a);

  InheritsSomething::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(z);
}

void IS_a::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(IS_a);

  InheritsSomething::xmlPrint(os, indent);

  XMLPRINT_GENERIC(z);
  XMLPRINT_FOOTER(IS_a);

}

IS_a *IS_a::clone() const
{
  IS_a *ret = new IS_a(
    z
  );
  return ret;
}

DEFN_AST_DOWNCASTS(InheritsSomething, IS_b, IS_B)

IS_b::~IS_b()
{
}

void IS_b::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, IS_b);

  InheritsSomething::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(q);
}

void IS_b::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(IS_b);

  InheritsSomething::xmlPrint(os, indent);

  XMLPRINT_GENERIC(q);
  XMLPRINT_FOOTER(IS_b);

}

IS_b *IS_b::clone() const
{
  IS_b *ret = new IS_b(
    q
  );
  return ret;
}

DEFN_AST_DOWNCASTS(InheritsSomething, IS_c, IS_C)

IS_c::~IS_c()
{
}

void IS_c::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, IS_c);

  InheritsSomething::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(ret);
}

void IS_c::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(IS_c);

  InheritsSomething::xmlPrint(os, indent);

  XMLPRINT_GENERIC(ret);
  XMLPRINT_FOOTER(IS_c);

}

IS_c *IS_c::clone() const
{
  IS_c *ret = new IS_c(
    this->ret
  );
  return ret;
}

DEFN_AST_DOWNCASTS(InheritsSomething, IS_d, IS_D)

IS_d::~IS_d()
{
  delete ret;
}

void IS_d::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, IS_d);

  InheritsSomething::debugPrint(os, indent, subtreeName);

  PRINT_SUBTREE(ret);
}

void IS_d::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(IS_d);

  InheritsSomething::xmlPrint(os, indent);

  XMLPRINT_SUBTREE(ret);
  XMLPRINT_FOOTER(IS_d);

}

IS_d *IS_d::clone() const
{
  IS_d *ret = new IS_d(
    this->ret? this->ret->clone() : NULL
  );
  return ret;
}


// ------------------ HasLastArgs -------------------
// *** DO NOT EDIT ***
HasLastArgs::~HasLastArgs()
{
}

char const * const HasLastArgs::kindNames[HasLastArgs::NUM_KINDS] = {
  "Hla1",
  "Hla2",
};

void HasLastArgs::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_GENERIC(x);
  // (lastArgs are printed by subclasses)
}

void HasLastArgs::gdb() const
  { debugPrint(cout, 0); }

void HasLastArgs::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_GENERIC(x);
}

DEFN_AST_DOWNCASTS(HasLastArgs, Hla1, HLA1)

Hla1::~Hla1()
{
}

void Hla1::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, Hla1);

  HasLastArgs::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(y);
  PRINT_GENERIC(w);
}

void Hla1::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(Hla1);

  HasLastArgs::xmlPrint(os, indent);

  XMLPRINT_GENERIC(y);
  XMLPRINT_GENERIC(w);
  XMLPRINT_FOOTER(Hla1);

}

Hla1 *Hla1::clone() const
{
  Hla1 *ret = new Hla1(
    x,
    y,
    w
  );
  return ret;
}

DEFN_AST_DOWNCASTS(HasLastArgs, Hla2, HLA2)

Hla2::~Hla2()
{
}

void Hla2::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, Hla2);

  HasLastArgs::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(y);
  PRINT_GENERIC(z);
  PRINT_GENERIC(w);
}

void Hla2::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(Hla2);

  HasLastArgs::xmlPrint(os, indent);

  XMLPRINT_GENERIC(y);
  XMLPRINT_GENERIC(z);
  XMLPRINT_GENERIC(w);
  XMLPRINT_FOOTER(Hla2);

}

Hla2 *Hla2::clone() const
{
  Hla2 *ret = new Hla2(
    x,
    y,
    z,
    w
  );
  return ret;
}


// ------------------ SomethingElse -------------------
// *** DO NOT EDIT ***
SomethingElse::~SomethingElse()
{
}

void SomethingElse::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, SomethingElse);

  PRINT_GENERIC(x);
  PRINT_GENERIC(y);
}

void SomethingElse::gdb() const
  { debugPrint(cout, 0); }

void SomethingElse::xmlPrint(ostream &os, int indent) const
{
  XMLPRINT_HEADER(SomethingElse);

  XMLPRINT_GENERIC(x);
  XMLPRINT_GENERIC(y);
  XMLPRINT_FOOTER(SomethingElse);
}

SomethingElse *SomethingElse::clone() const
{
   return new SomethingElse(x,y); /*my own clone() code*/ ;
}




// ---------------------- ExampleVisitor ---------------------
// default no-op visitor
ExampleVisitor::~ExampleVisitor() {}
bool ExampleVisitor::visitNode(Node *obj) { return true; }
void ExampleVisitor::postvisitNode(Node *obj) {}
bool ExampleVisitor::visitNodeList(NodeList *obj) { return true; }
void ExampleVisitor::postvisitNodeList(NodeList *obj) {}
bool ExampleVisitor::visitAnotherList(AnotherList *obj) { return true; }
void ExampleVisitor::postvisitAnotherList(AnotherList *obj) {}
bool ExampleVisitor::visitSuper(Super *obj) { return true; }
void ExampleVisitor::postvisitSuper(Super *obj) {}
bool ExampleVisitor::visitUsesEnum(UsesEnum *obj) { return true; }
void ExampleVisitor::postvisitUsesEnum(UsesEnum *obj) {}
bool ExampleVisitor::visitInheritsSomething(InheritsSomething *obj) { return true; }
void ExampleVisitor::postvisitInheritsSomething(InheritsSomething *obj) {}
bool ExampleVisitor::visitHasLastArgs(HasLastArgs *obj) { return true; }
void ExampleVisitor::postvisitHasLastArgs(HasLastArgs *obj) {}
bool ExampleVisitor::visitSomethingElse(SomethingElse *obj) { return true; }
void ExampleVisitor::postvisitSomethingElse(SomethingElse *obj) {}

// List 'classes'
bool ExampleVisitor::visitList_NodeList_list(FakeList<Node>*) { return true; }
void ExampleVisitor::postvisitList_NodeList_list(FakeList<Node>*) {}
bool ExampleVisitor::visitList_AnotherList_list2(ASTList<Node>*) { return true; }
void ExampleVisitor::postvisitList_AnotherList_list2(ASTList<Node>*) {}
bool ExampleVisitor::visitListItem_NodeList_list(Node*) { return true; }
void ExampleVisitor::postvisitListItem_NodeList_list(Node*) {}
bool ExampleVisitor::visitListItem_AnotherList_list2(Node*) { return true; }
void ExampleVisitor::postvisitListItem_AnotherList_list2(Node*) {}


void Node::traverse(ExampleVisitor &vis)
{
  if (!vis.visitNode(this)) { return; }

   next->traverse(vis); ;
  vis.postvisitNode(this);
}

void NodeList::traverse(ExampleVisitor &vis)
{
  if (!vis.visitNodeList(this)) { return; }

  if (vis.visitList_NodeList_list(list)) {
    FAKELIST_FOREACH_NC(Node, list, iter) {
      if (vis.visitListItem_NodeList_list(iter)) {
        iter->traverse(vis);
        vis.postvisitListItem_NodeList_list(iter);
      }
    }
    vis.postvisitList_NodeList_list(list);
  }
  vis.postvisitNodeList(this);
}

void AnotherList::traverse(ExampleVisitor &vis)
{
  if (!vis.visitAnotherList(this)) { return; }

  if (vis.visitList_AnotherList_list2(&list2)) {
    FOREACH_ASTLIST_NC(Node, list2, iter) {
      if (vis.visitListItem_AnotherList_list2(iter.data())) {
        iter.data()->traverse(vis);
        vis.postvisitListItem_AnotherList_list2(iter.data());
      }
    }
    vis.postvisitList_AnotherList_list2(&list2);
  }
  vis.postvisitAnotherList(this);
}

void Super::traverse(ExampleVisitor &vis)
{
  // no 'visit' because it's handled by subclasses

  // no 'postvisit' either
}

void Sub1::traverse(ExampleVisitor &vis)
{
  if (!vis.visitSuper(this)) { return; }

  Super::traverse(vis);

  vis.postvisitSuper(this);
}

void Sub2::traverse(ExampleVisitor &vis)
{
  if (!vis.visitSuper(this)) { return; }

  Super::traverse(vis);

  vis.postvisitSuper(this);
}

void SubWithDefault::traverse(ExampleVisitor &vis)
{
  if (!vis.visitSuper(this)) { return; }

  Super::traverse(vis);

  vis.postvisitSuper(this);
}

void Sub3::traverse(ExampleVisitor &vis)
{
  if (!vis.visitSuper(this)) { return; }

  Super::traverse(vis);

  if (s1) { s1->traverse(vis); }
  if (s2) { s2->traverse(vis); }
  vis.postvisitSuper(this);
}

void UsesEnum::traverse(ExampleVisitor &vis)
{
  // no 'visit' because it's handled by subclasses

  // no 'postvisit' either
}

void UE_a::traverse(ExampleVisitor &vis)
{
  if (!vis.visitUsesEnum(this)) { return; }

  UsesEnum::traverse(vis);

  vis.postvisitUsesEnum(this);
}

void UE_b::traverse(ExampleVisitor &vis)
{
  if (!vis.visitUsesEnum(this)) { return; }

  UsesEnum::traverse(vis);

  vis.postvisitUsesEnum(this);
}

void InheritsSomething::traverse(ExampleVisitor &vis)
{
  // no 'visit' because it's handled by subclasses

  // no 'postvisit' either
}

void IS_a::traverse(ExampleVisitor &vis)
{
  if (!vis.visitInheritsSomething(this)) { return; }

  InheritsSomething::traverse(vis);

  vis.postvisitInheritsSomething(this);
}

void IS_b::traverse(ExampleVisitor &vis)
{
  if (!vis.visitInheritsSomething(this)) { return; }

  InheritsSomething::traverse(vis);

  vis.postvisitInheritsSomething(this);
}

void IS_c::traverse(ExampleVisitor &vis)
{
  if (!vis.visitInheritsSomething(this)) { return; }

  InheritsSomething::traverse(vis);

  vis.postvisitInheritsSomething(this);
}

void IS_d::traverse(ExampleVisitor &vis)
{
  if (!vis.visitInheritsSomething(this)) { return; }

  InheritsSomething::traverse(vis);

  if (ret) { ret->traverse(vis); }
  vis.postvisitInheritsSomething(this);
}

void HasLastArgs::traverse(ExampleVisitor &vis)
{
  // no 'visit' because it's handled by subclasses

  // no 'postvisit' either
}

void Hla1::traverse(ExampleVisitor &vis)
{
  if (!vis.visitHasLastArgs(this)) { return; }

  HasLastArgs::traverse(vis);

  vis.postvisitHasLastArgs(this);
}

void Hla2::traverse(ExampleVisitor &vis)
{
  if (!vis.visitHasLastArgs(this)) { return; }

  HasLastArgs::traverse(vis);

  vis.postvisitHasLastArgs(this);
}

void SomethingElse::traverse(ExampleVisitor &vis)
{
  if (!vis.visitSomethingElse(this)) { return; }

  vis.postvisitSomethingElse(this);
}


// ---------------------- ExampleDVisitor ---------------------
bool ExampleDVisitor::wasVisitedAST(void *ast)
{
  // do not bother to check if the user does not want us to
  if (!ensureOneVisit) {
    return false;
  }

  if (!ast) {return false;} // avoid NULL; actually happens for FakeLists
  if (wasVisitedASTNodes.contains(ast)) {
    return true;
  } else {
    wasVisitedASTNodes.add(ast);
    return false;
  }
}

bool ExampleDVisitor::wasVisitedList_ASTList(void *ast)
{
  // do not bother to check if the user does not want us to
  if (!ensureOneVisit) {
    return false;
  }

  if (!ast) {return false;} // avoid NULL; actually happens for FakeLists
  if (wasVisitedList_ASTListNodes.contains(ast)) {
    return true;
  } else {
    wasVisitedList_ASTListNodes.add(ast);
    return false;
  }
}

bool ExampleDVisitor::wasVisitedList_FakeList(void *ast)
{
  // do not bother to check if the user does not want us to
  if (!ensureOneVisit) {
    return false;
  }

  if (!ast) {return false;} // avoid NULL; actually happens for FakeLists
  if (wasVisitedList_FakeListNodes.contains(ast)) {
    return true;
  } else {
    wasVisitedList_FakeListNodes.add(ast);
    return false;
  }
}

// default no-op delegator-visitor
bool ExampleDVisitor::visitNode(Node *obj) {
  xassert(!wasVisitedAST(obj));
  return client ? client->visitNode(obj) : true;
}
void ExampleDVisitor::postvisitNode(Node *obj) {
  if (client) {
    client->postvisitNode(obj);
  }
}
bool ExampleDVisitor::visitNodeList(NodeList *obj) {
  xassert(!wasVisitedAST(obj));
  return client ? client->visitNodeList(obj) : true;
}
void ExampleDVisitor::postvisitNodeList(NodeList *obj) {
  if (client) {
    client->postvisitNodeList(obj);
  }
}
bool ExampleDVisitor::visitAnotherList(AnotherList *obj) {
  xassert(!wasVisitedAST(obj));
  return client ? client->visitAnotherList(obj) : true;
}
void ExampleDVisitor::postvisitAnotherList(AnotherList *obj) {
  if (client) {
    client->postvisitAnotherList(obj);
  }
}
bool ExampleDVisitor::visitSuper(Super *obj) {
  xassert(!wasVisitedAST(obj));
  return client ? client->visitSuper(obj) : true;
}
void ExampleDVisitor::postvisitSuper(Super *obj) {
  if (client) {
    client->postvisitSuper(obj);
  }
}
bool ExampleDVisitor::visitUsesEnum(UsesEnum *obj) {
  xassert(!wasVisitedAST(obj));
  return client ? client->visitUsesEnum(obj) : true;
}
void ExampleDVisitor::postvisitUsesEnum(UsesEnum *obj) {
  if (client) {
    client->postvisitUsesEnum(obj);
  }
}
bool ExampleDVisitor::visitInheritsSomething(InheritsSomething *obj) {
  xassert(!wasVisitedAST(obj));
  return client ? client->visitInheritsSomething(obj) : true;
}
void ExampleDVisitor::postvisitInheritsSomething(InheritsSomething *obj) {
  if (client) {
    client->postvisitInheritsSomething(obj);
  }
}
bool ExampleDVisitor::visitHasLastArgs(HasLastArgs *obj) {
  xassert(!wasVisitedAST(obj));
  return client ? client->visitHasLastArgs(obj) : true;
}
void ExampleDVisitor::postvisitHasLastArgs(HasLastArgs *obj) {
  if (client) {
    client->postvisitHasLastArgs(obj);
  }
}
bool ExampleDVisitor::visitSomethingElse(SomethingElse *obj) {
  xassert(!wasVisitedAST(obj));
  return client ? client->visitSomethingElse(obj) : true;
}
void ExampleDVisitor::postvisitSomethingElse(SomethingElse *obj) {
  if (client) {
    client->postvisitSomethingElse(obj);
  }
}

// List 'classes'
bool ExampleDVisitor::visitList_NodeList_list(FakeList<Node>* obj) {
  xassert(!wasVisitedList_FakeList(obj));
  return client ? client->visitList_NodeList_list(obj) : true;
}
void ExampleDVisitor::postvisitList_NodeList_list(FakeList<Node>* obj) {
  if (client) {
    client->postvisitList_NodeList_list(obj);
  }
}
bool ExampleDVisitor::visitList_AnotherList_list2(ASTList<Node>* obj) {
  xassert(!wasVisitedList_ASTList(obj));
  return client ? client->visitList_AnotherList_list2(obj) : true;
}
void ExampleDVisitor::postvisitList_AnotherList_list2(ASTList<Node>* obj) {
  if (client) {
    client->postvisitList_AnotherList_list2(obj);
  }
}
bool ExampleDVisitor::visitListItem_NodeList_list(Node *obj) {
  return client ? client->visitListItem_NodeList_list(obj) : true;
}
void ExampleDVisitor::postvisitListItem_NodeList_list(Node *obj) {
  if (client) {
    client->postvisitListItem_NodeList_list(obj);
  }
}
bool ExampleDVisitor::visitListItem_AnotherList_list2(Node *obj) {
  return client ? client->visitListItem_AnotherList_list2(obj) : true;
}
void ExampleDVisitor::postvisitListItem_AnotherList_list2(Node *obj) {
  if (client) {
    client->postvisitListItem_AnotherList_list2(obj);
  }
}


// ---------------------- ExampleMVisitor ---------------------
ExampleMVisitor::~ExampleMVisitor() {}

bool ExampleMVisitor::visitNode(Node *&obj) { return true; }

void ExampleMVisitor::mtraverse(Node *&obj)
{
  if (!visitNode(obj)) { return; }

   mtraverse(obj->next); ;
}


bool ExampleMVisitor::visitNodeList(NodeList *&obj) { return true; }

void ExampleMVisitor::mtraverse(NodeList *&obj)
{
  if (!visitNodeList(obj)) { return; }

  // fakelist mtraversal: obj->list
  {
    Node **iter = (Node**)&(obj->list);
    while (*iter) {
      mtraverse(*iter);
      iter = &( (*iter)->next );
    }
  }
}


bool ExampleMVisitor::visitAnotherList(AnotherList *&obj) { return true; }

void ExampleMVisitor::mtraverse(AnotherList *&obj)
{
  if (!visitAnotherList(obj)) { return; }

  FOREACH_ASTLIST_NC(Node, obj->list2, iter) {
    mtraverse(iter.dataRef());
  }
}


bool ExampleMVisitor::visitSuper(Super *&obj) { return true; }

void ExampleMVisitor::mtraverse(Super *&obj)
{
  if (!visitSuper(obj)) { return; }

  switch (obj->kind()) {
    case Super::SUB1: {
      Sub1 *sub = (Sub1*)obj;
      (void)sub;
      break;
    }
    case Super::SUB2: {
      Sub2 *sub = (Sub2*)obj;
      (void)sub;
      break;
    }
    case Super::SUBWITHDEFAULT: {
      SubWithDefault *sub = (SubWithDefault*)obj;
      (void)sub;
      break;
    }
    case Super::SUB3: {
      Sub3 *sub = (Sub3*)obj;
      (void)sub;
      if (sub->s1) {
        mtraverse(sub->s1);
      }
      if (sub->s2) {
        Super* tmp = sub->s2;
        mtraverse(tmp);
        if (tmp != sub->s2) {
          sub->s2 = tmp->asSub2();
        }
      }
      break;
    }
    default:;
  }
}


bool ExampleMVisitor::visitUsesEnum(UsesEnum *&obj) { return true; }

void ExampleMVisitor::mtraverse(UsesEnum *&obj)
{
  if (!visitUsesEnum(obj)) { return; }

  switch (obj->kind()) {
    case UsesEnum::UE_A: {
      UE_a *sub = (UE_a*)obj;
      (void)sub;
      break;
    }
    case UsesEnum::UE_B: {
      UE_b *sub = (UE_b*)obj;
      (void)sub;
      break;
    }
    default:;
  }
}


bool ExampleMVisitor::visitInheritsSomething(InheritsSomething *&obj) { return true; }

void ExampleMVisitor::mtraverse(InheritsSomething *&obj)
{
  if (!visitInheritsSomething(obj)) { return; }

  switch (obj->kind()) {
    case InheritsSomething::IS_A: {
      IS_a *sub = (IS_a*)obj;
      (void)sub;
      break;
    }
    case InheritsSomething::IS_B: {
      IS_b *sub = (IS_b*)obj;
      (void)sub;
      break;
    }
    case InheritsSomething::IS_C: {
      IS_c *sub = (IS_c*)obj;
      (void)sub;
      break;
    }
    case InheritsSomething::IS_D: {
      IS_d *sub = (IS_d*)obj;
      (void)sub;
      if (sub->ret) {
        mtraverse(sub->ret);
      }
      break;
    }
    default:;
  }
}


bool ExampleMVisitor::visitHasLastArgs(HasLastArgs *&obj) { return true; }

void ExampleMVisitor::mtraverse(HasLastArgs *&obj)
{
  if (!visitHasLastArgs(obj)) { return; }

  switch (obj->kind()) {
    case HasLastArgs::HLA1: {
      Hla1 *sub = (Hla1*)obj;
      (void)sub;
      break;
    }
    case HasLastArgs::HLA2: {
      Hla2 *sub = (Hla2*)obj;
      (void)sub;
      break;
    }
    default:;
  }
}


bool ExampleMVisitor::visitSomethingElse(SomethingElse *&obj) { return true; }

void ExampleMVisitor::mtraverse(SomethingElse *&obj)
{
  if (!visitSomethingElse(obj)) { return; }

}



