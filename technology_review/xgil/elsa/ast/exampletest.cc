// Test printing the example.
// Daniel S. Wilkerson

#include "example.h"
#include "../smbase/astlist.h"
#include "../smbase/objlist.h"
#include "locstr.h"

int main() {
  // **** build the thing
  FakeList<Node> *fl0;          // build in reverse
  Node *n1 = new Node(1,101);
  fl0 = FakeList<Node>::makeList(n1);
  Node *n0 = new Node(0,100);
  fl0 = fl0->prepend(n0);
  NodeList *nl0 = new NodeList(fl0);

  Node *n10 = new Node(10,110);
  Node *n20 = new Node(20,120);
  ASTList<Node> *astl0 = new ASTList<Node>();
  astl0->append(n10);
  astl0->append(n20);
  LocString *loc0 = new LocString(SourceLocation(FileLocation(200,201), new SourceFile("there0")),
                                  "somefilename");
  AnotherList *al0 = new AnotherList(astl0, loc0);

  Super *s3 = new Sub1(3, 103);

  Super *s4 = new Sub2(4, 104);

  // **** render it into xml
  cout << "**************** first" << endl;
  nl0->xmlPrint(cout,0);
  cout << "**************** second" << endl;
  al0->xmlPrint(cout,0);
  cout << "**************** third" << endl;
  s3->xmlPrint(cout,0);
  cout << "**************** fourth" << endl;
  s4->xmlPrint(cout,0);
  cout << "**************** done" << endl;

  return 0;
}
