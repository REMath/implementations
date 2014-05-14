// xml.h            see license.txt for copyright and terms of use

// Serialization and de-serialization support.

// FIX: this module should eventually go into the ast repository

#ifndef XML_H
#define XML_H

#include "strsobjdict.h"        // StringSObjDict
#include "sobjstack.h"          // SObjStack
#include "objstack.h"           // ObjStack
#include "astlist.h"            // ASTList
#include "strtable.h"           // StringRef
#include "strmap.h"             // StringRefMap

class AstXmlLexer;
class StringTable;

// forwards in this file
class XmlReaderManager;

// there are 3 categories of kinds of Tags
enum KindCategory {
  // normal node
  KC_Node,

  // list
  KC_ASTList,
  KC_FakeList,
  KC_ObjList,
  KC_SObjList,
  KC_Item,                      // an item entry in a list

  // name map
  KC_StringRefMap,
  KC_StringSObjDict,
  KC_Name,                      // a name entry in a name map
};

// the <_List_Item> </_List_Item> tag is parsed into this class to
// hold the name while the value contained by it is being parsed.
// Then it is deleted.
struct ListItem {
  StringRef to;
  ListItem() : to(NULL) {}
};

// the <_NameMap_Item> </_NameMap_Item> tag is parsed into this class
// to hold the name while the value contained by it is being parsed.
// Then it is deleted.
struct NameMapItem {
  StringRef from;
  StringRef to;
  NameMapItem() : from(NULL), to(NULL) {}
  // FIX: do I destruct/free() the name when I destruct the object?
};

// datastructures for dealing with unsatisified links; FIX: we can
// do the in-place recording of a lot of these unsatisified links
// (not the ast links)
struct UnsatLink {
  void *ptr;
  string id;
  int kind;
  bool embedded;
  UnsatLink(void *ptr0, string id0, int kind0, bool embedded0);
};

//  // datastructures for dealing with unsatisified links where neither
//  // party wants to know about the other
//  struct UnsatBiLink {
//    char const *from;
//    char const *to;
//    UnsatBiLink() : from(NULL), to(NULL) {}
//  };

// A subclass fills-in the methods that need to know about individual
// tags.
class XmlReader {
  protected:
  XmlReaderManager *manager;

  public:
  XmlReader() : manager(NULL) {}
  virtual ~XmlReader() {}

  public:
  void setManager(XmlReaderManager *manager0);

  protected:
  void userError(char const *msg) NORETURN;

  // **** virtual API
  public:

  // Parse a tag: construct a node for a tag
  virtual void *ctorNodeFromTag(int tag) = 0;

  // Parse an attribute: register an attribute into the current node
  virtual bool registerAttribute(void *target, int kind, int attr, char const *yytext0) = 0;

  // implement an eq-relation on tag kinds by mapping a tag kind to a
  // category
  virtual bool kind2kindCat(int kind, KindCategory *ret) = 0;

  // **** Generic Convert

  // note: return whether we know the answer, not the answer which
  // happens to also be a bool
  virtual bool recordKind(int kind, bool& answer) = 0;

  // cast a pointer to the pointer type we need it to be; this is only
  // needed because of multiple inheritance
  virtual bool callOpAssignToEmbeddedObj(void *obj, int kind, void *target) = 0;
  virtual bool upcastToWantedType(void *obj, int kind, void **target, int targetKind) = 0;
  // all lists are stored as ASTLists; convert to the real list
  virtual bool convertList2FakeList(ASTList<char> *list, int listKind, void **target) = 0;
  virtual bool convertList2SObjList(ASTList<char> *list, int listKind, void **target) = 0;
  virtual bool convertList2ObjList (ASTList<char> *list, int listKind, void **target) = 0;
  // all name maps are stored as StringRefMaps; convert to the real name maps
  virtual bool convertNameMap2StringRefMap
    (StringRefMap<char> *map, int mapKind, void *target) = 0;
  virtual bool convertNameMap2StringSObjDict
    (StringRefMap<char> *map, int mapKind, void *target) = 0;
};

// XmlReader-s register themselves with the Manager which tries them
// one at a time while handling incoming xml tags.
class XmlReaderManager {
  // the readers we are managing
  ASTList<XmlReader> readers;

  // **** Parsing
  char const *inputFname;       // just for error messages
  AstXmlLexer &lexer;           // a lexer on a stream already opened from the file
  public:
  StringTable &strTable;        // for canonicalizing the StringRef's in the input file

  private:
  // the node (and its kind) for the last closing tag we saw; useful
  // for extracting the top of the tree
  void *lastNode;
  int lastKind;
  // parsing stack
  SObjStack<void> nodeStack;
  ObjStack<int> kindStack;

  // **** Satisfying links

  public:
  // Since AST nodes are embedded, we have to put this on to a
  // different list than the ususal pointer unsatisfied links.
  ASTList<UnsatLink> unsatLinks;
  ASTList<UnsatLink> unsatLinks_List;
  ASTList<UnsatLink> unsatLinks_NameMap;
//    ASTList<UnsatBiLink> unsatBiLinks;

  // map object ids to the actual object
  StringSObjDict<void> id2obj;
  // map object ids to their kind ONLY IF there is a non-trivial
  // upcast to make at the link satisfaction point
  StringSObjDict<int> id2kind;

  public:
  XmlReaderManager(char const *inputFname0,
                   AstXmlLexer &lexer0,
                   StringTable &strTable0)
    : inputFname(inputFname0)
    , lexer(lexer0)
    , strTable(strTable0)
    , lastNode(NULL)            // also done in reset()
    , lastKind(0)               // also done in reset()
  {
    reset();
  }
  virtual ~XmlReaderManager() {
    readers.removeAll_dontDelete();
  }

  // **** initialization
  public:
  void registerReader(XmlReader *reader);
  void reset();

  // **** parsing
  public:
  void parseOneTopLevelTag();

  private:
  void parseOneTag();
  bool readAttributes();

  // disjunctive dispatch to the list of readers
  void kind2kindCat(int kind, KindCategory *kindCat);
  void *ctorNodeFromTag(int tag);
  void registerAttribute(void *target, int kind, int attr, char const *yytext0);

  void append2List(void *list, int listKind, void *datum);
  void insertIntoNameMap(void *map, int mapKind, StringRef name, void *datum);

  // **** parsing result
  public:
  // report an error to the user with source location information
  void userError(char const *msg) NORETURN;
  // are we at the top level during parsing?
  bool atTopLevel() {return nodeStack.isEmpty();}
  // return the top of the stack: the one tag that was parsed
  void *getLastNode() {return lastNode;}
  int getLastKind() {return lastKind;}

  // **** satisfying links
  public:
  void satisfyLinks();

  private:
  void satisfyLinks_Nodes();
  void satisfyLinks_Lists();
  void satisfyLinks_Maps();
//    void satisfyLinks_Bidirectional();

  public:
  bool recordKind(int kind);

  private:
  // convert nodes
  void callOpAssignToEmbeddedObj(void *obj, int kind, void *target);
  void *upcastToWantedType(void *obj, int kind, int targetKind);
  // convert lists
  void *convertList2FakeList(ASTList<char> *list, int listKind);
  void convertList2SObjList(ASTList<char> *list, int listKind, void **target);
  void convertList2ObjList (ASTList<char> *list, int listKind, void **target);
  // convert maps
  void convertNameMap2StringRefMap  (StringRefMap<char> *map, int listKind, void *target);
  void convertNameMap2StringSObjDict(StringRefMap<char> *map, int listKind, void *target);
};

#endif // XML_H
