// cc_type_xml.h            see license.txt for copyright and terms of use

#include "xml.h"
#include "strutil.h"            // parseQuotedString
#include "astxml_lexer.h"       // AstXmlLexer
#include "exc.h"                // xBase


UnsatLink::UnsatLink(void *ptr0, string id0, int kind0, bool embedded0)
  : ptr(ptr0), id(id0), kind(kind0), embedded(embedded0)
{};

void XmlReader::setManager(XmlReaderManager *manager0) {
  xassert(!manager);
  manager = manager0;
}

void XmlReader::userError(char const *msg) {
  manager->userError(msg);
}

void XmlReaderManager::registerReader(XmlReader *reader) {
  xassert(reader);
  readers.append(reader);
  reader->setManager(this);
}

void XmlReaderManager::reset() {
  lastNode = NULL;
  lastKind = 0;
  xassert(nodeStack.isEmpty());
  xassert(kindStack.isEmpty());
}

void XmlReaderManager::parseOneTopLevelTag() {
  // FIX: a do-while is always a bug
  do parseOneTag();
  while(!atTopLevel());
  xassert(kindStack.isEmpty()); // the stacks are synchronized
}

void XmlReaderManager::parseOneTag() {
  // state: looking for a tag start
  if (lexer.haveSeenEof()) {
    userError("unexpected EOF while looking for '<' of an open tag");
  }
  int start = lexer.getToken();
  //      printf("start:%s\n", lexer.tokenKindDesc(start).c_str());
  switch(start) {
  default:
    userError("unexpected token while looking for '<' of an open tag");
    break;
  case 0:                     // eof
    return;
    break;
  case XTOK_LESSTHAN:
    break;                    // continue parsing
  }

  // state: read a tag name
  int tag = lexer.getToken();
  // construct the tag object on the stack
  void *topTemp;
  bool sawOpenTag = true;
  switch(tag) {
  default:
    topTemp = ctorNodeFromTag(tag);
    break;
  // Slash: start of a close tag
  case XTOK_SLASH:
    sawOpenTag = false;
    break;
  // ListItem: a list element
  case XTOK__List_Item:
    topTemp = new ListItem();
    break;
  // NameMapItem: a map element
  case XTOK__NameMap_Item:
    topTemp = new NameMapItem();
    break;
//    // Special case the <__Link/> tag
//    case XTOK___Link:
//      topTemp = new UnsatBiLink();
//      break;
  }
  if (sawOpenTag) {
    // NOTE: even if it is a stand-alone tag that will not stay on the
    // stack, we still have to put it here as readAttributes()
    // attaches attributes to the node on the top of the stack (my
    // parser is some sort of stack machine).
    xassert(topTemp);
    nodeStack.push(topTemp);
    kindStack.push(new int(tag));

    // read the attributes
    bool sawContainerTag = readAttributes();

    // if it is a container tag, we just leave it on the stack
    if (sawContainerTag) {
      // state: we saw a container tag
      return;
    }

    // state: we saw a stand-alone tag.  FIX: I suppose I should
    // generalize this, but for now there is only one stand-alone tag
//      if (!tag == XTOK___Link) {
    userError("illegal stand-alone tag");
//      }
//      UnsatBiLink *ul = (UnsatBiLink*) topTemp;
//      if (!ul->from) {
//        userError("missing 'from' field on __Link tag");
//      }
//      if (!ul->to) {
//        userError("missing 'to' field on __Link tag");
//      }
//      unsatBiLinks.append(ul);
//      // we don't need it on the stack anymore
//      nodeStack.pop();
//      kindStack.pop();            // FIX: delete the return?
    return;
  }

  // state: read a close tag name
  int closeTag = lexer.getToken();
  if (!closeTag) {
    userError("unexpected file termination while looking for a close tag name");
  }
  if (nodeStack.isEmpty()) {
    userError("too many close tags");
  }
  lastNode = nodeStack.pop();
  lastKind = *kindStack.pop();
  if (lastKind != closeTag) {
    userError(stringc << "close tag " << lexer.tokenKindDesc(closeTag)
              << " does not match open tag " << lexer.tokenKindDesc(lastKind));
  }

  // state: read the '>' after a close tag
  int closeGreaterThan = lexer.getToken();
  switch(closeGreaterThan) {
  default: userError("unexpected token while looking for '>' of a close tag");
  case 0: userError("unexpected file termination while looking for '>' of a close tag");
  case XTOK_GREATERTHAN:
    break;
  }

  // deal with list entries
  if (closeTag == XTOK__List_Item) {
    // save the item tag
    ListItem *itemNode = (ListItem*)lastNode;
    int itemKind = lastKind;
    xassert(itemKind == XTOK__List_Item);

    // what kind of thing is next on the stack?
    if (nodeStack.isEmpty()) {
      userError("a _List_Item tag not immediately under a List");
    }
    void *listNode = nodeStack.top();
    int listKind = *kindStack.top();
    KindCategory listKindCat;
    kind2kindCat(listKind, &listKindCat);
    if (!(listNode &&
          (listKindCat == KC_ASTList
           || listKindCat == KC_FakeList
           || listKindCat == KC_ObjList
           || listKindCat == KC_SObjList)
        )) {
      userError("a _List_Item tag not immediately under a List");
    }

    // find the Node pointed to by the item; it should have been seen
    // by now
    if (!itemNode->to) {
      userError("no 'to' field for this _List_Item tag");
    }
    void *pointedToItem = id2obj.queryif(itemNode->to);
    if (!pointedToItem) {
      userError("no Node pointed to by _List_Item");
    }
    append2List(listNode, listKind, pointedToItem);
  }

  // deal with map entries
  else if (closeTag == XTOK__NameMap_Item) {
    // save the name tag
    NameMapItem *nameNode = (NameMapItem*)lastNode;
    int nameKind = lastKind;
    xassert(nameKind == XTOK__NameMap_Item);

    // what kind of thing is next on the stack?
    if (nodeStack.isEmpty()) {
      userError("a _NameMap_Item tag not immediately under a Map");
    }
    void *mapNode = nodeStack.top();
    int mapKind = *kindStack.top();
    KindCategory mapKindCat;
    kind2kindCat(mapKind, &mapKindCat);
    if (!(mapNode && (mapKindCat == KC_StringRefMap || mapKindCat == KC_StringSObjDict))) {
      userError("a _NameMap_Item tag not immediately under a Map");
    }

    // find the Node pointed to by the item; it should have been seen
    // by now
    void *pointedToItem = id2obj.queryif(nameNode->to);
    if (!pointedToItem) {
      userError("no Node pointed to by _NameMap_Item");
    }
    insertIntoNameMap(mapNode, mapKind, nameNode->from, pointedToItem);
  }

  // otherwise we are a normal node; just pop it off; no further
  // processing is required
  else {
  }
}

// state: read the attributes
bool XmlReaderManager::readAttributes() {
  while(1) {
    int attr = lexer.getToken();
    switch(attr) {
    default: break;             // go on; assume it is a legal attribute tag
    case 0: userError("unexpected file termination while looking for an attribute name");
    case XTOK_GREATERTHAN:
      return true;              // container tag
    case XTOK_SLASH:
      attr = lexer.getToken();  // eat the '>' token
      if (attr!=XTOK_GREATERTHAN) {
        userError("expected '>' after '/' that terminates a stand-alone tag");
      }
      return false;             // non-container tag
    }

    int eq = lexer.getToken();
    switch(eq) {
    default: userError("unexpected token while looking for an '='");
    case 0: userError("unexpected file termination while looking for an '='");
    case XTOK_EQUAL:
      break;                    // go on
    }

    int value = lexer.getToken();
    switch(value) {
    default: userError("unexpected token while looking for an attribute value");
    case 0: userError("unexpected file termination while looking for an attribute value");
    case XTOK_INT_LITERAL:
      // get it out of yytext below
      break;
    case XTOK_STRING_LITERAL:
      // get it out of yytext below
      break;                    // go on
    }

    // register the attribute
    xassert(nodeStack.isNotEmpty());
    // special case the '_id' attribute
    if (attr == XTOK_DOT_ID) {
      // FIX: I really hope the map makes a copy of this string
      string id0 = parseQuotedString(lexer.currentText());
      if (id2obj.isMapped(id0)) {
        userError(stringc << "this _id is taken " << id0);
      }
      id2obj.add(id0, nodeStack.top());
      if (recordKind(*kindStack.top())) {
        id2kind.add(id0, kindStack.top());
      }
    }
    // special case the _NameMap_Item node and its one attribute
    else if (*kindStack.top() == XTOK__NameMap_Item) {
      switch(attr) {
      default:
        userError("illegal attribute for _NameMap_Item");
        break;
      case XTOK_name:
        static_cast<NameMapItem*>(nodeStack.top())->from =
          strTable(parseQuotedString(lexer.currentText()));
        break;
      case XTOK_item:
        static_cast<NameMapItem*>(nodeStack.top())->to =
          strTable(parseQuotedString(lexer.currentText()));
        break;
      }
    }
    // special case the _List_Item node and its one attribute
    else if (*kindStack.top() == XTOK__List_Item) {
      switch(attr) {
      default:
        userError("illegal attribute for _List_Item");
        break;
      case XTOK_item:
        static_cast<ListItem*>(nodeStack.top())->to =
          strTable(parseQuotedString(lexer.currentText()));
        break;
      }
    }
//      // special case the __Link node and its attributes
//      else if (*kindStack.top() == XTOK___Link) {
//        switch(attr) {
//        default:
//          userError("illegal attribute for __Link");
//          break;
//        case XTOK_from:
//          static_cast<UnsatBiLink*>(nodeStack.top())->from =
//            strTable(parseQuotedString(lexer.currentText()));
//          break;
//        case XTOK_to:
//          static_cast<UnsatBiLink*>(nodeStack.top())->to =
//            strTable(parseQuotedString(lexer.currentText()));
//          break;
//        }
//      }
    // not a built-in attribute or tag
    else {
      registerAttribute(nodeStack.top(), *kindStack.top(), attr, lexer.currentText());
    }
  }
  if (!nodeStack.isEmpty()) {
    userError("missing closing tags at eof");
  }
  // stacks should not be out of sync
  xassert(kindStack.isEmpty());
}

void XmlReaderManager::kind2kindCat(int kind, KindCategory *kindCat) {
  xassert(kind != -1);          // this means you shouldn't be asking

  switch(kind) {
  default:
    // fallthrough the switch
    break;

  // special list element _List_Item
  case XTOK__List_Item:
    *kindCat = KC_Item;
    return;
    break;

  // special map element _NameMap_Item
  case XTOK__NameMap_Item:
    *kindCat = KC_Name;
    return;
    break;
  }

  // try each registered reader
  FOREACH_ASTLIST_NC(XmlReader, readers, iter) {
    if (iter.data()->kind2kindCat(kind, kindCat)) {
      return;
    }
  }

  xfailure("no kind category registered for this kind");
}

void *XmlReaderManager::ctorNodeFromTag(int tag) {
  xassert(tag != -1);          // this means you shouldn't be asking

  // try each registered reader
  FOREACH_ASTLIST_NC(XmlReader, readers, iter) {
    void *node = iter.data()->ctorNodeFromTag(tag);
    if (node) {
      return node;
    }
  }

  xfailure("no kind category registered for this kind");
}

void XmlReaderManager::registerAttribute
  (void *target, int kind, int attr, char const *yytext0) {
  xassert(kind != -1);          // this means you shouldn't be asking

  // try each registered reader
  FOREACH_ASTLIST_NC(XmlReader, readers, iter) {
    if (iter.data()->registerAttribute(target, kind, attr, yytext0)) {
      return;
    }
  }

  xfailure("no kind category registered for this kind");
}

void XmlReaderManager::append2List(void *list0, int listKind, void *datum0) {
  xassert(list0);
  ASTList<char> *list = static_cast<ASTList<char>*>(list0);
  char *datum = (char*)datum0;
  list->append(datum);
}

void XmlReaderManager::insertIntoNameMap(void *map0, int mapKind, StringRef name, void *datum) {
  xassert(map0);
  StringRefMap<char> *map = static_cast<StringRefMap<char>*>(map0);
  if (map->get(name)) {
    userError(stringc << "duplicate name " << name << " in map");
  }
  map->add(name, (char*)datum);
}

void XmlReaderManager::userError(char const *msg) {
  THROW(xBase(stringc << inputFname << ":" << lexer.linenumber << ":" << msg));
}

void XmlReaderManager::satisfyLinks() {
  satisfyLinks_Nodes();
  satisfyLinks_Lists();
  satisfyLinks_Maps();
//    satisfyLinks_Bidirectional();
}

void XmlReaderManager::satisfyLinks_Nodes() {
  FOREACH_ASTLIST(UnsatLink, unsatLinks, iter) {
    UnsatLink const *ul = iter.data();
    void *obj = id2obj.queryif(ul->id);
    if (obj) {
      if (ul->embedded) {
        // I can assume that the kind of the object that was
        // de-serialized is the same as the target because it was
        // embedded and there is no chance for a reference/referent
        // type mismatch.
        callOpAssignToEmbeddedObj(obj, ul->kind, ul->ptr);
        // FIX: we should now delete obj; in fact, this should be done
        // by callOpAssignToEmbeddedObj() since it knows the type of
        // the object which is necessary to delete it of course.  I'll
        // leave this for an optimization pass which we will do later
        // to handle many of these things.
      } else {
        if (int *kind = id2kind.queryif(ul->id)) {
          *( (void**)(ul->ptr) ) = upcastToWantedType(obj, *kind, ul->kind);
        } else {
          // no kind was registered for the object and therefore no
          // upcasting is required and there is no decision to make; so
          // just do the straight pointer assignment
          *( (void**) (ul->ptr) ) = obj;
        }
      }
    } else {
      // no satisfaction was provided for this link; for now we just
      // skip it, but if you wanted to report that in some way, here
      // is the place to do it
//        cout << "unsatisfied node link: " << ul->id << endl;
    }
  }
}

void XmlReaderManager::satisfyLinks_Lists() {
  FOREACH_ASTLIST(UnsatLink, unsatLinks_List, iter) {
    UnsatLink const *ul = iter.data();
    xassert(ul->embedded);
    // NOTE: I rely on the fact that all ASTLists just contain
    // pointers; otherwise this cast would cause problems; Note that I
    // have to use char instead of void because you can't delete a
    // pointer to void; see the note in the if below.
    ASTList<char> *obj = reinterpret_cast<ASTList<char>*>(id2obj.queryif(ul->id));
    if (!obj) {
      // no satisfaction was provided for this link; for now we just
      // skip it, but if you wanted to report that in some way, here
      // is the place to do it
      //        cout << "unsatisfied List link: " << ul->id << endl;
      continue;
    }

    KindCategory kindCat;
    kind2kindCat(ul->kind, &kindCat);
    switch (kindCat) {
    default:
      xfailure("illegal list kind");
      break;

    case KC_ASTList: {
      // Recall that ASTLists are used in a class by embeding them.
      // Therefore, a pointer to the field to be filled in is a
      // pointer to an ASTList, not a pointer to a pointer to an
      // ASTList, as one might expect for most other classes that were
      // used in a host class by being pointed to.
      ASTList<char> *ptr = reinterpret_cast<ASTList<char>*>(ul->ptr);
      xassert(ptr->isEmpty());
      // this is particularly tricky because the steal contains a
      // delete, however there is nothing to delete, so we should be
      // ok.  If there were something to delete, we would be in
      // trouble because you can't call delete on a pointer to an
      // object the size of which is different from the size you think
      // it is due to a type you cast it too.
      ptr->steal(obj);
      // it seems that I should not subsequently delete the list as
      // the steal() has deleted the voidlist of the ASTList and it
      // seems to be a bug to try to then delete the ASTList that has
      // been stolen from
      break;
    }

    case KC_FakeList: {
      // Convert the ASTList we used to store the FakeList into a real
      // FakeList and hook in all of the pointers.  This is
      // type-specific, so generated code must do it that can switch
      // on the templatized type of the FakeList.
      *( (void**) (ul->ptr) ) = convertList2FakeList(obj, ul->kind);
      // Make the list dis-own all of its contents so it doesn't delete
      // them when we delete it.  Yes, I should have used a non-owning
      // constant-time-append list.
      obj->removeAll_dontDelete();
      // delete the ASTList
      delete obj;
      break;
    }

    case KC_SObjList: {
      // Convert the ASTList we used to store the SObjList into a real
      // SObjList and hook in all of the pointers.  This is
      // type-specific, so generated code must do it that can switch
      // on the templatized type of the SObjList.
      convertList2SObjList(obj, ul->kind, (void**) (ul->ptr) );
      // Make the list dis-own all of its contents so it doesn't delete
      // them when we delete it.  Yes, I should have used a non-owning
      // constant-time-append list.
      obj->removeAll_dontDelete();
      // delete the ASTList
      delete obj;
      break;
    }

    case KC_ObjList: {
      // Convert the ASTList we used to store the ObjList into a real
      // ObjList and hook in all of the pointers.  This is
      // type-specific, so generated code must do it that can switch
      // on the templatized type of the ObjList.
      convertList2ObjList(obj, ul->kind, (void**) (ul->ptr) );
      // Make the list dis-own all of its contents so it doesn't delete
      // them when we delete it.  Yes, I should have used a non-owning
      // constant-time-append list.
      obj->removeAll_dontDelete();
      // delete the ASTList
      delete obj;
      break;
    }
    }
  }
}

void XmlReaderManager::satisfyLinks_Maps() {
  FOREACH_ASTLIST(UnsatLink, unsatLinks_NameMap, iter) {
    UnsatLink const *ul = iter.data();
    xassert(ul->embedded);
    // NOTE: I rely on the fact that all StringRefMap-s just contain
    // pointers; otherwise this cast would cause problems; Note that I
    // have to use char instead of void because you can't delete a
    // pointer to void; see the note in the if below.
    StringRefMap<char> *obj = reinterpret_cast<StringRefMap<char>*>(id2obj.queryif(ul->id));
    if (!obj) {
      // no satisfaction was provided for this link; for now we just
      // skip it, but if you wanted to report that in some way, here
      // is the place to do it
      //        cout << "unsatisfied List link: " << ul->id << endl;
      continue;
    }

    KindCategory kindCat;
    kind2kindCat(ul->kind, &kindCat);
    switch (kindCat) {
    default:
      xfailure("illegal name map kind");
      break;

    case KC_StringRefMap: {
      // FIX: this would be way more efficient if there were a
      // PtrMap::steal() method: I wouldn't need this convert call.
      convertNameMap2StringRefMap(obj, ul->kind, (void**) (ul->ptr) );
      break;
    }

    case KC_StringSObjDict: {
      convertNameMap2StringSObjDict(obj, ul->kind, (void**) (ul->ptr) );
      break;
    }

    }
  }
}

//  void XmlReaderManager::satisfyLinks_Bidirectional() {
//    FOREACH_ASTLIST(UnsatBiLink, unsatBiLinks, iter) {
//      UnsatBiLink const *ul = iter.data();
//      void **from = (void**)id2obj.queryif(ul->from);
//      // NOTE: these are different from unidirectional links: you really
//      // shouldn't make one unless both parties can be found.
//      if (!from) {
//        userError("Unsatisfied bidirectional link: 'from' not found");
//      }
//      void *to = id2obj.queryif(ul->to);
//      if (!to) {
//        userError("Unsatisfied bidirectional link: 'to' not found");
//      }
//      *(from) = to;
//    }
//  }

bool XmlReaderManager::recordKind(int kind) {
  FOREACH_ASTLIST_NC(XmlReader, readers, iter) {
    bool answer;
    if (iter.data()->recordKind(kind, answer)) {
      return answer;
    }
  }
  THROW(xBase(stringc << "no way to decide if kind should be recorded"));
}

void XmlReaderManager::callOpAssignToEmbeddedObj(void *obj, int kind, void *target) {
  FOREACH_ASTLIST_NC(XmlReader, readers, iter) {
    if (iter.data()->callOpAssignToEmbeddedObj(obj, kind, target)) {
      return;
    }
  }
  THROW(xBase(stringc << "no way to call op assign"));
}

void *XmlReaderManager::upcastToWantedType(void *obj, int kind, int targetKind) {
  FOREACH_ASTLIST_NC(XmlReader, readers, iter) {
    void *target;
    if (iter.data()->upcastToWantedType(obj, kind, &target, targetKind)) {
      return target;
    }
  }
  THROW(xBase(stringc << "no way to upcast"));
}

void *XmlReaderManager::convertList2FakeList(ASTList<char> *list, int listKind) {
  FOREACH_ASTLIST_NC(XmlReader, readers, iter) {
    void *target;
    if (iter.data()->convertList2FakeList(list, listKind, &target)) {
      return target;
    }
  }
  THROW(xBase(stringc << "no converter for FakeList type"));
}

void XmlReaderManager::convertList2SObjList(ASTList<char> *list, int listKind, void **target) {
  FOREACH_ASTLIST_NC(XmlReader, readers, iter) {
    if (iter.data()->convertList2SObjList(list, listKind, target)) {
      return;
    }
  }
  THROW(xBase(stringc << "no converter for SObjList type"));
}

void XmlReaderManager::convertList2ObjList(ASTList<char> *list, int listKind, void **target) {
  FOREACH_ASTLIST_NC(XmlReader, readers, iter) {
    if (iter.data()->convertList2ObjList(list, listKind, target)) {
      return;
    }
  }
  THROW(xBase(stringc << "no converter for ObjList type"));
}

void XmlReaderManager::convertNameMap2StringRefMap
  (StringRefMap<char> *map, int mapKind, void *target) {
  static int count = 0;
  ++count;
  FOREACH_ASTLIST_NC(XmlReader, readers, iter) {
    if (iter.data()->convertNameMap2StringRefMap(map, mapKind, target)) {
      return;
    }
  }
  THROW(xBase(stringc << "no converter for name map type"));
}

void XmlReaderManager::convertNameMap2StringSObjDict
  (StringRefMap<char> *map, int mapKind, void *target) {
  FOREACH_ASTLIST_NC(XmlReader, readers, iter) {
    if (iter.data()->convertNameMap2StringSObjDict(map, mapKind, target)) {
      return;
    }
  }
  THROW(xBase(stringc << "no converter for name map type"));
}
