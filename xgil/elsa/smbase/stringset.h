// stringset.h            see license.txt for copyright and terms of use
// set of character strings

#ifndef STRINGSET_H
#define STRINGSET_H

#include "strsobjdict.h"       // StringSObjDict

class StringSet {
private:     // data        
  // represent using a dictionary of pointers to nothing
  StringSObjDict<int> elts;
  
public:      // funcs
  StringSet() : elts() {}
  ~StringSet();

  // external iterator
  class Iter {
  private:
    StringSObjDict<int>::Iter iter;

  public:
    Iter(StringSet &set) : iter(set.elts) {}
    Iter(Iter const &obj) : DMEMB(iter) {}
    Iter& operator= (Iter const &obj) { CMEMB(iter); return *this; }

    bool isDone() const { return iter.isDone(); }
    Iter& next() { iter.next(); return *this; }

    string const &data() const { return iter.key(); }

    int private_getCurrent() const { return iter.private_getCurrent(); }
  };
  friend class Iter;

  class IterC {
  private:
    StringSObjDict<int>::IterC iter;

  public:
    IterC(StringSet const &set) : iter(set.elts) {}
    IterC(IterC const &obj) : DMEMB(iter) {}
    IterC& operator= (IterC const &obj) { CMEMB(iter); return *this; }

    bool isDone() const { return iter.isDone(); }
    IterC& next() { iter.next(); return *this; }

    string const &data() const { return iter.key(); }

    int private_getCurrent() const { return iter.private_getCurrent(); }
  };
  friend class IterC;

  // # elts in the set
  int size() const                        { return elts.size(); }

  bool isEmpty() const                    { return elts.isEmpty(); }
  bool isNotEmpty() const                 { return elts.isNotEmpty(); }

  // true if elt is in the set
  bool contains(char const *elt) const    { return elts.isMapped(elt); }
  bool contains(rostring elt) const       { return contains(elt.c_str()); }

  // add elt to the set; ok if it's already there
  void add(char const *elt);
  void add(rostring elt) { add(elt.c_str()); }

  // remove elt from the set; ok if it's not there now
  void remove(char const *elt);
  void remove(rostring elt) { remove(elt.c_str()); }

  // empty the set
  void empty()                            { elts.empty(); }
};

#define FOREACH_STRINGSET(list, iter) \
  for(StringSet::IterC iter(list); !iter.isDone(); iter.next())

#define FOREACH_STRINGSET_NC(list, iter) \
  for(StringSet::Iter iter(list); !iter.isDone(); iter.next())

#endif // STRINGSET_H
