// pair.h            see license.txt for copyright and terms of use
// approximately standard-conforming (20.2.2) definition of pair<>

// It is intended that a user who wants to use STL can simply arrange
// to #include <utility> (and say 'using std::pair;') at this point
// instead of using the definitions contained in this file.  That is,
// this file provides a subset of <utility>.

#ifndef PAIR_H
#define PAIR_H

template <class T1, class T2>
struct pair {
  typedef T1 first_type;
  typedef T2 second_type;

  T1 first;
  T2 second;

  pair() {}
  pair(T1 const &x, T2 const &y) : first(x), second(y) {}

  // I don't plan to use the templatized ctor, so will omit it

  // operator= is defined by the compiler

  // the header synopsis in 20.2 puts all the operators into
  // the namespace, but I like them in the class and it should
  // not make a difference
  
  // equality
  bool operator==(pair<T1,T2> const &obj)
    { return first == obj.first && second == obj.second; }
  bool operator!=(pair<T1,T2> const &obj)
    { return !operator==(obj); }
             
  // inequalities; note that this is the lexicographic order
  // with 'first' dominating
  bool operator <(pair<T1,T2> const &obj)
    { return first < obj.first ||
             (!(obj.first < first) && second < obj.second); }
  bool operator >(pair<T1,T2> const &obj)
    { return obj.operator<(*this); }
  bool operator<=(pair<T1,T2> const &obj)
    { return operator<(obj) || operator==(obj); }
  bool operator>=(pair<T1,T2> const &obj)
    { return operator>(obj) || operator==(obj); }
};
  

// I do not know why the standard uses 'T1' instead of 'T1 const &' here.
template <class T1, class T2>
inline pair<T1,T2> make_pair(T1 const &x, T2 const &y)
{
  return pair<T1,T2>(x,y);
}


#endif // PAIR_H
