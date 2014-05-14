// new.h
// implementation of new.h that doesn't use namespaces

#ifndef __NEW_H
#define __NEW_H

#include <stddef.h>    // size_t

// the contents of this file are taken directly from the
// C++ standard (section 18.1 para 1), modified to not use
// namespaces (i.e. this file is "new.h", not "new")

//namespace std {
  class bad_alloc {};
  struct nothrow_t {};
  extern const nothrow_t nothrow;
  typedef void (*new_handler)();
  new_handler set_new_handler(new_handler new_p) throw();
//}

  // sm: the ones marked with a trailing "// implicit" are supposed
  // to be implicitly declared, so the declarations here are
  // actually redundant [cppstd 3.7.3 para 2]

  void* operator new(/*std::*/size_t size) throw(/*std::*/bad_alloc);            // implicit
  void* operator new(/*std::*/size_t size, const /*std::*/nothrow_t&) throw();
  void operator delete(void* ptr) throw();                                       // implicit
  void operator delete(void* ptr, const /*std::*/nothrow_t&) throw();
  void* operator new[](/*std::*/size_t size) throw(/*std::*/bad_alloc);          // implicit
  void* operator new[](/*std::*/size_t size, const /*std::*/nothrow_t&) throw();
  void operator delete[](void* ptr) throw();                                     // implicit
  void operator delete[](void* ptr, const /*std::*/nothrow_t&) throw();

  void* operator new (/*std::*/size_t size, void* ptr) throw();
  void* operator new[](/*std::*/size_t size, void* ptr) throw();
  void operator delete (void* ptr, void*) throw();
  void operator delete[](void* ptr, void*) throw();

#endif // __NEW_H
