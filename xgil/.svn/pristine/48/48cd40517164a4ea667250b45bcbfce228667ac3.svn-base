// strmap.h
// PtrMap using StringRef as key

#ifndef STRMAP_H
#define STRMAP_H

#include "strtable.h"     // StringRef
#include "ptrmap.h"       // PtrMap

// The 'KEY' argument to PtrMap is "char const" because it implicitly
// adds a "*", so the actual key is "char const *", i.e. StringRef.
// But note that the keys really have to be StringRef, not just any
// char*, because PtrMap relies on the unique-representative property.
template <class VALUE>
class StringRefMap : public PtrMap<char const, VALUE> {
};

#endif // STRMAP_H
