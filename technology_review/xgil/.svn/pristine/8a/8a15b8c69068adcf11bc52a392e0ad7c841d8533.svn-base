
// Sixgill: Static assertion checker for C/C++ programs.
// Copyright (C) 2009-2010  Stanford University
// Author: Brian Hackett
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

// type representation.
// throws away typedefs, const and attributes

#include <util/hashcons.h>
#include <util/primitive.h>
#include "serial.h"

NAMESPACE_XGILL_BEGIN

#define ITERATE_TYPE_KINDS(ITER)		\
  ITER(Error, 1)				\
  ITER(Void, 2)					\
  ITER(Int, 3)					\
  ITER(Float, 4)				\
  ITER(Pointer, 5)				\
  ITER(Array, 6)				\
  ITER(CSU, 7)					\
  ITER(Function, 8)

enum TypeKind {
  YK_Invalid = 0,
#define ITER(NAME, NUM) YK_ ## NAME = NUM,
  ITERATE_TYPE_KINDS(ITER)
#undef ITER
};

class TypeError;
class TypeVoid;
class TypeInt;
class TypeFloat;
class TypePointer;
class TypeArray;
class TypeCSU;
class TypeFunction;

class Type : public HashObject
{
 public:
  static int Compare(const Type *y0, const Type *y1);
  static Type* Copy(const Type *y);
  static void Write(Buffer *buf, const Type *y);
  static Type* Read(Buffer *buf);

  static TypeError*    MakeError();
  static TypeVoid*     MakeVoid();
  static TypeInt*      MakeInt(size_t width, bool sign);
  static TypeFloat*    MakeFloat(size_t width);
  static TypePointer*  MakePointer(Type *target_type, size_t width);
  static TypeArray*    MakeArray(Type *element_type, size_t element_count);
  static TypeCSU*      MakeCSU(String *csu_name);
  static TypeFunction* MakeFunction(Type *return_type, TypeCSU *csu_type,
                                    bool varargs,
                                    const Vector<Type*> &arguments);

  // get the width to use when making pointer types. this should be made
  // a configurable option.
  static size_t PointerWidth() { return 4; }

 public:
  // get the kind of this type.
  TypeKind Kind() const { return m_kind; }

  DOWNCAST_TYPE(Type, YK_, Void)
  DOWNCAST_TYPE(Type, YK_, Int)
  DOWNCAST_TYPE(Type, YK_, Float)
  DOWNCAST_TYPE(Type, YK_, Pointer)
  DOWNCAST_TYPE(Type, YK_, Array)
  DOWNCAST_TYPE(Type, YK_, CSU)
  DOWNCAST_TYPE(Type, YK_, Function)

  // get the width in bytes of this type. 0 for void or function types.
  // computing the width of a type may require accessing the CSU type
  // cache (see storage.h), which may require an external transaction.
  virtual size_t Width() const { return 0; }

  // get whether this type is signed or not. some integer types and
  // all float types are signed, other types are unsigned.
  virtual bool IsSigned() const { return false; }

 protected:
  TypeKind m_kind;

  Type(TypeKind kind)
    : m_kind(kind)
  {
    m_hash = m_kind;
  }

  static HashCons<Type> g_table;
};

// Type instance classes

class TypeError : public Type
{
 public:
  // inherited methods
  void Print(OutStream &out) const;

 private:
  TypeError();
  friend class Type;
};

class TypeVoid : public Type
{
 public:
  // inherited methods
  size_t Width() const;
  void Print(OutStream &out) const;

 private:
  TypeVoid();
  friend class Type;
};

class TypeInt : public Type
{
 public:
  // inherited methods
  size_t Width() const;
  bool IsSigned() const;
  void Print(OutStream &out) const;

 private:
  size_t m_width;
  bool m_sign;

  TypeInt(size_t width, bool sign);
  friend class Type;
};

class TypeFloat : public Type
{
 public:
  // inherited methods
  size_t Width() const;
  bool IsSigned() const;
  void Print(OutStream &out) const;

 private:
  size_t m_width;

  TypeFloat(size_t width);
  friend class Type;
};

class TypePointer : public Type
{
 public:
  // get the target type of this pointer.
  Type* GetTargetType() const { return m_target_type; }

  // inherited methods
  size_t Width() const;
  void Print(OutStream &out) const;
  void MarkChildren() const;

 private:
  Type *m_target_type;
  size_t m_width;

  TypePointer(Type *target_type, size_t width);
  friend class Type;
};

class TypeArray : public Type
{
 public:
  // get the element type of this array.
  Type* GetElementType() const { return m_element_type; }

  // get the declared element count of this array.
  size_t GetElementCount() const { return m_element_count; }

  // inherited methods
  size_t Width() const;
  void Print(OutStream &out) const;
  void MarkChildren() const;

 private:
  Type* m_element_type;
  size_t m_element_count;

  TypeArray(Type *element_type, size_t element_count);
  friend class Type;
};

class TypeCSU : public Type
{
 public:
  // get the name of the class/struct/union this type represents.
  String* GetCSUName() const { return m_csu_name; }

  // inherited methods
  size_t Width() const;
  void Print(OutStream &out) const;
  void MarkChildren() const;

 private:
  String *m_csu_name;

  TypeCSU(String *csu_name);
  friend class Type;
};

class TypeFunction : public Type
{
 public:
  // get the return type of this function.
  Type* GetReturnType() const { return m_return_type; }

  // get the CSU this is an instance function type on, NULL if this is
  // not an instance function type.
  TypeCSU* GetCSUType() const { return m_csu_type; }

  // get whether this is a varargs function or not.
  bool IsVarArgs() const { return m_varargs; }

  // get the number of arguments of this function.
  size_t GetArgumentCount() const
  {
    return m_argument_count;
  }

  // get the type of an argument of this function.
  // returns NULL if the argument is out of range.
  Type* GetArgumentType(size_t argument) const
  {
    if (argument >= m_argument_count)
      return NULL;
    return m_argument_types[argument];
  }

  // inherited methods
  size_t Width() const;
  void Print(OutStream &out) const;
  void MarkChildren() const;
  void Persist();
  void UnPersist();

 private:
  Type *m_return_type;
  TypeCSU *m_csu_type;
  bool m_varargs;
  Type **m_argument_types;
  size_t m_argument_count;

  TypeFunction(Type *return_type, TypeCSU *csu_type, bool varargs,
               const Vector<Type*> &arguments);
  friend class Type;
};

// class/struct/union representation

// forward declarations.
class Field;
class Variable;
class BlockCFG;

// information about a data field of a type.
struct DataField
{
  // name of this field.
  Field *field;

  // offset into the type of this field.
  size_t offset;

  DataField()
    : field(NULL), offset(0) {}

  DataField(Field *_field, size_t _offset)
    : field(_field), offset(_offset) {}
};

// information about a virtual instance function field of a type.
struct FunctionField
{
  // name of this field. if this was inherited from a base class then
  // the CSU of the field will be the original base the function
  // was declared for.
  Field *field;

  // if this was inherited from a base class, the field representing that base.
  Field *base;

  // the actual function invoked when using the field on this class.
  // NULL if the field is pure virtual in this class.
  Variable *function;

  FunctionField()
    : field(NULL), base(NULL), function(NULL) {}

  FunctionField(Field *_field, Field *_base, Variable *_function)
    : field(_field), base(_base), function(_function) {}
};

#define ITERATE_CSU_KINDS(ITER)				\
  ITER(Class, XIL_CSU_Class)				\
  ITER(Struct, XIL_CSU_Struct)				\
  ITER(Union, XIL_CSU_Union)

enum CSUKind {
  CSU_Invalid = 0,
#define ITER(NAME, NUM) CSU_ ## NAME = NUM,
  ITERATE_CSU_KINDS(ITER)
#undef ITER
};

// information about a class, struct, or union definition.
class CompositeCSU : public HashObject
{
 public:
  static int Compare(const CompositeCSU *csu0, const CompositeCSU *csu1);
  static CompositeCSU* Copy(const CompositeCSU *csu);
  static void Write(Buffer *buf, const CompositeCSU *csu);
  static CompositeCSU* Read(Buffer *buf);

  static CompositeCSU* Make(String *name)
  {
    CompositeCSU xc(name);
    return g_table.Lookup(xc);
  }

 public:
  // get the kind of this CSU.
  CSUKind Kind() const { return m_kind; }

  // get the unique name of this CSU.
  String* GetName() const { return m_name; }

  // get the width in bytes of this CSU.
  size_t GetWidth() const { return m_width; }

  // get the command used to construct this CSU.
  String* GetCommand() const { return m_command; }

  // get the begin and end location of this CSU, NULL if not available.
  Location* GetBeginLocation() const { return m_begin_location; }
  Location* GetEndLocation() const { return m_end_location; }

  // get the data fields in this CSU.
  size_t GetFieldCount() const {
    return m_data_fields ? m_data_fields->Size() : 0;
  }
  const DataField& GetField(size_t ind) const {
    Assert(m_data_fields);
    return m_data_fields->At(ind);
  }

  // get the virtual instance function fields in this CSU.
  size_t GetFunctionFieldCount() const {
    return m_function_fields ? m_function_fields->Size() : 0;
  }
  const FunctionField& GetFunctionField(size_t ind) const {
    Assert(m_function_fields);
    return m_function_fields->At(ind);
  }

  // modification methods.

  // set the kind/width of this CSU.
  void SetKind(CSUKind kind);
  void SetWidth(size_t width);

  // set the command for generating this CSU.
  void SetCommand(String *command);

  // set the begin and end locations of this CSU in the source.
  void SetBeginLocation(Location *loc);
  void SetEndLocation(Location *loc);

  // add a base class to this CSU.
  void AddBaseClass(String *base_class);

  // add a data field to this CSU.
  void AddField(Field *field, size_t offset);

  // add a virtual function field to this CSU.
  void AddFunctionField(Field *field, Field *base, Variable *function);

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;
  void Persist();
  void UnPersist();

 private:
  CSUKind m_kind;

  String *m_name;
  size_t m_width;

  String *m_command;
  Location *m_begin_location;
  Location *m_end_location;

  Vector<DataField> *m_data_fields;
  Vector<FunctionField> *m_function_fields;

  CompositeCSU(String *name);
  static HashCons<CompositeCSU> g_table;
};

// information about a CSU field. this only describes non-static fields
// and virtual functions; static fields, static functions, and non-virtual
// functions are all represented as global variables/functions.
class Field : public HashObject
{
 public:
  static int Compare(const Field *f0, const Field *f1);
  static Field* Copy(const Field *f);
  static void Write(Buffer *buf, const Field *f);
  static Field* Read(Buffer *buf);

  static Field* Make(String *name, String *source_name,
                     TypeCSU *csu_type, Type *type, bool is_function)
  {
    Field xf(name, source_name, csu_type, type, is_function);
    return g_table.Lookup(xf);
  }

 public:
  // gets the name of this field. fields in a CSU have duplicate names
  // only for unnamed padding fields.
  String* GetName() const { return m_name; }

  // get the source name which will be used to print this field, if available.
  String* GetSourceName() const { return m_source_name; }

  // get the type of the CSU containing this field. for inherited fields
  // this specifies the supertype in which the field was declared.
  TypeCSU* GetCSUType() const { return m_csu_type; }

  // get the type of this field.
  Type* GetType() const { return m_type; }

  // whether this is a virtual instance function rather than data field of the
  // containing CSU. this is true only for C++.
  bool IsInstanceFunction() const { return m_is_function; }

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;

 private:
  String *m_name;
  String *m_source_name;
  TypeCSU *m_csu_type;
  Type *m_type;
  bool m_is_function;

  Field(String *name, String *source_name, TypeCSU *csu_type,
        Type *type, bool is_function);
  static HashCons<Field> g_table;
};

NAMESPACE_XGILL_END
