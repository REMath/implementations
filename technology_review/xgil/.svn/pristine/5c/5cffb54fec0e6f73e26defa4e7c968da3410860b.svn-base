// cc_type_xml.h            see license.txt for copyright and terms of use

// Serialization and de-serialization for the type system, template
// system, and variables.

#ifndef CC_TYPE_XML_H
#define CC_TYPE_XML_H

#include "cc_type.h"            // Types, TypeVisitor
#include "template.h"           // Template stuff is only forward-declared in cc_type.h
#include "sobjset.h"            // SObjSet
#include "xml.h"                // ReadXml

class AstXmlLexer;
class OverloadSet;
class ASTVisitor;

string toXml(CompoundType::Keyword id);
void fromXml(CompoundType::Keyword &out, rostring str);

string toXml(FunctionFlags id);
void fromXml(FunctionFlags &out, rostring str);

// -------------------- TypeToXml -------------------

// print the Type tree out as XML
class TypeToXml {
  protected:
  ostream &out;                 // output stream to which to print
  int &depth;                   // ref so we can share our indentation depth with other printers
  bool indent;                  // should we print indentation?

  public:
  ASTVisitor *astVisitor;       // for launching sub-traversals of AST we encounter in the Types

  protected:
  // printing of types is idempotent
  SObjSet<void const *> printedSetTY;
  SObjSet<void const *> printedSetBC;
  SObjSet<void const *> printedSetOL;
  SObjSet<void const *> printedSetNM;

  public:
  TypeToXml(ostream &out0, int &depth0, bool indent0=false);
  virtual ~TypeToXml() {}

  private:
  // print a newline and indent if the user wants indentation; NOTE:
  // the convention is that you don't print a newline until you are
  // *sure* you have something to print that goes onto the next line;
  // that is, most lines do *not* end in a newline
  void newline();
  friend class TypeToXml_CloseTagPrinter;

#define identity0(NAME, TEMPL) TEMPL bool printed(NAME const * const obj)
#define identity(NAME) identity0(NAME, )
#define identityTempl(NAME) identity0(NAME, template<class T>)

  identity(Type);
  identity(AtomicType);
  identity(CompoundType);
  identity(FunctionType::ExnSpec);
  identity(EnumType::Value);
  identity(BaseClass);
  identity(Scope);
  identity(Variable);
  identity(OverloadSet);
  identity(STemplateArgument);
  identity(TemplateInfo);
  identity(InheritedTemplateParams);
  identityTempl(ObjList<T>);
  identityTempl(SObjList<T>);
  identityTempl(StringRefMap<T>);
  identityTempl(StringObjDict<T>);

#undef identity0
#undef identity
#undef identityTempl

  public:
  // in the AST
  void toXml(ObjList<STemplateArgument> *list);

  void toXml(Type *t);
  void toXml(AtomicType *atom);
  void toXml(CompoundType *ct); // disambiguates the overloading
  void toXml(Variable *var);

  private:
  void toXml_FunctionType_ExnSpec(void /*FunctionType::ExnSpec*/ *exnSpec);

  void toXml_EnumType_Value(void /*EnumType::Value*/ *eValue0);
  void toXml_NamedAtomicType_properties(NamedAtomicType *nat);
  void toXml_NamedAtomicType_subtags(NamedAtomicType *nat);

  void toXml(OverloadSet *oload);

  void toXml(BaseClass *bc);
  void toXml_BaseClass_properties(BaseClass *bc);
  void toXml_BaseClass_subtags(BaseClass *bc);
  void toXml(BaseClassSubobj *bc);

  void toXml(Scope *scope);
  void toXml_Scope_properties(Scope *scope);
  void toXml_Scope_subtags(Scope *scope);

  void toXml(STemplateArgument *sta);
  void toXml(TemplateInfo *ti);
  void toXml(InheritedTemplateParams *itp);
  void toXml_TemplateParams_properties(TemplateParams *tp);
  void toXml_TemplateParams_subtags(TemplateParams *tp);
};


// -------------------- TypeXmlReader -------------------

// Specialization of the ReadXml framework that reads in XML for
// serialized types.

// parse Types and Variables serialized as XML
class TypeXmlReader : public XmlReader {
//    BasicTypeFactory &tFac;

  public:
  // Parse a tag: construct a node for a tag
  virtual void *ctorNodeFromTag(int tag);

  // Parse an attribute: register an attribute into the current node
  virtual bool registerAttribute(void *target, int kind, int attr, char const *yytext0);

  // implement an eq-relation on tag kinds by mapping a tag kind to a
  // category
  virtual bool kind2kindCat(int kind, KindCategory *ret);

  // **** Generic Convert
  virtual bool recordKind(int kind, bool& answer);

  // cast a pointer to the pointer type we need it to be
  virtual bool callOpAssignToEmbeddedObj(void *obj, int kind, void *target);
  virtual bool upcastToWantedType(void *obj, int kind, void **target, int targetKind);
  // all lists are stored as ASTLists; convert to the real list
  virtual bool convertList2FakeList(ASTList<char> *list, int listKind, void **target);
  virtual bool convertList2SObjList(ASTList<char> *list, int listKind, void **target);
  virtual bool convertList2ObjList (ASTList<char> *list, int listKind, void **target);
  // all name maps are stored as StringRefMaps; convert to the real name maps
  virtual bool convertNameMap2StringRefMap
    (StringRefMap<char> *map, int mapKind, void *target);
  virtual bool convertNameMap2StringSObjDict
    (StringRefMap<char> *map, int mapKind, void *target);

  private:
  // Types
  void registerAttr_CVAtomicType       (CVAtomicType *,        int attr, char const *strValue);
  void registerAttr_PointerType        (PointerType *,         int attr, char const *strValue);
  void registerAttr_ReferenceType      (ReferenceType *,       int attr, char const *strValue);
  void registerAttr_FunctionType       (FunctionType *,        int attr, char const *strValue);
  void registerAttr_FunctionType_ExnSpec
    (FunctionType::ExnSpec *, int attr, char const *strValue);
  void registerAttr_ArrayType          (ArrayType *,           int attr, char const *strValue);
  void registerAttr_PointerToMemberType(PointerToMemberType *, int attr, char const *strValue);

  // AtomicTypes
  bool registerAttr_NamedAtomicType_super(NamedAtomicType *,   int attr, char const *strValue);
  void registerAttr_SimpleType         (SimpleType *,          int attr, char const *strValue);
  void registerAttr_CompoundType       (CompoundType *,        int attr, char const *strValue);
  void registerAttr_EnumType           (EnumType *,            int attr, char const *strValue);
  void registerAttr_EnumType_Value     (EnumType::Value *,     int attr, char const *strValue);
  void registerAttr_TypeVariable       (TypeVariable *,        int attr, char const *strValue);
  void registerAttr_PseudoInstantiation(PseudoInstantiation *, int attr, char const *strValue);
  void registerAttr_DependentQType     (DependentQType *,      int attr, char const *strValue);

  // other
  void registerAttr_Variable           (Variable *,            int attr, char const *strValue);
  bool registerAttr_Scope_super        (Scope *,               int attr, char const *strValue);
  void registerAttr_Scope              (Scope *,               int attr, char const *strValue);
  bool registerAttr_BaseClass_super    (BaseClass *,           int attr, char const *strValue);
  void registerAttr_BaseClass          (BaseClass *,           int attr, char const *strValue);
  void registerAttr_BaseClassSubobj    (BaseClassSubobj *,     int attr, char const *strValue);
  void registerAttr_OverloadSet        (OverloadSet *,         int attr, char const *strValue);
  void registerAttr_STemplateArgument  (STemplateArgument *,   int attr, char const *strValue);
  bool registerAttr_TemplateParams_super(TemplateParams *obj,  int attr, char const *strValue);
  void registerAttr_TemplateInfo       (TemplateInfo *,        int attr, char const *strValue);
  void registerAttr_InheritedTemplateParams(InheritedTemplateParams*,
                                                               int attr, char const *strValue);
};

#endif // CC_TYPE_XML_H
