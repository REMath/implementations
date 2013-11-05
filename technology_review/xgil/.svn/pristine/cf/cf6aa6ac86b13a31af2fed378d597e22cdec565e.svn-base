// cc_flags.cc            see license.txt for copyright and terms of use
// code for cc_flags.h

#include "cc_flags.h"     // this module
#include "macros.h"       // STATIC_ASSERT
#include "xassert.h"      // xassert
#include "trace.h"        // tracingSys


// the check for array[limit-1] is meant to ensure that there
// are as many specified entries as there are total entries
#define MAKE_TOSTRING(T, limit, array)        \
  char const *toString(T index)               \
  {                                           \
    xassert((unsigned)index < limit);         \
    xassert(array[limit-1] != NULL);          \
    return array[index];                      \
  }

// for now we just serialize out enums as ints; it would be much more
// useful to the end-user if they were serialized out in the same form
// as toString, but we have to write a fromString() as well and that
// gets a little non-trivial for the bitwise toString() functions;
// FIX: this is pretty inefficient I think, but this code is just
// temporary
#define MAKE_TOXML_INT(T)                    \
string toXml(T index)                        \
{                                            \
  return stringc << static_cast<int>(index); \
}

#define MAKE_FROMXML_INT(T)           \
void fromXml(T &out, rostring str) \
{                                     \
  out = static_cast<T>(atoi(str));    \
}


// -------------------- TypeIntr -------------------------
char const * const typeIntrNames[NUM_TYPEINTRS] = {
  "struct",
  "class",
  "union",
  "enum"
};

MAKE_TOSTRING(TypeIntr, NUM_TYPEINTRS, typeIntrNames)
MAKE_TOXML_INT(TypeIntr)
MAKE_FROMXML_INT(TypeIntr)


// ---------------- CVFlags -------------
char const * const cvFlagNames[NUM_CVFLAGS] = {
  "const",
  "volatile",
  "restrict",
  "owner"
};


string bitmapString(int bitmap, char const * const *names, int numflags)
{
  stringBuilder sb;
  int count=0;
  for (int i=0; i<numflags; i++) {
    if (bitmap & (1 << i)) {
      if (count++) {
        sb << " ";
      }
      sb << names[i];
    }
  }

  return sb;
}

string toString(CVFlags cv)
{
  return bitmapString(cv >> CV_SHIFT_AMOUNT, cvFlagNames, NUM_CVFLAGS);
}
MAKE_TOXML_INT(CVFlags)
MAKE_FROMXML_INT(CVFlags)


// ------------------- DeclFlags --------------
char const * const declFlagNames[NUM_DECLFLAGS] = {
  "auto",           // 0
  "register",
  "static",
  "extern",
  "mutable",        // 4
  "inline",
  "virtual",
  "explicit",
  "friend",
  "typedef",        // 9

  "<enumerator>",
  "<global>",
  "<initialized>",
  "<builtin>",
  "<bound tparam>", // 14
  "<addrtaken>",
  "<parameter>",
  "<universal>",
  "<existential>",
  "<member>",       // 19
  "<definition>",
  "<inline_defn>",
  "<implicit>",
  "<forward>",
  "<temporary>",    // 24

  "<unused>",
  "namespace",
  "<extern \"C\">",
  "<selfname>",
  "<templ param>",  // 29
  "<using alias>",
  "<bitfield>",
};


string toString(DeclFlags df)
{ 
  // make sure I haven't added a flag without adding a string for it
  xassert(declFlagNames[NUM_DECLFLAGS-1] != NULL);

  return bitmapString(df, declFlagNames, NUM_DECLFLAGS);
}
MAKE_TOXML_INT(DeclFlags)
MAKE_FROMXML_INT(DeclFlags)


// ----------------------- ScopeKind ----------------------------
char const *toString(ScopeKind sk)
{
  static char const * const arr[] = {
    "unknown",
    "global",
    "parameter",
    "function",
    "class",
    "template_params",
    "template_args",
    "namespace",
  };
  STATIC_ASSERT(TABLESIZE(arr) == NUM_SCOPEKINDS);

  xassert((unsigned)sk < NUM_SCOPEKINDS);
  return arr[sk];
}


// ---------------------- SimpleTypeId --------------------------
bool isValid(SimpleTypeId id)
{
  return 0 <= id && id <= NUM_SIMPLE_TYPES;
}


#define S(x) ((SimpleTypeFlags)(x))    // work around bitwise-OR in initializers..
static SimpleTypeInfo const simpleTypeInfoArray[] = {
  //name                   size,    flags
  { "char",                   1,    S(STF_INTEGER                          ) },
  { "unsigned char",          1,    S(STF_INTEGER | STF_UNSIGNED           ) },
  { "signed char",            1,    S(STF_INTEGER                          ) },
  { "bool",                   4,    S(STF_INTEGER                          ) },
  { "int",                    4,    S(STF_INTEGER | STF_PROM               ) },
  { "unsigned int",           4,    S(STF_INTEGER | STF_PROM | STF_UNSIGNED) },
  { "long int",               4,    S(STF_INTEGER | STF_PROM               ) },
  { "unsigned long int",      4,    S(STF_INTEGER | STF_PROM | STF_UNSIGNED) },
  { "long long int",          8,    S(STF_INTEGER | STF_PROM               ) },
  { "unsigned long long int", 8,    S(STF_INTEGER | STF_PROM | STF_UNSIGNED) },
  { "short int",              2,    S(STF_INTEGER                          ) },
  { "unsigned short int",     2,    S(STF_INTEGER | STF_UNSIGNED           ) },
  { "wchar_t",                2,    S(STF_INTEGER                          ) },
  { "float",                  4,    S(STF_FLOAT                            ) },
  { "double",                 8,    S(STF_FLOAT | STF_PROM                 ) },
  { "long double",           10,    S(STF_FLOAT                            ) },
  { "float _Complex",         8,    S(STF_FLOAT                            ) },
  { "double _Complex",       16,    S(STF_FLOAT                            ) },
  { "long double _Complex",  20,    S(STF_FLOAT                            ) },
  { "float _Imaginary",       4,    S(STF_FLOAT                            ) },
  { "double _Imaginary",      8,    S(STF_FLOAT                            ) },
  { "long double _Imaginary",10,    S(STF_FLOAT                            ) },
  { "void",                   1,    S(STF_NONE                             ) },    // gnu: sizeof(void) is 1

  // these should go away early on in typechecking
  { "...",                    0,    S(STF_NONE                             ) },
  { "/*cdtor*/",              0,    S(STF_NONE                             ) },    // dsw: don't want to print <cdtor>
  { "<error>",                0,    S(STF_NONE                             ) },
  { "<dependent>",            0,    S(STF_NONE                             ) },
  { "<implicit-int>",         0,    S(STF_NONE                             ) },
  { "<notfound>",             0,    S(STF_NONE                             ) },


  { "<prom_int>",             0,    S(STF_NONE                             ) },
  { "<prom_arith>",           0,    S(STF_NONE                             ) },
  { "<integral>",             0,    S(STF_NONE                             ) },
  { "<arith>",                0,    S(STF_NONE                             ) },
  { "<arith_nobool>",         0,    S(STF_NONE                             ) },
  { "<any_obj>",              0,    S(STF_NONE                             ) },
  { "<non_void>",             0,    S(STF_NONE                             ) },
  { "<any_type>",             0,    S(STF_NONE                             ) },
  

  { "<pret_strip_ref>",       0,    S(STF_NONE                             ) },
  { "<pret_ptm>",             0,    S(STF_NONE                             ) },
  { "<pret_arith_conv>",      0,    S(STF_NONE                             ) },
  { "<pret_first>",           0,    S(STF_NONE                             ) },
  { "<pret_first_ptr2ref>",   0,    S(STF_NONE                             ) },
  { "<pret_second>",          0,    S(STF_NONE                             ) },
  { "<pret_second_ptr2ref>",  0,    S(STF_NONE                             ) },
};
#undef S

SimpleTypeInfo const &simpleTypeInfo(SimpleTypeId id)
{
  STATIC_ASSERT(TABLESIZE(simpleTypeInfoArray) == NUM_SIMPLE_TYPES);
  xassert(isValid(id));
  return simpleTypeInfoArray[id];
}


bool isComplexOrImaginary(SimpleTypeId id)
{
  return ST_FLOAT_COMPLEX <= id && id <= ST_DOUBLE_IMAGINARY;
}

MAKE_TOXML_INT(SimpleTypeId)
MAKE_FROMXML_INT(SimpleTypeId)

// ------------------------ UnaryOp -----------------------------
char const * const unaryOpNames[NUM_UNARYOPS] = {
  "+",
  "-",
  "!",
  "~"
};

MAKE_TOSTRING(UnaryOp, NUM_UNARYOPS, unaryOpNames)
MAKE_TOXML_INT(UnaryOp)
MAKE_FROMXML_INT(UnaryOp)


char const * const effectOpNames[NUM_EFFECTOPS] = {
  "++/*postfix*/",
  "--/*postfix*/",
  "++/*prefix*/",
  "--/*prefix*/",
};

MAKE_TOSTRING(EffectOp, NUM_EFFECTOPS, effectOpNames)
MAKE_TOXML_INT(EffectOp)
MAKE_FROMXML_INT(EffectOp)

bool isPostfix(EffectOp op)
{
  return op <= EFF_POSTDEC;
}


// ---------------------- BinaryOp -------------------------
char const * const binaryOpNames[NUM_BINARYOPS] = {
  "==",
  "!=",
  "<",
  ">",
  "<=",
  ">=",

  "*",
  "/",
  "%",
  "+",
  "-",
  "<<",
  ">>",
  "&",
  "^",
  "|",
  "&&",
  "||",
  ",",

  "<?",
  ">?",

  "[]",

  "=",

  ".*",
  "->*",

  "==>",
  "<==>",
};

MAKE_TOSTRING(BinaryOp, NUM_BINARYOPS, binaryOpNames)
MAKE_TOXML_INT(BinaryOp)
MAKE_FROMXML_INT(BinaryOp)

bool isPredicateCombinator(BinaryOp op)
{
  return op==BIN_AND || op==BIN_OR || op==BIN_IMPLIES || op==BIN_EQUIVALENT;
}

bool isRelational(BinaryOp op)
{
  return BIN_EQUAL <= op && op <= BIN_GREATEREQ;
}

bool isInequality(BinaryOp op)
{
  return BIN_LESS <= op && op <= BIN_GREATEREQ;
}

bool isOverloadable(BinaryOp op)
{
  return BIN_EQUAL <= op && op <= BIN_BRACKETS ||
         op == BIN_ARROW_STAR;
}


// ------------------- AccessKeyword -------------------
char const * const accessKeywordNames[NUM_ACCESS_KEYWORDS] = {
  "public",
  "protected",
  "private",
  "unspecified"
};

MAKE_TOSTRING(AccessKeyword, NUM_ACCESS_KEYWORDS, accessKeywordNames)
MAKE_TOXML_INT(AccessKeyword)
MAKE_FROMXML_INT(AccessKeyword)


// -------------------- CastKeyword --------------------
char const * const castKeywordNames[NUM_CAST_KEYWORDS] = {
  "dynamic_cast",
  "static_cast",
  "reinterpret_cast",
  "const_cast"
};

MAKE_TOSTRING(CastKeyword, NUM_CAST_KEYWORDS, castKeywordNames)
MAKE_TOXML_INT(CastKeyword)
MAKE_FROMXML_INT(CastKeyword)


// -------------------- OverloadableOp --------------------
char const * const overloadableOpNames[NUM_OVERLOADABLE_OPS] = {
  "!",
  "~",

  "++",
  "--",

  "+",
  "-",
  "*",
  "&",

  "/",
  "%",
  "<<",
  ">>",
  "^",
  "|",

  "=",
  "+=",
  "-=",
  "*=",
  "/=",
  "%=",
  "<<=",
  ">>=",
  "&=",
  "^=",
  "|=",

  "==",
  "!=",
  "<",
  ">",
  "<=",
  ">=",

  "&&",
  "||",

  "->",
  "->*",

  "[]",
  "()",
  ",",
  "?:",
  
  "<?",
  ">?",
};

MAKE_TOSTRING(OverloadableOp, NUM_OVERLOADABLE_OPS, overloadableOpNames)
MAKE_TOXML_INT(OverloadableOp)
MAKE_FROMXML_INT(OverloadableOp)


char const * const operatorFunctionNames[NUM_OVERLOADABLE_OPS] = {
  "operator!",
  "operator~",

  "operator++",
  "operator--",

  "operator+",
  "operator-",
  "operator*",
  "operator&",

  "operator/",
  "operator%",
  "operator<<",
  "operator>>",
  "operator^",
  "operator|",

  "operator=",
  "operator+=",
  "operator-=",
  "operator*=",
  "operator/=",
  "operator%=",
  "operator<<=",
  "operator>>=",
  "operator&=",
  "operator^=",
  "operator|=",

  "operator==",
  "operator!=",
  "operator<",
  "operator>",
  "operator<=",
  "operator>=",

  "operator&&",
  "operator||",

  "operator->",
  "operator->*",

  "operator[]",
  "operator()",
  "operator,",
  "operator?",
  
  "operator<?",
  "operator>?",
};


OverloadableOp toOverloadableOp(UnaryOp op)
{
  static OverloadableOp const map[] = {
    OP_PLUS,
    OP_MINUS,
    OP_NOT,
    OP_BITNOT
  };
  ASSERT_TABLESIZE(map, NUM_UNARYOPS);
  xassert(validCode(op));
  return map[op];
}

OverloadableOp toOverloadableOp(EffectOp op)
{
  static OverloadableOp const map[] = {
    OP_PLUSPLUS,
    OP_MINUSMINUS,
    OP_PLUSPLUS,
    OP_MINUSMINUS,
  };
  ASSERT_TABLESIZE(map, NUM_EFFECTOPS);
  xassert(validCode(op));
  return map[op];
}

OverloadableOp toOverloadableOp(BinaryOp op, bool isAssignment)
{ 
  xassert(validCode(op));

  // in the table, this means that an operator cannot be overloaded
  #define BAD_ENTRY NUM_OVERLOADABLE_OPS
  OverloadableOp ret = BAD_ENTRY;

  if (!isAssignment) {
    static OverloadableOp const map[] = {
      OP_EQUAL,
      OP_NOTEQUAL,
      OP_LESS,
      OP_GREATER,
      OP_LESSEQ,
      OP_GREATEREQ,

      OP_STAR,
      OP_DIV,
      OP_MOD,
      OP_PLUS,
      OP_MINUS,
      OP_LSHIFT,
      OP_RSHIFT,
      OP_AMPERSAND,
      OP_BITXOR,
      OP_BITOR,
      OP_AND,
      OP_OR,
      OP_COMMA,
      
      OP_MINIMUM,
      OP_MAXIMUM,

      OP_BRACKETS,

      BAD_ENTRY,      // isAssignment is false

      BAD_ENTRY,      // cannot overload
      OP_ARROW_STAR,

      BAD_ENTRY,      // extension..
      BAD_ENTRY,
    };
    ASSERT_TABLESIZE(map, NUM_BINARYOPS);
    ret = map[op];
  }

  else {
    static OverloadableOp const map[] = {
      BAD_ENTRY,
      BAD_ENTRY,
      BAD_ENTRY,
      BAD_ENTRY,
      BAD_ENTRY,
      BAD_ENTRY,

      OP_MULTEQ,
      OP_DIVEQ,
      OP_MODEQ,
      OP_PLUSEQ,
      OP_MINUSEQ,
      OP_LSHIFTEQ,
      OP_RSHIFTEQ,
      OP_BITANDEQ,
      OP_BITXOREQ,
      OP_BITOREQ,
      BAD_ENTRY,
      BAD_ENTRY,
      BAD_ENTRY,

      BAD_ENTRY,
      BAD_ENTRY,

      BAD_ENTRY,

      OP_ASSIGN,

      BAD_ENTRY,
      BAD_ENTRY,

      BAD_ENTRY,
      BAD_ENTRY,
    };
    ASSERT_TABLESIZE(map, NUM_BINARYOPS);
    ret = map[op];
  }
  
  xassert(ret != BAD_ENTRY);    // otherwise why did you try to map it?
  return ret;

  #undef BAD_ENTRY
}

// ------------------------ UberModifiers ---------------------
char const * const uberModifierNames[UM_NUM_FLAGS] = {
  "auto",            // 0x00000001
  "register",
  "static",
  "extern",
  "mutable",         // 0x00000010
  "inline",
  "virtual",
  "explicit",
  "friend",          // 0x00000100
  "typedef",

  "const",
  "volatile",
  "restrict",        // 0x00001000

  "wchar_t",
  "bool",
  "short",
  "int",             // 0x00010000
  "long",
  "signed",
  "unsigned",
  "float",           // 0x00100000
  "double",
  "void",
  "long long",
  "char",            // 0x01000000
  "complex",
  "imaginary"
};

string toString(UberModifiers m)
{
  xassert(uberModifierNames[UM_NUM_FLAGS-1] != NULL);
  return bitmapString(m, uberModifierNames, UM_NUM_FLAGS);
}


// ---------------------- SpecialExpr -----------------
char const *toString(SpecialExpr se)
{
  switch (se) {       
    default: xfailure("bad se code");
    case SE_NONE:       return "SE_NONE";
    case SE_ZERO:       return "SE_ZERO";
    case SE_STRINGLIT:  return "SE_STRINGLIT";
  }
}
