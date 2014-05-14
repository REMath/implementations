#!/usr/bin/perl -w
use strict;

# Think of this perl script as compressed data: the set of tokens for
# the xml for the type system.  This file generates three different
# files that have to agree with one another.

# defines the token names for purposes of printing out
my $tokenNamesFile = "astxml_lexer1_type.cc";
# the lexer file
my $tokenLexerFile = "astxml_lexer1_type.lex";
# the file that goes into the definition of enum ASTXMLTokenType
my $tokenEnumFile = "astxml_tokens1_type.h";

open(NAMES, ">$tokenNamesFile") or die $!;
open(LEXER, ">$tokenLexerFile") or die $!;
open(ENUM,  ">$tokenEnumFile") or die $!;

sub renderFiles {
  while (<DATA>) {
    chomp;
    s/^\s*//;                   # trim leading whitespace
    s/\s*$//;                   # trim trailnig whitespace
    if (/^$/) {
      # blank line
      print NAMES "\n";
      print LEXER "\n";
      print ENUM  "\n";
    } elsif (/^\#(.*)$/) {
      # comment line
      my $comment = $1;
      print NAMES "  // $comment\n";
      print LEXER "  /*${comment}*/\n";
      print ENUM  "  // $comment\n";
    } elsif (/^\w+$/) {
      # data line
      print NAMES "  \"XTOK_$_\",\n";
      print LEXER "\"$_\" return tok(XTOK_$_);\n";
      print ENUM  "  XTOK_$_, // \"$_\"\n";
    } else {
      # illegal line
      die "illegal line: $\n";
    }
  }
}

eval {
  renderFiles();
};
if ($@) {
  print "$@";
  unlink $tokenNamesFile;
  unlink $tokenLexerFile;
  unlink $tokenEnumFile;
  exit 1;
}

close(NAMES) or die $!;
close(LEXER) or die $!;
close(ENUM) or die $!;

__DATA__

# location attributes
# loc
curLoc

# Type nodes
Type
CVAtomicType
PointerType
ReferenceType
FunctionType
  FunctionType_ExnSpec
ArrayType
PointerToMemberType
# fields
atomic
atType
retType
eltType
inClassNAT
# these two are duplicated with the AST tokens
#  cv
#  size

# AtomicType nodes
AtomicType
NamedAtomicType
SimpleType
CompoundType
EnumType
  EnumType_Value
TypeVariable
PseudoInstantiation
DependentQType
# more fields
typedefVar
forward
dataMembers
virtualBases
subobj
conversionOperators
instName
syntax
parameterizingScope
selfType
valueIndex
nextValue
primary
first
# these are already defined
# "name" return tok(XTOK_name);
# "access" return tok(XTOK_access);
# "type" return tok(XTOK_type);
# "bases" return tok(XTOK_bases);
# "args" return tok(XTOK_args);
# "rest" return tok(XTOK_rest);

# Other
Variable
Scope
BaseClass
BaseClassSubobj
OverloadSet
STemplateArgument
TemplateInfo
InheritedTemplateParams
# yet more fields
flags
value
defaultParamType
funcDefn
scope
intData
usingAlias_or_parameterizedEntity
templInfo
canAcceptNames
parentScope
scopeKind
namespaceVar
curCompound
ct
variables
typeTags
parents
templateParams
overload
set
inheritedParams
instantiationOf
instantiations
specializationOf
specializations
arguments
partialInstantiationOf
partialInstantiations
argumentsToPrimary
defnScope
definitionTemplateInfo
enclosing
instLoc
# params
kind
t
# i
v
# e
at

# Some containers; I no longer care about order
#   ObjList
List_CompoundType_bases
List_CompoundType_virtualBases
List_PseudoInstantiation_args
List_TemplateInfo_inheritedParams
List_TemplateInfo_arguments
List_TemplateInfo_argumentsToPrimary
List_PQ_qualifier_sargs
List_PQ_template_sargs
#   SObjList
List_FunctionType_params
List_CompoundType_dataMembers
List_CompoundType_conversionOperators
List_BaseClassSubobj_parents
List_ExnSpec_types
List_Scope_templateParams
List_OverloadSet_set
List_TemplateInfo_instantiations
List_TemplateInfo_specializations
List_TemplateInfo_partialInstantiations
List_TemplateParams_params
#   a list element; these are in the AST so I don't need them here
#  _List_Item
#  to

#   StringRefMap
NameMap_Scope_variables
NameMap_Scope_typeTags
NameMap_EnumType_valueIndex
#   a map element
_NameMap_Item

# NOTE: off for now
# an bidirectional unsatisfied link
#  _Map_Item
#  from
#  to
