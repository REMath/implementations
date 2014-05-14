noinst_LIBRARIES = libast.a

INCLUDES = -I../sat/mtl -I../sat/core

libast_a_SOURCES = AST.cpp ASTKind.cpp ASTUtil.cpp BitBlast.cpp SimpBool.cpp ToCNF.cpp ToSAT.cpp Transform.cpp
noinst_HEADERS = AST.h ASTKind.h ASTUtil.h
dist_noinst_DATA = ASTKind.kinds genkinds.pl

ASTKind.h ASTKind.cpp: ASTKind.kinds
	$(PERL) genkinds.pl

AST.cpp BitBlast.cpp SimpBool.cpp ToCNF.cpp ToSAT.cpp Transform.cpp: ASTKind.h
