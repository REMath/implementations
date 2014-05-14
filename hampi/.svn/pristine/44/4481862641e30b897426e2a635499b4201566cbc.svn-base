/* ############################## T R E E  W A L K E R ############################ */

tree grammar HampiTree;

options {
    tokenVocab=Hampi;
    ASTLabelType=CommonTree;
}

@header{
package hampi.parser;
}

program returns  [HProgram program= new HProgram()]:
        ^(PROGRAM
           (stmt=statement
           {
             program.add(stmt);
           }
            )+
          );
        
statement returns [HStatement s = null]: 
               ( i1=vardeclStmt {s=i1;}
               | i2=cfgStmt  {s=i2;}
               | i3=regStmt  {s=i3;}
               | i4=valDeclStmt {s=i4;}
               | i5=assertStmt {s=i5;}
               ) 
          ;

vardeclStmt returns [HStatement s = null]: 
^(VAR id=ID
      size=INT
              {
                s = new HVarDeclStatement(id.getText(), size.getText());
              }
      ) 
    |
  ^(VAR id=ID
        sizeMin=INT
        sizeMax=INT
            { 
              s = new HVarDeclStatement(id.getText(), sizeMin.getText(), sizeMax.getText());
            }
         );

cfgStmt returns [CFGStatement s = new CFGStatement()]:
^(
  CFG 
  ^(CFGPROD id=ID 
    {
      s.setId(id.getText());
    }
    (cfgElemSet=cfgProductionElementSet
    {
      s.appendElementSet(cfgElemSet);
    })+
   )
 );

cfgProductionElementSet returns [List list= new ArrayList()] :
 ^(CFGPRODELEMSET 
   (el=cfgProdElement
   {
     list.add(el);
   })*
 );

cfgProdElement returns [CFGProductionElement el = null]:
  ( e1=cfgTerminal {el=e1;}
  | e2=cfgNonterminal {el=e2;}
  | e3=cfgOption {el=e3;}
  | e4=cfgStar {el=e4;}
  | e5=cfgPlus {el=e5;}
  | e6=cfgCharRange {el=e6;}
  | e7=cfgCharSeqRange {el=e7;} 
  ) 
  ;
 
cfgTerminal returns [CFGTerminal t= null] :
  (str=STR_LIT  { t = new CFGTerminal(str.getText()); }
  |seq=CHAR_SEQ { int s = Integer.valueOf(seq.getText().substring(1,4)); // PIETER
                  t = new CFGTerminal("\"" + String.valueOf((char)s) + "\""); } 
  );

cfgNonterminal returns [CFGNonterminal t= null] :
  (id= ID
  {
    t = new CFGNonterminal(id.getText());
  }
  );

cfgOption returns [CFGOption t= null] :
  ^(CFGOPTION
    el=cfgProdElement
  {
    t = new CFGOption(el);
  }
  );

cfgStar returns [CFGStar t= null] :
  ^(CFGSTAR
    el=cfgProdElement
  {
    t = new CFGStar(el);
  }
  );

cfgPlus returns [CFGPlus t= null] :
  ^(CFGPLUS
    el=cfgProdElement
  {
    t = new CFGPlus(el);
  }
  );
  
cfgCharRange returns [CFGCharRange r= null]:
^(CFGCHARRANGE 
  ch1=CHAR_LIT 
  ch2=CHAR_LIT
  {
    r = new CFGCharRange(ch1.getText(), ch2.getText());
  }
  );

cfgCharSeqRange returns [CFGCharRange r= null]: // PIETER
^(CFGCHARSEQRANGE
   ch1=CHAR_SEQ
   ch2=CHAR_SEQ
  {
   int ch1i = Integer.valueOf(ch1.getText().substring(1,4)); 
   int ch2i = Integer.valueOf(ch2.getText().substring(1,4));
   String ch1s = ("'" + String.valueOf((char)ch1i) + "'");
   String ch2s = ("'" + String.valueOf((char)ch2i) + "'");
   r = new CFGCharRange(ch1s, ch2s);
  }
  );

regStmt returns [HRegDeclStatement stmt = null] :
 ^(REG id=ID 
      r=regDefinition
      {
         stmt= new HRegDeclStatement(id.getText(), r);
      }
  );

regDefinition returns [HRegDefinition def= null]:
   (s=regConst       { def = s;  }
  | sprime=regCharSeqConst { def = sprime; } // PIETER 
  | id=regVarRef     { def = id;}
  | fix=cfgSizeFix   { def = fix;}
  | star=regStar     { def = star;}
  | range=regRange   { def = range;}
  | range=regSeqRange{ def = range;} 
  | or=regOr         { def = or;}
  | concat=regConcat { def = concat;}
  )
 ;

regVarRef returns [HRegDefinition def= null]:
(id=ID 
  {
    def = new HRegVarRef(id.getText());
  });

regOr returns [HOrRegexp def= null]:
^(OR 
   {
     def = new HOrRegexp();
   }
   (r=regDefinition
    {
      def.add(r);
    }
   )+
  );

regConcat returns [HConcatRegexp def= null]:
^(CONCAT 
   {
     def = new HConcatRegexp();
   }
   (r=regDefinition
    {
      def.add(r);
    }
   )+
  );

regRange returns [HRegDefinition def= null]:
 ^(RANGE low=CHAR_LIT 
         high=CHAR_LIT
         {
           def = new HRangeRegexp(low.getText(), high.getText());
         }
         );

regSeqRange returns [HRegDefinition def= null]:  // PIETER
 ^(CHARSEQRANGE ch1=CHAR_SEQ
         ch2=CHAR_SEQ
         {
           int ch1i = Integer.valueOf(ch1.getText().substring(1,4));
           int ch2i = Integer.valueOf(ch2.getText().substring(1,4));
           String ch1s = ("'" + String.valueOf((char)ch1i) + "'");
           String ch2s = ("'" + String.valueOf((char)ch2i) + "'");
           def = new HRangeRegexp(ch1s, ch2s);
         }
         );
 
regStar returns [HRegDefinition def= null]:
 ^(STAR r=regDefinition
    {
      def = new HStarRegexp(r);
    });
 
regConst returns [HRegDefinition def= null]:
 (s=STR_LIT 
   {
     def = new HConstRegexp(s.getText());
   });

regCharSeqConst returns [HRegDefinition def= null]: // PIETER
 (s=CHAR_SEQ 
   {
     int si = Integer.valueOf(s.getText().substring(1,4)); 
     def = new HConstRegexp("\"" + String.valueOf((char)si) + "\"");
   });
 
cfgSizeFix returns [HRegDefinition def = null] :
  ^(FIX  
     id=ID 
     s=INT
     {
       def = new HSizeFixRegDefinition(id.getText(), s.getText());
     }
   );

valDeclStmt returns [HValDeclStatement s = null] :
 ^(VAL 
  id=ID
  e=expr
  {
    s= new HValDeclStatement(id.getText(), e);
  }
  );
  
expr returns [HExpression e = null] :
 (s=STR_LIT
  {
    e = new HConstantExpression(s.getText());
  }
 )
 |
 (id=ID 
 {
   e = new HVarReferenceExpression(id.getText());
 }
 ) 
 |
 ^(CONCAT 
    {
      HConcatExpression cat = new HConcatExpression();
    }
   (sube=expr
   {
     cat.add(sube);
   }
   )+
   
   {
     e = cat;
   }
 )
 |
  ^(SUBSEQUENCE id=ID startIndex=INT len=INT
    {
      e = new HSubsequenceExpression(id.getText(),startIndex.getText(),len.getText());
    }
 );

assertStmt returns [HAssertStatement s= null] :
 ^(ASSERT b=boolExpr
   {
     s = new HAssertStatement(b);
   }
 );
 
 
boolExpr returns [HBooleanExpression b = null] :
    ^(IN id1=ID id2=ID
    {
      b = new HInExpression(id1.getText(), id2.getText(), true);
    }
    )
  | ^(CONTAINS id=ID str=STR_LIT
  {
      b = new HContainsExpression(id.getText(), str.getText(), true);
  }
  )
  |
    ^(NOTIN id1=ID id2=ID
    {
      b = new HInExpression(id1.getText(), id2.getText(), false);
    }
    )
  | ^(NOTCONTAINS id=ID str=STR_LIT
  {
      b = new HContainsExpression(id.getText(), str.getText(), false);
  }
  )
  | ^(TEQUALS id1=ID id2=ID
  {
      b = new HEqualsExpression(id1.getText(), id2.getText(), true);
  }
  )
  | ^(TNOTEQUALS id1=ID id2=ID
  {
      b = new HEqualsExpression(id1.getText(), id2.getText(), false);
  }
  )
  ;
