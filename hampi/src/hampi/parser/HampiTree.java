// $ANTLR 3.1b1 src/hampi/parser/HampiTree.g 2010-05-27 10:36:52

package hampi.parser;


import java.util.*;

import org.antlr.runtime.*;
import org.antlr.runtime.BitSet;
import org.antlr.runtime.tree.*;

public class HampiTree extends TreeParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "CFGPROD", "ASSIGN", "PROGRAM", "CFGOPTION", "CFGSTAR", "CFGPLUS", "TEQUALS", "TNOTEQUALS", "FIX", "CONTAINS", "IN", "ASSERT", "CONCAT", "SUBSEQUENCE", "VAR", "CFG", "REG", "VAL", "CONST", "RANGE", "CHARSEQRANGE", "OR", "NOTIN", "NOTCONTAINS", "CFGCHARRANGE", "CFGCHARSEQRANGE", "CFGPRODELEMSET", "VALS", "SEMI", "KW_VAR", "ID", "COLON", "INT", "KW_CFG", "BAR", "LPAREN", "RPAREN", "QUESTION", "STAR", "PLUS", "LSQUARE", "CHAR_LIT", "MINUS", "RSQUARE", "CHAR_SEQ", "STR_LIT", "KW_REG", "KW_FIX", "COMMA", "KW_STAR", "KW_OR", "KW_CONCAT", "KW_VAL", "KW_ASSERT", "KW_IN", "KW_CONTAINS", "KW_NOT", "KW_EQUALS", "KN_NOT", "KW_QUERY", "EQUALS", "NOTEQUALS", "EscapeSequence", "NEWLINE", "WS", "COMMENT", "LINE_COMMENT", "'..'"
    };
    public static final int CFGSTAR=8;
    public static final int FIX=12;
    public static final int STAR=42;
    public static final int LSQUARE=44;
    public static final int KW_VAL=56;
    public static final int KW_EQUALS=61;
    public static final int CONST=22;
    public static final int CFGPROD=4;
    public static final int CONTAINS=13;
    public static final int EQUALS=64;
    public static final int ID=34;
    public static final int CFG=19;
    public static final int EOF=-1;
    public static final int LPAREN=39;
    public static final int KW_VAR=33;
    public static final int VALS=31;
    public static final int CHAR_SEQ=48;
    public static final int RPAREN=40;
    public static final int IN=14;
    public static final int CFGOPTION=7;
    public static final int COMMA=52;
    public static final int CFGPRODELEMSET=30;
    public static final int TEQUALS=10;
    public static final int CFGCHARRANGE=28;
    public static final int KW_IN=58;
    public static final int VAL=21;
    public static final int PLUS=43;
    public static final int VAR=18;
    public static final int COMMENT=69;
    public static final int NOTCONTAINS=27;
    public static final int KW_FIX=51;
    public static final int KW_REG=50;
    public static final int LINE_COMMENT=70;
    public static final int CONCAT=16;
    public static final int KW_ASSERT=57;
    public static final int STR_LIT=49;
    public static final int NOTEQUALS=65;
    public static final int KW_QUERY=63;
    public static final int RANGE=23;
    public static final int SUBSEQUENCE=17;
    public static final int INT=36;
    public static final int CHAR_LIT=45;
    public static final int MINUS=46;
    public static final int RSQUARE=47;
    public static final int REG=20;
    public static final int SEMI=32;
    public static final int TNOTEQUALS=11;
    public static final int ASSERT=15;
    public static final int CFGCHARSEQRANGE=29;
    public static final int CFGPLUS=9;
    public static final int COLON=35;
    public static final int T__71=71;
    public static final int WS=68;
    public static final int QUESTION=41;
    public static final int KW_CONCAT=55;
    public static final int NEWLINE=67;
    public static final int KW_OR=54;
    public static final int KW_CONTAINS=59;
    public static final int OR=25;
    public static final int CHARSEQRANGE=24;
    public static final int ASSIGN=5;
    public static final int KN_NOT=62;
    public static final int PROGRAM=6;
    public static final int KW_STAR=53;
    public static final int EscapeSequence=66;
    public static final int BAR=38;
    public static final int KW_CFG=37;
    public static final int KW_NOT=60;
    public static final int NOTIN=26;

    // delegates
    // delegators


        public HampiTree(TreeNodeStream input) {
            this(input, new RecognizerSharedState());
        }
        public HampiTree(TreeNodeStream input, RecognizerSharedState state) {
            super(input, state);
        }
        

    public String[] getTokenNames() { return HampiTree.tokenNames; }
    public String getGrammarFileName() { return "src/hampi/parser/HampiTree.g"; }



    // $ANTLR start program
    // src/hampi/parser/HampiTree.g:14:1: program returns [HProgram program= new HProgram()] : ^( PROGRAM (stmt= statement )+ ) ;
    public final HProgram program() throws RecognitionException {
        HProgram program =  new HProgram();

        HStatement stmt = null;


        try {
            // src/hampi/parser/HampiTree.g:14:52: ( ^( PROGRAM (stmt= statement )+ ) )
            // src/hampi/parser/HampiTree.g:15:9: ^( PROGRAM (stmt= statement )+ )
            {
            match(input,PROGRAM,FOLLOW_PROGRAM_in_program56); 

            match(input, Token.DOWN, null); 
            // src/hampi/parser/HampiTree.g:16:12: (stmt= statement )+
            int cnt1=0;
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0==ASSERT||(LA1_0>=VAR && LA1_0<=VAL)) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // src/hampi/parser/HampiTree.g:16:13: stmt= statement
            	    {
            	    pushFollow(FOLLOW_statement_in_program72);
            	    stmt=statement();

            	    state._fsp--;


            	                 program.add(stmt);
            	               

            	    }
            	    break;

            	default :
            	    if ( cnt1 >= 1 ) break loop1;
                        EarlyExitException eee =
                            new EarlyExitException(1, input);
                        throw eee;
                }
                cnt1++;
            } while (true);


            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return program;
    }
    // $ANTLR end program


    // $ANTLR start statement
    // src/hampi/parser/HampiTree.g:23:1: statement returns [HStatement s = null] : (i1= vardeclStmt | i2= cfgStmt | i3= regStmt | i4= valDeclStmt | i5= assertStmt ) ;
    public final HStatement statement() throws RecognitionException {
        HStatement s =  null;

        HStatement i1 = null;

        CFGStatement i2 = null;

        HRegDeclStatement i3 = null;

        HValDeclStatement i4 = null;

        HAssertStatement i5 = null;


        try {
            // src/hampi/parser/HampiTree.g:23:40: ( (i1= vardeclStmt | i2= cfgStmt | i3= regStmt | i4= valDeclStmt | i5= assertStmt ) )
            // src/hampi/parser/HampiTree.g:24:16: (i1= vardeclStmt | i2= cfgStmt | i3= regStmt | i4= valDeclStmt | i5= assertStmt )
            {
            // src/hampi/parser/HampiTree.g:24:16: (i1= vardeclStmt | i2= cfgStmt | i3= regStmt | i4= valDeclStmt | i5= assertStmt )
            int alt2=5;
            switch ( input.LA(1) ) {
            case VAR:
                {
                alt2=1;
                }
                break;
            case CFG:
                {
                alt2=2;
                }
                break;
            case REG:
                {
                alt2=3;
                }
                break;
            case VAL:
                {
                alt2=4;
                }
                break;
            case ASSERT:
                {
                alt2=5;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 2, 0, input);

                throw nvae;
            }

            switch (alt2) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:24:18: i1= vardeclStmt
                    {
                    pushFollow(FOLLOW_vardeclStmt_in_statement151);
                    i1=vardeclStmt();

                    state._fsp--;

                    s=i1;

                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:25:18: i2= cfgStmt
                    {
                    pushFollow(FOLLOW_cfgStmt_in_statement174);
                    i2=cfgStmt();

                    state._fsp--;

                    s=i2;

                    }
                    break;
                case 3 :
                    // src/hampi/parser/HampiTree.g:26:18: i3= regStmt
                    {
                    pushFollow(FOLLOW_regStmt_in_statement198);
                    i3=regStmt();

                    state._fsp--;

                    s=i3;

                    }
                    break;
                case 4 :
                    // src/hampi/parser/HampiTree.g:27:18: i4= valDeclStmt
                    {
                    pushFollow(FOLLOW_valDeclStmt_in_statement222);
                    i4=valDeclStmt();

                    state._fsp--;

                    s=i4;

                    }
                    break;
                case 5 :
                    // src/hampi/parser/HampiTree.g:28:18: i5= assertStmt
                    {
                    pushFollow(FOLLOW_assertStmt_in_statement245);
                    i5=assertStmt();

                    state._fsp--;

                    s=i5;

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return s;
    }
    // $ANTLR end statement


    // $ANTLR start vardeclStmt
    // src/hampi/parser/HampiTree.g:32:1: vardeclStmt returns [HStatement s = null] : ( ^( VAR id= ID size= INT ) | ^( VAR id= ID sizeMin= INT sizeMax= INT ) );
    public final HStatement vardeclStmt() throws RecognitionException {
        HStatement s =  null;

        CommonTree id=null;
        CommonTree size=null;
        CommonTree sizeMin=null;
        CommonTree sizeMax=null;

        try {
            // src/hampi/parser/HampiTree.g:32:42: ( ^( VAR id= ID size= INT ) | ^( VAR id= ID sizeMin= INT sizeMax= INT ) )
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==VAR) ) {
                int LA3_1 = input.LA(2);

                if ( (LA3_1==DOWN) ) {
                    int LA3_2 = input.LA(3);

                    if ( (LA3_2==ID) ) {
                        int LA3_3 = input.LA(4);

                        if ( (LA3_3==INT) ) {
                            int LA3_4 = input.LA(5);

                            if ( (LA3_4==INT) ) {
                                alt3=2;
                            }
                            else if ( (LA3_4==UP) ) {
                                alt3=1;
                            }
                            else {
                                NoViableAltException nvae =
                                    new NoViableAltException("", 3, 4, input);

                                throw nvae;
                            }
                        }
                        else {
                            NoViableAltException nvae =
                                new NoViableAltException("", 3, 3, input);

                            throw nvae;
                        }
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("", 3, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 3, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }
            switch (alt3) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:33:1: ^( VAR id= ID size= INT )
                    {
                    match(input,VAR,FOLLOW_VAR_in_vardeclStmt289); 

                    match(input, Token.DOWN, null); 
                    id=(CommonTree)match(input,ID,FOLLOW_ID_in_vardeclStmt293); 
                    size=(CommonTree)match(input,INT,FOLLOW_INT_in_vardeclStmt303); 

                                    s = new HVarDeclStatement(id.getText(), size.getText());
                                  

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:40:3: ^( VAR id= ID sizeMin= INT sizeMax= INT )
                    {
                    match(input,VAR,FOLLOW_VAR_in_vardeclStmt339); 

                    match(input, Token.DOWN, null); 
                    id=(CommonTree)match(input,ID,FOLLOW_ID_in_vardeclStmt343); 
                    sizeMin=(CommonTree)match(input,INT,FOLLOW_INT_in_vardeclStmt355); 
                    sizeMax=(CommonTree)match(input,INT,FOLLOW_INT_in_vardeclStmt367); 
                     
                                  s = new HVarDeclStatement(id.getText(), sizeMin.getText(), sizeMax.getText());
                                

                    match(input, Token.UP, null); 

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return s;
    }
    // $ANTLR end vardeclStmt


    // $ANTLR start cfgStmt
    // src/hampi/parser/HampiTree.g:48:1: cfgStmt returns [CFGStatement s = new CFGStatement()] : ^( CFG ^( CFGPROD id= ID (cfgElemSet= cfgProductionElementSet )+ ) ) ;
    public final CFGStatement cfgStmt() throws RecognitionException {
        CFGStatement s =  new CFGStatement();

        CommonTree id=null;
        List cfgElemSet = null;


        try {
            // src/hampi/parser/HampiTree.g:48:54: ( ^( CFG ^( CFGPROD id= ID (cfgElemSet= cfgProductionElementSet )+ ) ) )
            // src/hampi/parser/HampiTree.g:49:1: ^( CFG ^( CFGPROD id= ID (cfgElemSet= cfgProductionElementSet )+ ) )
            {
            match(input,CFG,FOLLOW_CFG_in_cfgStmt407); 

            match(input, Token.DOWN, null); 
            match(input,CFGPROD,FOLLOW_CFGPROD_in_cfgStmt413); 

            match(input, Token.DOWN, null); 
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_cfgStmt417); 

                  s.setId(id.getText());
                
            // src/hampi/parser/HampiTree.g:55:5: (cfgElemSet= cfgProductionElementSet )+
            int cnt4=0;
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( (LA4_0==CFGPRODELEMSET) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // src/hampi/parser/HampiTree.g:55:6: cfgElemSet= cfgProductionElementSet
            	    {
            	    pushFollow(FOLLOW_cfgProductionElementSet_in_cfgStmt433);
            	    cfgElemSet=cfgProductionElementSet();

            	    state._fsp--;


            	          s.appendElementSet(cfgElemSet);
            	        

            	    }
            	    break;

            	default :
            	    if ( cnt4 >= 1 ) break loop4;
                        EarlyExitException eee =
                            new EarlyExitException(4, input);
                        throw eee;
                }
                cnt4++;
            } while (true);


            match(input, Token.UP, null); 

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return s;
    }
    // $ANTLR end cfgStmt


    // $ANTLR start cfgProductionElementSet
    // src/hampi/parser/HampiTree.g:62:1: cfgProductionElementSet returns [List list= new ArrayList()] : ^( CFGPRODELEMSET (el= cfgProdElement )* ) ;
    public final List cfgProductionElementSet() throws RecognitionException {
        List list =  new ArrayList();

        CFGProductionElement el = null;


        try {
            // src/hampi/parser/HampiTree.g:62:62: ( ^( CFGPRODELEMSET (el= cfgProdElement )* ) )
            // src/hampi/parser/HampiTree.g:63:2: ^( CFGPRODELEMSET (el= cfgProdElement )* )
            {
            match(input,CFGPRODELEMSET,FOLLOW_CFGPRODELEMSET_in_cfgProductionElementSet463); 

            if ( input.LA(1)==Token.DOWN ) {
                match(input, Token.DOWN, null); 
                // src/hampi/parser/HampiTree.g:64:4: (el= cfgProdElement )*
                loop5:
                do {
                    int alt5=2;
                    int LA5_0 = input.LA(1);

                    if ( ((LA5_0>=CFGOPTION && LA5_0<=CFGPLUS)||(LA5_0>=CFGCHARRANGE && LA5_0<=CFGCHARSEQRANGE)||LA5_0==ID||(LA5_0>=CHAR_SEQ && LA5_0<=STR_LIT)) ) {
                        alt5=1;
                    }


                    switch (alt5) {
                	case 1 :
                	    // src/hampi/parser/HampiTree.g:64:5: el= cfgProdElement
                	    {
                	    pushFollow(FOLLOW_cfgProdElement_in_cfgProductionElementSet472);
                	    el=cfgProdElement();

                	    state._fsp--;


                	         list.add(el);
                	       

                	    }
                	    break;

                	default :
                	    break loop5;
                    }
                } while (true);


                match(input, Token.UP, null); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return list;
    }
    // $ANTLR end cfgProductionElementSet


    // $ANTLR start cfgProdElement
    // src/hampi/parser/HampiTree.g:70:1: cfgProdElement returns [CFGProductionElement el = null] : (e1= cfgTerminal | e2= cfgNonterminal | e3= cfgOption | e4= cfgStar | e5= cfgPlus | e6= cfgCharRange | e7= cfgCharSeqRange ) ;
    public final CFGProductionElement cfgProdElement() throws RecognitionException {
        CFGProductionElement el =  null;

        CFGTerminal e1 = null;

        CFGNonterminal e2 = null;

        CFGOption e3 = null;

        CFGStar e4 = null;

        CFGPlus e5 = null;

        CFGCharRange e6 = null;

        CFGCharRange e7 = null;


        try {
            // src/hampi/parser/HampiTree.g:70:56: ( (e1= cfgTerminal | e2= cfgNonterminal | e3= cfgOption | e4= cfgStar | e5= cfgPlus | e6= cfgCharRange | e7= cfgCharSeqRange ) )
            // src/hampi/parser/HampiTree.g:71:3: (e1= cfgTerminal | e2= cfgNonterminal | e3= cfgOption | e4= cfgStar | e5= cfgPlus | e6= cfgCharRange | e7= cfgCharSeqRange )
            {
            // src/hampi/parser/HampiTree.g:71:3: (e1= cfgTerminal | e2= cfgNonterminal | e3= cfgOption | e4= cfgStar | e5= cfgPlus | e6= cfgCharRange | e7= cfgCharSeqRange )
            int alt6=7;
            switch ( input.LA(1) ) {
            case CHAR_SEQ:
            case STR_LIT:
                {
                alt6=1;
                }
                break;
            case ID:
                {
                alt6=2;
                }
                break;
            case CFGOPTION:
                {
                alt6=3;
                }
                break;
            case CFGSTAR:
                {
                alt6=4;
                }
                break;
            case CFGPLUS:
                {
                alt6=5;
                }
                break;
            case CFGCHARRANGE:
                {
                alt6=6;
                }
                break;
            case CFGCHARSEQRANGE:
                {
                alt6=7;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 6, 0, input);

                throw nvae;
            }

            switch (alt6) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:71:5: e1= cfgTerminal
                    {
                    pushFollow(FOLLOW_cfgTerminal_in_cfgProdElement499);
                    e1=cfgTerminal();

                    state._fsp--;

                    el=e1;

                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:72:5: e2= cfgNonterminal
                    {
                    pushFollow(FOLLOW_cfgNonterminal_in_cfgProdElement509);
                    e2=cfgNonterminal();

                    state._fsp--;

                    el=e2;

                    }
                    break;
                case 3 :
                    // src/hampi/parser/HampiTree.g:73:5: e3= cfgOption
                    {
                    pushFollow(FOLLOW_cfgOption_in_cfgProdElement519);
                    e3=cfgOption();

                    state._fsp--;

                    el=e3;

                    }
                    break;
                case 4 :
                    // src/hampi/parser/HampiTree.g:74:5: e4= cfgStar
                    {
                    pushFollow(FOLLOW_cfgStar_in_cfgProdElement529);
                    e4=cfgStar();

                    state._fsp--;

                    el=e4;

                    }
                    break;
                case 5 :
                    // src/hampi/parser/HampiTree.g:75:5: e5= cfgPlus
                    {
                    pushFollow(FOLLOW_cfgPlus_in_cfgProdElement539);
                    e5=cfgPlus();

                    state._fsp--;

                    el=e5;

                    }
                    break;
                case 6 :
                    // src/hampi/parser/HampiTree.g:76:5: e6= cfgCharRange
                    {
                    pushFollow(FOLLOW_cfgCharRange_in_cfgProdElement549);
                    e6=cfgCharRange();

                    state._fsp--;

                    el=e6;

                    }
                    break;
                case 7 :
                    // src/hampi/parser/HampiTree.g:77:5: e7= cfgCharSeqRange
                    {
                    pushFollow(FOLLOW_cfgCharSeqRange_in_cfgProdElement559);
                    e7=cfgCharSeqRange();

                    state._fsp--;

                    el=e7;

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return el;
    }
    // $ANTLR end cfgProdElement


    // $ANTLR start cfgTerminal
    // src/hampi/parser/HampiTree.g:81:1: cfgTerminal returns [CFGTerminal t= null] : (str= STR_LIT | seq= CHAR_SEQ ) ;
    public final CFGTerminal cfgTerminal() throws RecognitionException {
        CFGTerminal t =  null;

        CommonTree str=null;
        CommonTree seq=null;

        try {
            // src/hampi/parser/HampiTree.g:81:43: ( (str= STR_LIT | seq= CHAR_SEQ ) )
            // src/hampi/parser/HampiTree.g:82:3: (str= STR_LIT | seq= CHAR_SEQ )
            {
            // src/hampi/parser/HampiTree.g:82:3: (str= STR_LIT | seq= CHAR_SEQ )
            int alt7=2;
            int LA7_0 = input.LA(1);

            if ( (LA7_0==STR_LIT) ) {
                alt7=1;
            }
            else if ( (LA7_0==CHAR_SEQ) ) {
                alt7=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 7, 0, input);

                throw nvae;
            }
            switch (alt7) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:82:4: str= STR_LIT
                    {
                    str=(CommonTree)match(input,STR_LIT,FOLLOW_STR_LIT_in_cfgTerminal588); 
                     t = new CFGTerminal(str.getText()); 

                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:83:4: seq= CHAR_SEQ
                    {
                    seq=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_cfgTerminal598); 
                     int s = Integer.valueOf(seq.getText().substring(1,4)); // PIETER
                                      t = new CFGTerminal("\"" + String.valueOf((char)s) + "\""); 

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return t;
    }
    // $ANTLR end cfgTerminal


    // $ANTLR start cfgNonterminal
    // src/hampi/parser/HampiTree.g:87:1: cfgNonterminal returns [CFGNonterminal t= null] : (id= ID ) ;
    public final CFGNonterminal cfgNonterminal() throws RecognitionException {
        CFGNonterminal t =  null;

        CommonTree id=null;

        try {
            // src/hampi/parser/HampiTree.g:87:49: ( (id= ID ) )
            // src/hampi/parser/HampiTree.g:88:3: (id= ID )
            {
            // src/hampi/parser/HampiTree.g:88:3: (id= ID )
            // src/hampi/parser/HampiTree.g:88:4: id= ID
            {
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_cfgNonterminal623); 

                t = new CFGNonterminal(id.getText());
              

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return t;
    }
    // $ANTLR end cfgNonterminal


    // $ANTLR start cfgOption
    // src/hampi/parser/HampiTree.g:94:1: cfgOption returns [CFGOption t= null] : ^( CFGOPTION el= cfgProdElement ) ;
    public final CFGOption cfgOption() throws RecognitionException {
        CFGOption t =  null;

        CFGProductionElement el = null;


        try {
            // src/hampi/parser/HampiTree.g:94:39: ( ^( CFGOPTION el= cfgProdElement ) )
            // src/hampi/parser/HampiTree.g:95:3: ^( CFGOPTION el= cfgProdElement )
            {
            match(input,CFGOPTION,FOLLOW_CFGOPTION_in_cfgOption646); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cfgProdElement_in_cfgOption654);
            el=cfgProdElement();

            state._fsp--;


                t = new CFGOption(el);
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return t;
    }
    // $ANTLR end cfgOption


    // $ANTLR start cfgStar
    // src/hampi/parser/HampiTree.g:102:1: cfgStar returns [CFGStar t= null] : ^( CFGSTAR el= cfgProdElement ) ;
    public final CFGStar cfgStar() throws RecognitionException {
        CFGStar t =  null;

        CFGProductionElement el = null;


        try {
            // src/hampi/parser/HampiTree.g:102:35: ( ^( CFGSTAR el= cfgProdElement ) )
            // src/hampi/parser/HampiTree.g:103:3: ^( CFGSTAR el= cfgProdElement )
            {
            match(input,CFGSTAR,FOLLOW_CFGSTAR_in_cfgStar677); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cfgProdElement_in_cfgStar685);
            el=cfgProdElement();

            state._fsp--;


                t = new CFGStar(el);
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return t;
    }
    // $ANTLR end cfgStar


    // $ANTLR start cfgPlus
    // src/hampi/parser/HampiTree.g:110:1: cfgPlus returns [CFGPlus t= null] : ^( CFGPLUS el= cfgProdElement ) ;
    public final CFGPlus cfgPlus() throws RecognitionException {
        CFGPlus t =  null;

        CFGProductionElement el = null;


        try {
            // src/hampi/parser/HampiTree.g:110:35: ( ^( CFGPLUS el= cfgProdElement ) )
            // src/hampi/parser/HampiTree.g:111:3: ^( CFGPLUS el= cfgProdElement )
            {
            match(input,CFGPLUS,FOLLOW_CFGPLUS_in_cfgPlus708); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cfgProdElement_in_cfgPlus716);
            el=cfgProdElement();

            state._fsp--;


                t = new CFGPlus(el);
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return t;
    }
    // $ANTLR end cfgPlus


    // $ANTLR start cfgCharRange
    // src/hampi/parser/HampiTree.g:118:1: cfgCharRange returns [CFGCharRange r= null] : ^( CFGCHARRANGE ch1= CHAR_LIT ch2= CHAR_LIT ) ;
    public final CFGCharRange cfgCharRange() throws RecognitionException {
        CFGCharRange r =  null;

        CommonTree ch1=null;
        CommonTree ch2=null;

        try {
            // src/hampi/parser/HampiTree.g:118:44: ( ^( CFGCHARRANGE ch1= CHAR_LIT ch2= CHAR_LIT ) )
            // src/hampi/parser/HampiTree.g:119:1: ^( CFGCHARRANGE ch1= CHAR_LIT ch2= CHAR_LIT )
            {
            match(input,CFGCHARRANGE,FOLLOW_CFGCHARRANGE_in_cfgCharRange738); 

            match(input, Token.DOWN, null); 
            ch1=(CommonTree)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_cfgCharRange745); 
            ch2=(CommonTree)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_cfgCharRange752); 

                r = new CFGCharRange(ch1.getText(), ch2.getText());
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return r;
    }
    // $ANTLR end cfgCharRange


    // $ANTLR start cfgCharSeqRange
    // src/hampi/parser/HampiTree.g:127:1: cfgCharSeqRange returns [CFGCharRange r= null] : ^( CFGCHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ ) ;
    public final CFGCharRange cfgCharSeqRange() throws RecognitionException {
        CFGCharRange r =  null;

        CommonTree ch1=null;
        CommonTree ch2=null;

        try {
            // src/hampi/parser/HampiTree.g:127:47: ( ^( CFGCHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ ) )
            // src/hampi/parser/HampiTree.g:128:1: ^( CFGCHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ )
            {
            match(input,CFGCHARSEQRANGE,FOLLOW_CFGCHARSEQRANGE_in_cfgCharSeqRange773); 

            match(input, Token.DOWN, null); 
            ch1=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_cfgCharSeqRange780); 
            ch2=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_cfgCharSeqRange787); 

               int ch1i = Integer.valueOf(ch1.getText().substring(1,4)); 
               int ch2i = Integer.valueOf(ch2.getText().substring(1,4));
               String ch1s = ("'" + String.valueOf((char)ch1i) + "'");
               String ch2s = ("'" + String.valueOf((char)ch2i) + "'");
               r = new CFGCharRange(ch1s, ch2s);
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return r;
    }
    // $ANTLR end cfgCharSeqRange


    // $ANTLR start regStmt
    // src/hampi/parser/HampiTree.g:140:1: regStmt returns [HRegDeclStatement stmt = null] : ^( REG id= ID r= regDefinition ) ;
    public final HRegDeclStatement regStmt() throws RecognitionException {
        HRegDeclStatement stmt =  null;

        CommonTree id=null;
        HRegDefinition r = null;


        try {
            // src/hampi/parser/HampiTree.g:140:49: ( ^( REG id= ID r= regDefinition ) )
            // src/hampi/parser/HampiTree.g:141:2: ^( REG id= ID r= regDefinition )
            {
            match(input,REG,FOLLOW_REG_in_regStmt809); 

            match(input, Token.DOWN, null); 
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_regStmt813); 
            pushFollow(FOLLOW_regDefinition_in_regStmt824);
            r=regDefinition();

            state._fsp--;


                     stmt= new HRegDeclStatement(id.getText(), r);
                  

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return stmt;
    }
    // $ANTLR end regStmt


    // $ANTLR start regDefinition
    // src/hampi/parser/HampiTree.g:148:1: regDefinition returns [HRegDefinition def= null] : (s= regConst | sprime= regCharSeqConst | id= regVarRef | fix= cfgSizeFix | star= regStar | range= regRange | range= regSeqRange | or= regOr | concat= regConcat ) ;
    public final HRegDefinition regDefinition() throws RecognitionException {
        HRegDefinition def =  null;

        HRegDefinition s = null;

        HRegDefinition sprime = null;

        HRegDefinition id = null;

        HRegDefinition fix = null;

        HRegDefinition star = null;

        HRegDefinition range = null;

        HOrRegexp or = null;

        HConcatRegexp concat = null;


        try {
            // src/hampi/parser/HampiTree.g:148:49: ( (s= regConst | sprime= regCharSeqConst | id= regVarRef | fix= cfgSizeFix | star= regStar | range= regRange | range= regSeqRange | or= regOr | concat= regConcat ) )
            // src/hampi/parser/HampiTree.g:149:4: (s= regConst | sprime= regCharSeqConst | id= regVarRef | fix= cfgSizeFix | star= regStar | range= regRange | range= regSeqRange | or= regOr | concat= regConcat )
            {
            // src/hampi/parser/HampiTree.g:149:4: (s= regConst | sprime= regCharSeqConst | id= regVarRef | fix= cfgSizeFix | star= regStar | range= regRange | range= regSeqRange | or= regOr | concat= regConcat )
            int alt8=9;
            switch ( input.LA(1) ) {
            case STR_LIT:
                {
                alt8=1;
                }
                break;
            case CHAR_SEQ:
                {
                alt8=2;
                }
                break;
            case ID:
                {
                alt8=3;
                }
                break;
            case FIX:
                {
                alt8=4;
                }
                break;
            case STAR:
                {
                alt8=5;
                }
                break;
            case RANGE:
                {
                alt8=6;
                }
                break;
            case CHARSEQRANGE:
                {
                alt8=7;
                }
                break;
            case OR:
                {
                alt8=8;
                }
                break;
            case CONCAT:
                {
                alt8=9;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 8, 0, input);

                throw nvae;
            }

            switch (alt8) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:149:5: s= regConst
                    {
                    pushFollow(FOLLOW_regConst_in_regDefinition853);
                    s=regConst();

                    state._fsp--;

                     def = s;  

                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:150:5: sprime= regCharSeqConst
                    {
                    pushFollow(FOLLOW_regCharSeqConst_in_regDefinition869);
                    sprime=regCharSeqConst();

                    state._fsp--;

                     def = sprime; 

                    }
                    break;
                case 3 :
                    // src/hampi/parser/HampiTree.g:151:5: id= regVarRef
                    {
                    pushFollow(FOLLOW_regVarRef_in_regDefinition880);
                    id=regVarRef();

                    state._fsp--;

                     def = id;

                    }
                    break;
                case 4 :
                    // src/hampi/parser/HampiTree.g:152:5: fix= cfgSizeFix
                    {
                    pushFollow(FOLLOW_cfgSizeFix_in_regDefinition894);
                    fix=cfgSizeFix();

                    state._fsp--;

                     def = fix;

                    }
                    break;
                case 5 :
                    // src/hampi/parser/HampiTree.g:153:5: star= regStar
                    {
                    pushFollow(FOLLOW_regStar_in_regDefinition906);
                    star=regStar();

                    state._fsp--;

                     def = star;

                    }
                    break;
                case 6 :
                    // src/hampi/parser/HampiTree.g:154:5: range= regRange
                    {
                    pushFollow(FOLLOW_regRange_in_regDefinition920);
                    range=regRange();

                    state._fsp--;

                     def = range;

                    }
                    break;
                case 7 :
                    // src/hampi/parser/HampiTree.g:155:5: range= regSeqRange
                    {
                    pushFollow(FOLLOW_regSeqRange_in_regDefinition932);
                    range=regSeqRange();

                    state._fsp--;

                     def = range;

                    }
                    break;
                case 8 :
                    // src/hampi/parser/HampiTree.g:156:5: or= regOr
                    {
                    pushFollow(FOLLOW_regOr_in_regDefinition942);
                    or=regOr();

                    state._fsp--;

                     def = or;

                    }
                    break;
                case 9 :
                    // src/hampi/parser/HampiTree.g:157:5: concat= regConcat
                    {
                    pushFollow(FOLLOW_regConcat_in_regDefinition960);
                    concat=regConcat();

                    state._fsp--;

                     def = concat;

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regDefinition


    // $ANTLR start regVarRef
    // src/hampi/parser/HampiTree.g:161:1: regVarRef returns [HRegDefinition def= null] : (id= ID ) ;
    public final HRegDefinition regVarRef() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree id=null;

        try {
            // src/hampi/parser/HampiTree.g:161:45: ( (id= ID ) )
            // src/hampi/parser/HampiTree.g:162:1: (id= ID )
            {
            // src/hampi/parser/HampiTree.g:162:1: (id= ID )
            // src/hampi/parser/HampiTree.g:162:2: id= ID
            {
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_regVarRef982); 

                def = new HRegVarRef(id.getText());
              

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regVarRef


    // $ANTLR start regOr
    // src/hampi/parser/HampiTree.g:167:1: regOr returns [HOrRegexp def= null] : ^( OR (r= regDefinition )+ ) ;
    public final HOrRegexp regOr() throws RecognitionException {
        HOrRegexp def =  null;

        HRegDefinition r = null;


        try {
            // src/hampi/parser/HampiTree.g:167:36: ( ^( OR (r= regDefinition )+ ) )
            // src/hampi/parser/HampiTree.g:168:1: ^( OR (r= regDefinition )+ )
            {
            match(input,OR,FOLLOW_OR_in_regOr1000); 


                 def = new HOrRegexp();
               

            match(input, Token.DOWN, null); 
            // src/hampi/parser/HampiTree.g:172:4: (r= regDefinition )+
            int cnt9=0;
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( (LA9_0==FIX||LA9_0==CONCAT||(LA9_0>=RANGE && LA9_0<=OR)||LA9_0==ID||LA9_0==STAR||(LA9_0>=CHAR_SEQ && LA9_0<=STR_LIT)) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // src/hampi/parser/HampiTree.g:172:5: r= regDefinition
            	    {
            	    pushFollow(FOLLOW_regDefinition_in_regOr1014);
            	    r=regDefinition();

            	    state._fsp--;


            	          def.add(r);
            	        

            	    }
            	    break;

            	default :
            	    if ( cnt9 >= 1 ) break loop9;
                        EarlyExitException eee =
                            new EarlyExitException(9, input);
                        throw eee;
                }
                cnt9++;
            } while (true);


            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regOr


    // $ANTLR start regConcat
    // src/hampi/parser/HampiTree.g:179:1: regConcat returns [HConcatRegexp def= null] : ^( CONCAT (r= regDefinition )+ ) ;
    public final HConcatRegexp regConcat() throws RecognitionException {
        HConcatRegexp def =  null;

        HRegDefinition r = null;


        try {
            // src/hampi/parser/HampiTree.g:179:44: ( ^( CONCAT (r= regDefinition )+ ) )
            // src/hampi/parser/HampiTree.g:180:1: ^( CONCAT (r= regDefinition )+ )
            {
            match(input,CONCAT,FOLLOW_CONCAT_in_regConcat1042); 


                 def = new HConcatRegexp();
               

            match(input, Token.DOWN, null); 
            // src/hampi/parser/HampiTree.g:184:4: (r= regDefinition )+
            int cnt10=0;
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( (LA10_0==FIX||LA10_0==CONCAT||(LA10_0>=RANGE && LA10_0<=OR)||LA10_0==ID||LA10_0==STAR||(LA10_0>=CHAR_SEQ && LA10_0<=STR_LIT)) ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // src/hampi/parser/HampiTree.g:184:5: r= regDefinition
            	    {
            	    pushFollow(FOLLOW_regDefinition_in_regConcat1056);
            	    r=regDefinition();

            	    state._fsp--;


            	          def.add(r);
            	        

            	    }
            	    break;

            	default :
            	    if ( cnt10 >= 1 ) break loop10;
                        EarlyExitException eee =
                            new EarlyExitException(10, input);
                        throw eee;
                }
                cnt10++;
            } while (true);


            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regConcat


    // $ANTLR start regRange
    // src/hampi/parser/HampiTree.g:191:1: regRange returns [HRegDefinition def= null] : ^( RANGE low= CHAR_LIT high= CHAR_LIT ) ;
    public final HRegDefinition regRange() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree low=null;
        CommonTree high=null;

        try {
            // src/hampi/parser/HampiTree.g:191:44: ( ^( RANGE low= CHAR_LIT high= CHAR_LIT ) )
            // src/hampi/parser/HampiTree.g:192:2: ^( RANGE low= CHAR_LIT high= CHAR_LIT )
            {
            match(input,RANGE,FOLLOW_RANGE_in_regRange1085); 

            match(input, Token.DOWN, null); 
            low=(CommonTree)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_regRange1089); 
            high=(CommonTree)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_regRange1103); 

                       def = new HRangeRegexp(low.getText(), high.getText());
                     

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regRange


    // $ANTLR start regSeqRange
    // src/hampi/parser/HampiTree.g:199:1: regSeqRange returns [HRegDefinition def= null] : ^( CHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ ) ;
    public final HRegDefinition regSeqRange() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree ch1=null;
        CommonTree ch2=null;

        try {
            // src/hampi/parser/HampiTree.g:199:47: ( ^( CHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ ) )
            // src/hampi/parser/HampiTree.g:200:2: ^( CHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ )
            {
            match(input,CHARSEQRANGE,FOLLOW_CHARSEQRANGE_in_regSeqRange1140); 

            match(input, Token.DOWN, null); 
            ch1=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regSeqRange1144); 
            ch2=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regSeqRange1157); 

                       int ch1i = Integer.valueOf(ch1.getText().substring(1,4));
                       int ch2i = Integer.valueOf(ch2.getText().substring(1,4));
                       String ch1s = ("'" + String.valueOf((char)ch1i) + "'");
                       String ch2s = ("'" + String.valueOf((char)ch2i) + "'");
                       def = new HRangeRegexp(ch1s, ch2s);
                     

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regSeqRange


    // $ANTLR start regStar
    // src/hampi/parser/HampiTree.g:211:1: regStar returns [HRegDefinition def= null] : ^( STAR r= regDefinition ) ;
    public final HRegDefinition regStar() throws RecognitionException {
        HRegDefinition def =  null;

        HRegDefinition r = null;


        try {
            // src/hampi/parser/HampiTree.g:211:43: ( ^( STAR r= regDefinition ) )
            // src/hampi/parser/HampiTree.g:212:2: ^( STAR r= regDefinition )
            {
            match(input,STAR,FOLLOW_STAR_in_regStar1193); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_regDefinition_in_regStar1197);
            r=regDefinition();

            state._fsp--;


                  def = new HStarRegexp(r);
                

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regStar


    // $ANTLR start regConst
    // src/hampi/parser/HampiTree.g:217:1: regConst returns [HRegDefinition def= null] : (s= STR_LIT ) ;
    public final HRegDefinition regConst() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree s=null;

        try {
            // src/hampi/parser/HampiTree.g:217:44: ( (s= STR_LIT ) )
            // src/hampi/parser/HampiTree.g:218:2: (s= STR_LIT )
            {
            // src/hampi/parser/HampiTree.g:218:2: (s= STR_LIT )
            // src/hampi/parser/HampiTree.g:218:3: s= STR_LIT
            {
            s=(CommonTree)match(input,STR_LIT,FOLLOW_STR_LIT_in_regConst1220); 

                 def = new HConstRegexp(s.getText());
               

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regConst


    // $ANTLR start regCharSeqConst
    // src/hampi/parser/HampiTree.g:223:1: regCharSeqConst returns [HRegDefinition def= null] : (s= CHAR_SEQ ) ;
    public final HRegDefinition regCharSeqConst() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree s=null;

        try {
            // src/hampi/parser/HampiTree.g:223:51: ( (s= CHAR_SEQ ) )
            // src/hampi/parser/HampiTree.g:224:2: (s= CHAR_SEQ )
            {
            // src/hampi/parser/HampiTree.g:224:2: (s= CHAR_SEQ )
            // src/hampi/parser/HampiTree.g:224:3: s= CHAR_SEQ
            {
            s=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regCharSeqConst1243); 

                 int si = Integer.valueOf(s.getText().substring(1,4)); 
                 def = new HConstRegexp("\"" + String.valueOf((char)si) + "\"");
               

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regCharSeqConst


    // $ANTLR start cfgSizeFix
    // src/hampi/parser/HampiTree.g:230:1: cfgSizeFix returns [HRegDefinition def = null] : ^( FIX id= ID s= INT ) ;
    public final HRegDefinition cfgSizeFix() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree id=null;
        CommonTree s=null;

        try {
            // src/hampi/parser/HampiTree.g:230:48: ( ^( FIX id= ID s= INT ) )
            // src/hampi/parser/HampiTree.g:231:3: ^( FIX id= ID s= INT )
            {
            match(input,FIX,FOLLOW_FIX_in_cfgSizeFix1266); 

            match(input, Token.DOWN, null); 
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_cfgSizeFix1277); 
            s=(CommonTree)match(input,INT,FOLLOW_INT_in_cfgSizeFix1287); 

                   def = new HSizeFixRegDefinition(id.getText(), s.getText());
                 

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end cfgSizeFix


    // $ANTLR start valDeclStmt
    // src/hampi/parser/HampiTree.g:239:1: valDeclStmt returns [HValDeclStatement s = null] : ^( VAL id= ID e= expr ) ;
    public final HValDeclStatement valDeclStmt() throws RecognitionException {
        HValDeclStatement s =  null;

        CommonTree id=null;
        HExpression e = null;


        try {
            // src/hampi/parser/HampiTree.g:239:50: ( ^( VAL id= ID e= expr ) )
            // src/hampi/parser/HampiTree.g:240:2: ^( VAL id= ID e= expr )
            {
            match(input,VAL,FOLLOW_VAL_in_valDeclStmt1313); 

            match(input, Token.DOWN, null); 
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_valDeclStmt1320); 
            pushFollow(FOLLOW_expr_in_valDeclStmt1326);
            e=expr();

            state._fsp--;


                s= new HValDeclStatement(id.getText(), e);
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return s;
    }
    // $ANTLR end valDeclStmt


    // $ANTLR start expr
    // src/hampi/parser/HampiTree.g:248:1: expr returns [HExpression e = null] : ( (s= STR_LIT ) | (id= ID ) | ^( CONCAT (sube= expr )+ ) | ^( SUBSEQUENCE id= ID startIndex= INT len= INT ) );
    public final HExpression expr() throws RecognitionException {
        HExpression e =  null;

        CommonTree s=null;
        CommonTree id=null;
        CommonTree startIndex=null;
        CommonTree len=null;
        HExpression sube = null;


        try {
            // src/hampi/parser/HampiTree.g:248:37: ( (s= STR_LIT ) | (id= ID ) | ^( CONCAT (sube= expr )+ ) | ^( SUBSEQUENCE id= ID startIndex= INT len= INT ) )
            int alt12=4;
            switch ( input.LA(1) ) {
            case STR_LIT:
                {
                alt12=1;
                }
                break;
            case ID:
                {
                alt12=2;
                }
                break;
            case CONCAT:
                {
                alt12=3;
                }
                break;
            case SUBSEQUENCE:
                {
                alt12=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 12, 0, input);

                throw nvae;
            }

            switch (alt12) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:249:2: (s= STR_LIT )
                    {
                    // src/hampi/parser/HampiTree.g:249:2: (s= STR_LIT )
                    // src/hampi/parser/HampiTree.g:249:3: s= STR_LIT
                    {
                    s=(CommonTree)match(input,STR_LIT,FOLLOW_STR_LIT_in_expr1352); 

                        e = new HConstantExpression(s.getText());
                      

                    }


                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:255:2: (id= ID )
                    {
                    // src/hampi/parser/HampiTree.g:255:2: (id= ID )
                    // src/hampi/parser/HampiTree.g:255:3: id= ID
                    {
                    id=(CommonTree)match(input,ID,FOLLOW_ID_in_expr1368); 

                       e = new HVarReferenceExpression(id.getText());
                     

                    }


                    }
                    break;
                case 3 :
                    // src/hampi/parser/HampiTree.g:261:2: ^( CONCAT (sube= expr )+ )
                    {
                    match(input,CONCAT,FOLLOW_CONCAT_in_expr1383); 


                          HConcatExpression cat = new HConcatExpression();
                        

                    match(input, Token.DOWN, null); 
                    // src/hampi/parser/HampiTree.g:265:4: (sube= expr )+
                    int cnt11=0;
                    loop11:
                    do {
                        int alt11=2;
                        int LA11_0 = input.LA(1);

                        if ( ((LA11_0>=CONCAT && LA11_0<=SUBSEQUENCE)||LA11_0==ID||LA11_0==STR_LIT) ) {
                            alt11=1;
                        }


                        switch (alt11) {
                    	case 1 :
                    	    // src/hampi/parser/HampiTree.g:265:5: sube= expr
                    	    {
                    	    pushFollow(FOLLOW_expr_in_expr1398);
                    	    sube=expr();

                    	    state._fsp--;


                    	         cat.add(sube);
                    	       

                    	    }
                    	    break;

                    	default :
                    	    if ( cnt11 >= 1 ) break loop11;
                                EarlyExitException eee =
                                    new EarlyExitException(11, input);
                                throw eee;
                        }
                        cnt11++;
                    } while (true);


                         e = cat;
                       

                    match(input, Token.UP, null); 

                    }
                    break;
                case 4 :
                    // src/hampi/parser/HampiTree.g:276:3: ^( SUBSEQUENCE id= ID startIndex= INT len= INT )
                    {
                    match(input,SUBSEQUENCE,FOLLOW_SUBSEQUENCE_in_expr1429); 

                    match(input, Token.DOWN, null); 
                    id=(CommonTree)match(input,ID,FOLLOW_ID_in_expr1433); 
                    startIndex=(CommonTree)match(input,INT,FOLLOW_INT_in_expr1437); 
                    len=(CommonTree)match(input,INT,FOLLOW_INT_in_expr1441); 

                          e = new HSubsequenceExpression(id.getText(),startIndex.getText(),len.getText());
                        

                    match(input, Token.UP, null); 

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return e;
    }
    // $ANTLR end expr


    // $ANTLR start assertStmt
    // src/hampi/parser/HampiTree.g:282:1: assertStmt returns [HAssertStatement s= null] : ^( ASSERT b= boolExpr ) ;
    public final HAssertStatement assertStmt() throws RecognitionException {
        HAssertStatement s =  null;

        HBooleanExpression b = null;


        try {
            // src/hampi/parser/HampiTree.g:282:47: ( ^( ASSERT b= boolExpr ) )
            // src/hampi/parser/HampiTree.g:283:2: ^( ASSERT b= boolExpr )
            {
            match(input,ASSERT,FOLLOW_ASSERT_in_assertStmt1464); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_boolExpr_in_assertStmt1468);
            b=boolExpr();

            state._fsp--;


                 s = new HAssertStatement(b);
               

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return s;
    }
    // $ANTLR end assertStmt


    // $ANTLR start boolExpr
    // src/hampi/parser/HampiTree.g:290:1: boolExpr returns [HBooleanExpression b = null] : ( ^( IN id1= ID id2= ID ) | ^( CONTAINS id= ID str= STR_LIT ) | ^( NOTIN id1= ID id2= ID ) | ^( NOTCONTAINS id= ID str= STR_LIT ) | ^( TEQUALS id1= ID id2= ID ) | ^( TNOTEQUALS id1= ID id2= ID ) );
    public final HBooleanExpression boolExpr() throws RecognitionException {
        HBooleanExpression b =  null;

        CommonTree id1=null;
        CommonTree id2=null;
        CommonTree id=null;
        CommonTree str=null;

        try {
            // src/hampi/parser/HampiTree.g:290:48: ( ^( IN id1= ID id2= ID ) | ^( CONTAINS id= ID str= STR_LIT ) | ^( NOTIN id1= ID id2= ID ) | ^( NOTCONTAINS id= ID str= STR_LIT ) | ^( TEQUALS id1= ID id2= ID ) | ^( TNOTEQUALS id1= ID id2= ID ) )
            int alt13=6;
            switch ( input.LA(1) ) {
            case IN:
                {
                alt13=1;
                }
                break;
            case CONTAINS:
                {
                alt13=2;
                }
                break;
            case NOTIN:
                {
                alt13=3;
                }
                break;
            case NOTCONTAINS:
                {
                alt13=4;
                }
                break;
            case TEQUALS:
                {
                alt13=5;
                }
                break;
            case TNOTEQUALS:
                {
                alt13=6;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 13, 0, input);

                throw nvae;
            }

            switch (alt13) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:291:5: ^( IN id1= ID id2= ID )
                    {
                    match(input,IN,FOLLOW_IN_in_boolExpr1496); 

                    match(input, Token.DOWN, null); 
                    id1=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1500); 
                    id2=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1504); 

                          b = new HInExpression(id1.getText(), id2.getText(), true);
                        

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:296:5: ^( CONTAINS id= ID str= STR_LIT )
                    {
                    match(input,CONTAINS,FOLLOW_CONTAINS_in_boolExpr1523); 

                    match(input, Token.DOWN, null); 
                    id=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1527); 
                    str=(CommonTree)match(input,STR_LIT,FOLLOW_STR_LIT_in_boolExpr1531); 

                          b = new HContainsExpression(id.getText(), str.getText(), true);
                      

                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // src/hampi/parser/HampiTree.g:302:5: ^( NOTIN id1= ID id2= ID )
                    {
                    match(input,NOTIN,FOLLOW_NOTIN_in_boolExpr1550); 

                    match(input, Token.DOWN, null); 
                    id1=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1554); 
                    id2=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1558); 

                          b = new HInExpression(id1.getText(), id2.getText(), false);
                        

                    match(input, Token.UP, null); 

                    }
                    break;
                case 4 :
                    // src/hampi/parser/HampiTree.g:307:5: ^( NOTCONTAINS id= ID str= STR_LIT )
                    {
                    match(input,NOTCONTAINS,FOLLOW_NOTCONTAINS_in_boolExpr1577); 

                    match(input, Token.DOWN, null); 
                    id=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1581); 
                    str=(CommonTree)match(input,STR_LIT,FOLLOW_STR_LIT_in_boolExpr1585); 

                          b = new HContainsExpression(id.getText(), str.getText(), false);
                      

                    match(input, Token.UP, null); 

                    }
                    break;
                case 5 :
                    // src/hampi/parser/HampiTree.g:312:5: ^( TEQUALS id1= ID id2= ID )
                    {
                    match(input,TEQUALS,FOLLOW_TEQUALS_in_boolExpr1600); 

                    match(input, Token.DOWN, null); 
                    id1=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1604); 
                    id2=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1608); 

                          b = new HEqualsExpression(id1.getText(), id2.getText(), true);
                      

                    match(input, Token.UP, null); 

                    }
                    break;
                case 6 :
                    // src/hampi/parser/HampiTree.g:317:5: ^( TNOTEQUALS id1= ID id2= ID )
                    {
                    match(input,TNOTEQUALS,FOLLOW_TNOTEQUALS_in_boolExpr1623); 

                    match(input, Token.DOWN, null); 
                    id1=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1627); 
                    id2=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1631); 

                          b = new HEqualsExpression(id1.getText(), id2.getText(), false);
                      

                    match(input, Token.UP, null); 

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return b;
    }
    // $ANTLR end boolExpr

    // Delegated rules


 

    public static final BitSet FOLLOW_PROGRAM_in_program56 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_statement_in_program72 = new BitSet(new long[]{0x00000000003C8008L});
    public static final BitSet FOLLOW_vardeclStmt_in_statement151 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgStmt_in_statement174 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regStmt_in_statement198 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_valDeclStmt_in_statement222 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_assertStmt_in_statement245 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_in_vardeclStmt289 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_vardeclStmt293 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_vardeclStmt303 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_VAR_in_vardeclStmt339 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_vardeclStmt343 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_vardeclStmt355 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_vardeclStmt367 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CFG_in_cfgStmt407 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CFGPROD_in_cfgStmt413 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_cfgStmt417 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_cfgProductionElementSet_in_cfgStmt433 = new BitSet(new long[]{0x0000000040000008L});
    public static final BitSet FOLLOW_CFGPRODELEMSET_in_cfgProductionElementSet463 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cfgProdElement_in_cfgProductionElementSet472 = new BitSet(new long[]{0x0003000430000388L});
    public static final BitSet FOLLOW_cfgTerminal_in_cfgProdElement499 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgNonterminal_in_cfgProdElement509 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgOption_in_cfgProdElement519 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgStar_in_cfgProdElement529 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgPlus_in_cfgProdElement539 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgCharRange_in_cfgProdElement549 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgCharSeqRange_in_cfgProdElement559 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_STR_LIT_in_cfgTerminal588 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_cfgTerminal598 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_cfgNonterminal623 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CFGOPTION_in_cfgOption646 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cfgProdElement_in_cfgOption654 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CFGSTAR_in_cfgStar677 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cfgProdElement_in_cfgStar685 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CFGPLUS_in_cfgPlus708 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cfgProdElement_in_cfgPlus716 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CFGCHARRANGE_in_cfgCharRange738 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHAR_LIT_in_cfgCharRange745 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_cfgCharRange752 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CFGCHARSEQRANGE_in_cfgCharSeqRange773 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_cfgCharSeqRange780 = new BitSet(new long[]{0x0001000000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_cfgCharSeqRange787 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_REG_in_regStmt809 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_regStmt813 = new BitSet(new long[]{0x0003040403811000L});
    public static final BitSet FOLLOW_regDefinition_in_regStmt824 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_regConst_in_regDefinition853 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regCharSeqConst_in_regDefinition869 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regVarRef_in_regDefinition880 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgSizeFix_in_regDefinition894 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regStar_in_regDefinition906 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regRange_in_regDefinition920 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regSeqRange_in_regDefinition932 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regOr_in_regDefinition942 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regConcat_in_regDefinition960 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_regVarRef982 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OR_in_regOr1000 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_regDefinition_in_regOr1014 = new BitSet(new long[]{0x0003040403811008L});
    public static final BitSet FOLLOW_CONCAT_in_regConcat1042 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_regDefinition_in_regConcat1056 = new BitSet(new long[]{0x0003040403811008L});
    public static final BitSet FOLLOW_RANGE_in_regRange1085 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHAR_LIT_in_regRange1089 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_regRange1103 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHARSEQRANGE_in_regSeqRange1140 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regSeqRange1144 = new BitSet(new long[]{0x0001000000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regSeqRange1157 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STAR_in_regStar1193 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_regDefinition_in_regStar1197 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STR_LIT_in_regConst1220 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regCharSeqConst1243 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_FIX_in_cfgSizeFix1266 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_cfgSizeFix1277 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_cfgSizeFix1287 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_VAL_in_valDeclStmt1313 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_valDeclStmt1320 = new BitSet(new long[]{0x0002000400030000L});
    public static final BitSet FOLLOW_expr_in_valDeclStmt1326 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STR_LIT_in_expr1352 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_expr1368 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONCAT_in_expr1383 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_expr_in_expr1398 = new BitSet(new long[]{0x0002000400030008L});
    public static final BitSet FOLLOW_SUBSEQUENCE_in_expr1429 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_expr1433 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_expr1437 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_expr1441 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_ASSERT_in_assertStmt1464 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_boolExpr_in_assertStmt1468 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_IN_in_boolExpr1496 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_boolExpr1500 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1504 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONTAINS_in_boolExpr1523 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_boolExpr1527 = new BitSet(new long[]{0x0002000000000000L});
    public static final BitSet FOLLOW_STR_LIT_in_boolExpr1531 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NOTIN_in_boolExpr1550 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_boolExpr1554 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1558 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NOTCONTAINS_in_boolExpr1577 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_boolExpr1581 = new BitSet(new long[]{0x0002000000000000L});
    public static final BitSet FOLLOW_STR_LIT_in_boolExpr1585 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TEQUALS_in_boolExpr1600 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_boolExpr1604 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1608 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_TNOTEQUALS_in_boolExpr1623 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_boolExpr1627 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1631 = new BitSet(new long[]{0x0000000000000008L});

}