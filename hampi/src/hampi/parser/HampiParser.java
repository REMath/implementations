// $ANTLR 3.1b1 src/hampi/parser/Hampi.g 2010-05-27 10:36:54
 
     package hampi.parser; 
   

import org.antlr.runtime.*;
import org.antlr.runtime.tree.*;

public class HampiParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "CFGPROD", "ASSIGN", "PROGRAM", "CFGOPTION", "CFGSTAR", "CFGPLUS", "TEQUALS", "TNOTEQUALS", "FIX", "CONTAINS", "IN", "ASSERT", "CONCAT", "SUBSEQUENCE", "VAR", "CFG", "REG", "VAL", "CONST", "RANGE", "CHARSEQRANGE", "OR", "NOTIN", "NOTCONTAINS", "CFGCHARRANGE", "CFGCHARSEQRANGE", "CFGPRODELEMSET", "VALS", "SEMI", "KW_VAR", "ID", "COLON", "INT", "KW_CFG", "BAR", "LPAREN", "RPAREN", "QUESTION", "STAR", "PLUS", "LSQUARE", "CHAR_LIT", "MINUS", "RSQUARE", "CHAR_SEQ", "STR_LIT", "KW_REG", "KW_FIX", "COMMA", "KW_STAR", "KW_OR", "KW_CONCAT", "KW_VAL", "KW_ASSERT", "KW_IN", "KW_CONTAINS", "KW_NOT", "KW_EQUALS", "KW_QUERY", "EQUALS", "NOTEQUALS", "EscapeSequence", "NEWLINE", "WS", "COMMENT", "LINE_COMMENT", "'..'"
    };
    public static final int CFGSTAR=8;
    public static final int FIX=12;
    public static final int STAR=42;
    public static final int KW_VAL=56;
    public static final int LSQUARE=44;
    public static final int KW_EQUALS=61;
    public static final int CFGPROD=4;
    public static final int CONST=22;
    public static final int CONTAINS=13;
    public static final int EQUALS=63;
    public static final int ID=34;
    public static final int EOF=-1;
    public static final int CFG=19;
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
    public static final int COMMENT=68;
    public static final int NOTCONTAINS=27;
    public static final int KW_FIX=51;
    public static final int KW_REG=50;
    public static final int LINE_COMMENT=69;
    public static final int CONCAT=16;
    public static final int KW_ASSERT=57;
    public static final int STR_LIT=49;
    public static final int NOTEQUALS=64;
    public static final int KW_QUERY=62;
    public static final int RANGE=23;
    public static final int SUBSEQUENCE=17;
    public static final int INT=36;
    public static final int CHAR_LIT=45;
    public static final int RSQUARE=47;
    public static final int MINUS=46;
    public static final int REG=20;
    public static final int ASSERT=15;
    public static final int TNOTEQUALS=11;
    public static final int SEMI=32;
    public static final int CFGCHARSEQRANGE=29;
    public static final int CFGPLUS=9;
    public static final int COLON=35;
    public static final int WS=67;
    public static final int NEWLINE=66;
    public static final int KW_CONCAT=55;
    public static final int QUESTION=41;
    public static final int T__70=70;
    public static final int KW_OR=54;
    public static final int KW_CONTAINS=59;
    public static final int CHARSEQRANGE=24;
    public static final int OR=25;
    public static final int ASSIGN=5;
    public static final int PROGRAM=6;
    public static final int KW_STAR=53;
    public static final int EscapeSequence=65;
    public static final int BAR=38;
    public static final int KW_NOT=60;
    public static final int KW_CFG=37;
    public static final int NOTIN=26;

    // delegates
    // delegators


        public HampiParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public HampiParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
        }
        
    protected TreeAdaptor adaptor = new CommonTreeAdaptor();

    public void setTreeAdaptor(TreeAdaptor adaptor) {
        this.adaptor = adaptor;
    }
    public TreeAdaptor getTreeAdaptor() {
        return adaptor;
    }

    public String[] getTokenNames() { return HampiParser.tokenNames; }
    public String getGrammarFileName() { return "src/hampi/parser/Hampi.g"; }


    public static class program_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start program
    // src/hampi/parser/Hampi.g:50:2: program : ( statement SEMI )+ -> ^( PROGRAM ( statement )+ ) ;
    public final HampiParser.program_return program() throws RecognitionException {
        HampiParser.program_return retval = new HampiParser.program_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token SEMI2=null;
        HampiParser.statement_return statement1 = null;


        Object SEMI2_tree=null;
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");
        try {
            // src/hampi/parser/Hampi.g:50:10: ( ( statement SEMI )+ -> ^( PROGRAM ( statement )+ ) )
            // src/hampi/parser/Hampi.g:50:12: ( statement SEMI )+
            {
            // src/hampi/parser/Hampi.g:50:12: ( statement SEMI )+
            int cnt1=0;
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0==KW_VAR||LA1_0==KW_CFG||LA1_0==KW_REG||(LA1_0>=KW_VAL && LA1_0<=KW_ASSERT)) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // src/hampi/parser/Hampi.g:50:13: statement SEMI
            	    {
            	    pushFollow(FOLLOW_statement_in_program300);
            	    statement1=statement();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) stream_statement.add(statement1.getTree());
            	    SEMI2=(Token)match(input,SEMI,FOLLOW_SEMI_in_program302); if (state.failed) return retval; 
            	    if ( state.backtracking==0 ) stream_SEMI.add(SEMI2);


            	    }
            	    break;

            	default :
            	    if ( cnt1 >= 1 ) break loop1;
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(1, input);
                        throw eee;
                }
                cnt1++;
            } while (true);



            // AST REWRITE
            // elements: statement
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (Object)adaptor.nil();
            // 50:30: -> ^( PROGRAM ( statement )+ )
            {
                // src/hampi/parser/Hampi.g:50:33: ^( PROGRAM ( statement )+ )
                {
                Object root_1 = (Object)adaptor.nil();
                root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PROGRAM, "PROGRAM"), root_1);

                if ( !(stream_statement.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_statement.hasNext() ) {
                    adaptor.addChild(root_1, stream_statement.nextTree());

                }
                stream_statement.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end program

    public static class statement_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start statement
    // src/hampi/parser/Hampi.g:52:2: statement : ( vardeclStmt | cfgStmt | regStmt | valDeclStmt | assertStmt );
    public final HampiParser.statement_return statement() throws RecognitionException {
        HampiParser.statement_return retval = new HampiParser.statement_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        HampiParser.vardeclStmt_return vardeclStmt3 = null;

        HampiParser.cfgStmt_return cfgStmt4 = null;

        HampiParser.regStmt_return regStmt5 = null;

        HampiParser.valDeclStmt_return valDeclStmt6 = null;

        HampiParser.assertStmt_return assertStmt7 = null;



        try {
            // src/hampi/parser/Hampi.g:52:12: ( vardeclStmt | cfgStmt | regStmt | valDeclStmt | assertStmt )
            int alt2=5;
            switch ( input.LA(1) ) {
            case KW_VAR:
                {
                alt2=1;
                }
                break;
            case KW_CFG:
                {
                alt2=2;
                }
                break;
            case KW_REG:
                {
                alt2=3;
                }
                break;
            case KW_VAL:
                {
                alt2=4;
                }
                break;
            case KW_ASSERT:
                {
                alt2=5;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 2, 0, input);

                throw nvae;
            }

            switch (alt2) {
                case 1 :
                    // src/hampi/parser/Hampi.g:52:14: vardeclStmt
                    {
                    root_0 = (Object)adaptor.nil();

                    pushFollow(FOLLOW_vardeclStmt_in_statement323);
                    vardeclStmt3=vardeclStmt();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, vardeclStmt3.getTree());

                    }
                    break;
                case 2 :
                    // src/hampi/parser/Hampi.g:53:14: cfgStmt
                    {
                    root_0 = (Object)adaptor.nil();

                    pushFollow(FOLLOW_cfgStmt_in_statement339);
                    cfgStmt4=cfgStmt();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, cfgStmt4.getTree());

                    }
                    break;
                case 3 :
                    // src/hampi/parser/Hampi.g:54:14: regStmt
                    {
                    root_0 = (Object)adaptor.nil();

                    pushFollow(FOLLOW_regStmt_in_statement354);
                    regStmt5=regStmt();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, regStmt5.getTree());

                    }
                    break;
                case 4 :
                    // src/hampi/parser/Hampi.g:55:14: valDeclStmt
                    {
                    root_0 = (Object)adaptor.nil();

                    pushFollow(FOLLOW_valDeclStmt_in_statement369);
                    valDeclStmt6=valDeclStmt();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, valDeclStmt6.getTree());

                    }
                    break;
                case 5 :
                    // src/hampi/parser/Hampi.g:56:14: assertStmt
                    {
                    root_0 = (Object)adaptor.nil();

                    pushFollow(FOLLOW_assertStmt_in_statement384);
                    assertStmt7=assertStmt();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) adaptor.addChild(root_0, assertStmt7.getTree());

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end statement

    public static class vardeclStmt_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start vardeclStmt
    // src/hampi/parser/Hampi.g:59:2: vardeclStmt : ( ( KW_VAR ID COLON INT '..' INT ) -> ^( VAR ID INT INT ) | ( KW_VAR ID COLON INT ) -> ^( VAR ID INT ) );
    public final HampiParser.vardeclStmt_return vardeclStmt() throws RecognitionException {
        HampiParser.vardeclStmt_return retval = new HampiParser.vardeclStmt_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token KW_VAR8=null;
        Token ID9=null;
        Token COLON10=null;
        Token INT11=null;
        Token string_literal12=null;
        Token INT13=null;
        Token KW_VAR14=null;
        Token ID15=null;
        Token COLON16=null;
        Token INT17=null;

        Object KW_VAR8_tree=null;
        Object ID9_tree=null;
        Object COLON10_tree=null;
        Object INT11_tree=null;
        Object string_literal12_tree=null;
        Object INT13_tree=null;
        Object KW_VAR14_tree=null;
        Object ID15_tree=null;
        Object COLON16_tree=null;
        Object INT17_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_INT=new RewriteRuleTokenStream(adaptor,"token INT");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_70=new RewriteRuleTokenStream(adaptor,"token 70");
        RewriteRuleTokenStream stream_KW_VAR=new RewriteRuleTokenStream(adaptor,"token KW_VAR");

        try {
            // src/hampi/parser/Hampi.g:59:14: ( ( KW_VAR ID COLON INT '..' INT ) -> ^( VAR ID INT INT ) | ( KW_VAR ID COLON INT ) -> ^( VAR ID INT ) )
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==KW_VAR) ) {
                int LA3_1 = input.LA(2);

                if ( (LA3_1==ID) ) {
                    int LA3_2 = input.LA(3);

                    if ( (LA3_2==COLON) ) {
                        int LA3_3 = input.LA(4);

                        if ( (LA3_3==INT) ) {
                            int LA3_4 = input.LA(5);

                            if ( (LA3_4==70) ) {
                                alt3=1;
                            }
                            else if ( (LA3_4==EOF||LA3_4==SEMI) ) {
                                alt3=2;
                            }
                            else {
                                if (state.backtracking>0) {state.failed=true; return retval;}
                                NoViableAltException nvae =
                                    new NoViableAltException("", 3, 4, input);

                                throw nvae;
                            }
                        }
                        else {
                            if (state.backtracking>0) {state.failed=true; return retval;}
                            NoViableAltException nvae =
                                new NoViableAltException("", 3, 3, input);

                            throw nvae;
                        }
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 3, 2, input);

                        throw nvae;
                    }
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 3, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }
            switch (alt3) {
                case 1 :
                    // src/hampi/parser/Hampi.g:59:18: ( KW_VAR ID COLON INT '..' INT )
                    {
                    // src/hampi/parser/Hampi.g:59:18: ( KW_VAR ID COLON INT '..' INT )
                    // src/hampi/parser/Hampi.g:59:19: KW_VAR ID COLON INT '..' INT
                    {
                    KW_VAR8=(Token)match(input,KW_VAR,FOLLOW_KW_VAR_in_vardeclStmt419); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_VAR.add(KW_VAR8);

                    ID9=(Token)match(input,ID,FOLLOW_ID_in_vardeclStmt421); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID9);

                    COLON10=(Token)match(input,COLON,FOLLOW_COLON_in_vardeclStmt423); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_COLON.add(COLON10);

                    INT11=(Token)match(input,INT,FOLLOW_INT_in_vardeclStmt425); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_INT.add(INT11);

                    string_literal12=(Token)match(input,70,FOLLOW_70_in_vardeclStmt427); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_70.add(string_literal12);

                    INT13=(Token)match(input,INT,FOLLOW_INT_in_vardeclStmt429); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_INT.add(INT13);


                    }



                    // AST REWRITE
                    // elements: INT, INT, ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 59:49: -> ^( VAR ID INT INT )
                    {
                        // src/hampi/parser/Hampi.g:59:52: ^( VAR ID INT INT )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(VAR, "VAR"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_INT.nextNode());
                        adaptor.addChild(root_1, stream_INT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 2 :
                    // src/hampi/parser/Hampi.g:60:21: ( KW_VAR ID COLON INT )
                    {
                    // src/hampi/parser/Hampi.g:60:21: ( KW_VAR ID COLON INT )
                    // src/hampi/parser/Hampi.g:60:22: KW_VAR ID COLON INT
                    {
                    KW_VAR14=(Token)match(input,KW_VAR,FOLLOW_KW_VAR_in_vardeclStmt465); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_VAR.add(KW_VAR14);

                    ID15=(Token)match(input,ID,FOLLOW_ID_in_vardeclStmt467); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID15);

                    COLON16=(Token)match(input,COLON,FOLLOW_COLON_in_vardeclStmt469); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_COLON.add(COLON16);

                    INT17=(Token)match(input,INT,FOLLOW_INT_in_vardeclStmt471); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_INT.add(INT17);


                    }



                    // AST REWRITE
                    // elements: ID, INT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 60:43: -> ^( VAR ID INT )
                    {
                        // src/hampi/parser/Hampi.g:60:46: ^( VAR ID INT )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(VAR, "VAR"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_INT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end vardeclStmt

    public static class cfgStmt_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgStmt
    // src/hampi/parser/Hampi.g:63:2: cfgStmt : ( KW_CFG cfgProduction ) -> ^( CFG cfgProduction ) ;
    public final HampiParser.cfgStmt_return cfgStmt() throws RecognitionException {
        HampiParser.cfgStmt_return retval = new HampiParser.cfgStmt_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token KW_CFG18=null;
        HampiParser.cfgProduction_return cfgProduction19 = null;


        Object KW_CFG18_tree=null;
        RewriteRuleTokenStream stream_KW_CFG=new RewriteRuleTokenStream(adaptor,"token KW_CFG");
        RewriteRuleSubtreeStream stream_cfgProduction=new RewriteRuleSubtreeStream(adaptor,"rule cfgProduction");
        try {
            // src/hampi/parser/Hampi.g:63:10: ( ( KW_CFG cfgProduction ) -> ^( CFG cfgProduction ) )
            // src/hampi/parser/Hampi.g:63:12: ( KW_CFG cfgProduction )
            {
            // src/hampi/parser/Hampi.g:63:12: ( KW_CFG cfgProduction )
            // src/hampi/parser/Hampi.g:63:13: KW_CFG cfgProduction
            {
            KW_CFG18=(Token)match(input,KW_CFG,FOLLOW_KW_CFG_in_cfgStmt510); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_KW_CFG.add(KW_CFG18);

            pushFollow(FOLLOW_cfgProduction_in_cfgStmt512);
            cfgProduction19=cfgProduction();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) stream_cfgProduction.add(cfgProduction19.getTree());

            }



            // AST REWRITE
            // elements: cfgProduction
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (Object)adaptor.nil();
            // 63:35: -> ^( CFG cfgProduction )
            {
                // src/hampi/parser/Hampi.g:63:38: ^( CFG cfgProduction )
                {
                Object root_1 = (Object)adaptor.nil();
                root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CFG, "CFG"), root_1);

                adaptor.addChild(root_1, stream_cfgProduction.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgStmt

    public static class cfgProduction_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgProduction
    // src/hampi/parser/Hampi.g:65:2: cfgProduction : ( ID ASSIGN cfgProductionSet ) -> ^( CFGPROD ID cfgProductionSet ) ;
    public final HampiParser.cfgProduction_return cfgProduction() throws RecognitionException {
        HampiParser.cfgProduction_return retval = new HampiParser.cfgProduction_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token ID20=null;
        Token ASSIGN21=null;
        HampiParser.cfgProductionSet_return cfgProductionSet22 = null;


        Object ID20_tree=null;
        Object ASSIGN21_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
        RewriteRuleSubtreeStream stream_cfgProductionSet=new RewriteRuleSubtreeStream(adaptor,"rule cfgProductionSet");
        try {
            // src/hampi/parser/Hampi.g:65:16: ( ( ID ASSIGN cfgProductionSet ) -> ^( CFGPROD ID cfgProductionSet ) )
            // src/hampi/parser/Hampi.g:65:18: ( ID ASSIGN cfgProductionSet )
            {
            // src/hampi/parser/Hampi.g:65:18: ( ID ASSIGN cfgProductionSet )
            // src/hampi/parser/Hampi.g:65:19: ID ASSIGN cfgProductionSet
            {
            ID20=(Token)match(input,ID,FOLLOW_ID_in_cfgProduction532); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_ID.add(ID20);

            ASSIGN21=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_cfgProduction534); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_ASSIGN.add(ASSIGN21);

            pushFollow(FOLLOW_cfgProductionSet_in_cfgProduction537);
            cfgProductionSet22=cfgProductionSet();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) stream_cfgProductionSet.add(cfgProductionSet22.getTree());

            }



            // AST REWRITE
            // elements: cfgProductionSet, ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (Object)adaptor.nil();
            // 65:49: -> ^( CFGPROD ID cfgProductionSet )
            {
                // src/hampi/parser/Hampi.g:65:52: ^( CFGPROD ID cfgProductionSet )
                {
                Object root_1 = (Object)adaptor.nil();
                root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CFGPROD, "CFGPROD"), root_1);

                adaptor.addChild(root_1, stream_ID.nextNode());
                adaptor.addChild(root_1, stream_cfgProductionSet.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgProduction

    public static class cfgProductionSet_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgProductionSet
    // src/hampi/parser/Hampi.g:67:2: cfgProductionSet : ( cfgProductionElementSet ( BAR cfgProductionElementSet )* ) -> ( cfgProductionElementSet )+ ;
    public final HampiParser.cfgProductionSet_return cfgProductionSet() throws RecognitionException {
        HampiParser.cfgProductionSet_return retval = new HampiParser.cfgProductionSet_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token BAR24=null;
        HampiParser.cfgProductionElementSet_return cfgProductionElementSet23 = null;

        HampiParser.cfgProductionElementSet_return cfgProductionElementSet25 = null;


        Object BAR24_tree=null;
        RewriteRuleTokenStream stream_BAR=new RewriteRuleTokenStream(adaptor,"token BAR");
        RewriteRuleSubtreeStream stream_cfgProductionElementSet=new RewriteRuleSubtreeStream(adaptor,"rule cfgProductionElementSet");
        try {
            // src/hampi/parser/Hampi.g:67:19: ( ( cfgProductionElementSet ( BAR cfgProductionElementSet )* ) -> ( cfgProductionElementSet )+ )
            // src/hampi/parser/Hampi.g:67:21: ( cfgProductionElementSet ( BAR cfgProductionElementSet )* )
            {
            // src/hampi/parser/Hampi.g:67:21: ( cfgProductionElementSet ( BAR cfgProductionElementSet )* )
            // src/hampi/parser/Hampi.g:67:22: cfgProductionElementSet ( BAR cfgProductionElementSet )*
            {
            pushFollow(FOLLOW_cfgProductionElementSet_in_cfgProductionSet561);
            cfgProductionElementSet23=cfgProductionElementSet();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) stream_cfgProductionElementSet.add(cfgProductionElementSet23.getTree());
            // src/hampi/parser/Hampi.g:67:46: ( BAR cfgProductionElementSet )*
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( (LA4_0==BAR) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // src/hampi/parser/Hampi.g:67:47: BAR cfgProductionElementSet
            	    {
            	    BAR24=(Token)match(input,BAR,FOLLOW_BAR_in_cfgProductionSet564); if (state.failed) return retval; 
            	    if ( state.backtracking==0 ) stream_BAR.add(BAR24);

            	    pushFollow(FOLLOW_cfgProductionElementSet_in_cfgProductionSet566);
            	    cfgProductionElementSet25=cfgProductionElementSet();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) stream_cfgProductionElementSet.add(cfgProductionElementSet25.getTree());

            	    }
            	    break;

            	default :
            	    break loop4;
                }
            } while (true);


            }



            // AST REWRITE
            // elements: cfgProductionElementSet
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (Object)adaptor.nil();
            // 67:78: -> ( cfgProductionElementSet )+
            {
                if ( !(stream_cfgProductionElementSet.hasNext()) ) {
                    throw new RewriteEarlyExitException();
                }
                while ( stream_cfgProductionElementSet.hasNext() ) {
                    adaptor.addChild(root_0, stream_cfgProductionElementSet.nextTree());

                }
                stream_cfgProductionElementSet.reset();

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgProductionSet

    public static class cfgProductionElementSet_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgProductionElementSet
    // src/hampi/parser/Hampi.g:69:2: cfgProductionElementSet : ( ( cfgProductionElement )* ) -> ^( CFGPRODELEMSET ( cfgProductionElement )* ) ;
    public final HampiParser.cfgProductionElementSet_return cfgProductionElementSet() throws RecognitionException {
        HampiParser.cfgProductionElementSet_return retval = new HampiParser.cfgProductionElementSet_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        HampiParser.cfgProductionElement_return cfgProductionElement26 = null;


        RewriteRuleSubtreeStream stream_cfgProductionElement=new RewriteRuleSubtreeStream(adaptor,"rule cfgProductionElement");
        try {
            // src/hampi/parser/Hampi.g:69:26: ( ( ( cfgProductionElement )* ) -> ^( CFGPRODELEMSET ( cfgProductionElement )* ) )
            // src/hampi/parser/Hampi.g:69:28: ( ( cfgProductionElement )* )
            {
            // src/hampi/parser/Hampi.g:69:28: ( ( cfgProductionElement )* )
            // src/hampi/parser/Hampi.g:69:29: ( cfgProductionElement )*
            {
            // src/hampi/parser/Hampi.g:69:29: ( cfgProductionElement )*
            loop5:
            do {
                int alt5=2;
                int LA5_0 = input.LA(1);

                if ( (LA5_0==ID||LA5_0==LPAREN||LA5_0==LSQUARE||(LA5_0>=CHAR_SEQ && LA5_0<=STR_LIT)) ) {
                    alt5=1;
                }


                switch (alt5) {
            	case 1 :
            	    // src/hampi/parser/Hampi.g:0:0: cfgProductionElement
            	    {
            	    pushFollow(FOLLOW_cfgProductionElement_in_cfgProductionElementSet585);
            	    cfgProductionElement26=cfgProductionElement();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ) stream_cfgProductionElement.add(cfgProductionElement26.getTree());

            	    }
            	    break;

            	default :
            	    break loop5;
                }
            } while (true);


            }



            // AST REWRITE
            // elements: cfgProductionElement
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (Object)adaptor.nil();
            // 69:53: -> ^( CFGPRODELEMSET ( cfgProductionElement )* )
            {
                // src/hampi/parser/Hampi.g:69:56: ^( CFGPRODELEMSET ( cfgProductionElement )* )
                {
                Object root_1 = (Object)adaptor.nil();
                root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CFGPRODELEMSET, "CFGPRODELEMSET"), root_1);

                // src/hampi/parser/Hampi.g:69:73: ( cfgProductionElement )*
                while ( stream_cfgProductionElement.hasNext() ) {
                    adaptor.addChild(root_1, stream_cfgProductionElement.nextTree());

                }
                stream_cfgProductionElement.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgProductionElementSet

    public static class cfgProductionElement_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgProductionElement
    // src/hampi/parser/Hampi.g:71:2: cfgProductionElement : ( cfgTerminal -> cfgTerminal | cfgNonterminal -> cfgNonterminal | LPAREN cfgNonterminal RPAREN QUESTION -> ^( CFGOPTION cfgNonterminal ) | LPAREN cfgNonterminal RPAREN STAR -> ^( CFGSTAR cfgNonterminal ) | LPAREN cfgNonterminal RPAREN PLUS -> ^( CFGPLUS cfgNonterminal ) | LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE -> ^( CFGCHARRANGE CHAR_LIT CHAR_LIT ) | LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE -> ^( CFGCHARSEQRANGE CHAR_SEQ CHAR_SEQ ) );
    public final HampiParser.cfgProductionElement_return cfgProductionElement() throws RecognitionException {
        HampiParser.cfgProductionElement_return retval = new HampiParser.cfgProductionElement_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token LPAREN29=null;
        Token RPAREN31=null;
        Token QUESTION32=null;
        Token LPAREN33=null;
        Token RPAREN35=null;
        Token STAR36=null;
        Token LPAREN37=null;
        Token RPAREN39=null;
        Token PLUS40=null;
        Token LSQUARE41=null;
        Token CHAR_LIT42=null;
        Token MINUS43=null;
        Token CHAR_LIT44=null;
        Token RSQUARE45=null;
        Token LSQUARE46=null;
        Token CHAR_SEQ47=null;
        Token MINUS48=null;
        Token CHAR_SEQ49=null;
        Token RSQUARE50=null;
        HampiParser.cfgTerminal_return cfgTerminal27 = null;

        HampiParser.cfgNonterminal_return cfgNonterminal28 = null;

        HampiParser.cfgNonterminal_return cfgNonterminal30 = null;

        HampiParser.cfgNonterminal_return cfgNonterminal34 = null;

        HampiParser.cfgNonterminal_return cfgNonterminal38 = null;


        Object LPAREN29_tree=null;
        Object RPAREN31_tree=null;
        Object QUESTION32_tree=null;
        Object LPAREN33_tree=null;
        Object RPAREN35_tree=null;
        Object STAR36_tree=null;
        Object LPAREN37_tree=null;
        Object RPAREN39_tree=null;
        Object PLUS40_tree=null;
        Object LSQUARE41_tree=null;
        Object CHAR_LIT42_tree=null;
        Object MINUS43_tree=null;
        Object CHAR_LIT44_tree=null;
        Object RSQUARE45_tree=null;
        Object LSQUARE46_tree=null;
        Object CHAR_SEQ47_tree=null;
        Object MINUS48_tree=null;
        Object CHAR_SEQ49_tree=null;
        Object RSQUARE50_tree=null;
        RewriteRuleTokenStream stream_CHAR_SEQ=new RewriteRuleTokenStream(adaptor,"token CHAR_SEQ");
        RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
        RewriteRuleTokenStream stream_PLUS=new RewriteRuleTokenStream(adaptor,"token PLUS");
        RewriteRuleTokenStream stream_STAR=new RewriteRuleTokenStream(adaptor,"token STAR");
        RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
        RewriteRuleTokenStream stream_CHAR_LIT=new RewriteRuleTokenStream(adaptor,"token CHAR_LIT");
        RewriteRuleTokenStream stream_QUESTION=new RewriteRuleTokenStream(adaptor,"token QUESTION");
        RewriteRuleTokenStream stream_MINUS=new RewriteRuleTokenStream(adaptor,"token MINUS");
        RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
        RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
        RewriteRuleSubtreeStream stream_cfgNonterminal=new RewriteRuleSubtreeStream(adaptor,"rule cfgNonterminal");
        RewriteRuleSubtreeStream stream_cfgTerminal=new RewriteRuleSubtreeStream(adaptor,"rule cfgTerminal");
        try {
            // src/hampi/parser/Hampi.g:71:23: ( cfgTerminal -> cfgTerminal | cfgNonterminal -> cfgNonterminal | LPAREN cfgNonterminal RPAREN QUESTION -> ^( CFGOPTION cfgNonterminal ) | LPAREN cfgNonterminal RPAREN STAR -> ^( CFGSTAR cfgNonterminal ) | LPAREN cfgNonterminal RPAREN PLUS -> ^( CFGPLUS cfgNonterminal ) | LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE -> ^( CFGCHARRANGE CHAR_LIT CHAR_LIT ) | LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE -> ^( CFGCHARSEQRANGE CHAR_SEQ CHAR_SEQ ) )
            int alt6=7;
            alt6 = dfa6.predict(input);
            switch (alt6) {
                case 1 :
                    // src/hampi/parser/Hampi.g:71:25: cfgTerminal
                    {
                    pushFollow(FOLLOW_cfgTerminal_in_cfgProductionElement608);
                    cfgTerminal27=cfgTerminal();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_cfgTerminal.add(cfgTerminal27.getTree());


                    // AST REWRITE
                    // elements: cfgTerminal
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 71:37: -> cfgTerminal
                    {
                        adaptor.addChild(root_0, stream_cfgTerminal.nextTree());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 2 :
                    // src/hampi/parser/Hampi.g:72:25: cfgNonterminal
                    {
                    pushFollow(FOLLOW_cfgNonterminal_in_cfgProductionElement638);
                    cfgNonterminal28=cfgNonterminal();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_cfgNonterminal.add(cfgNonterminal28.getTree());


                    // AST REWRITE
                    // elements: cfgNonterminal
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 72:40: -> cfgNonterminal
                    {
                        adaptor.addChild(root_0, stream_cfgNonterminal.nextTree());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 3 :
                    // src/hampi/parser/Hampi.g:73:25: LPAREN cfgNonterminal RPAREN QUESTION
                    {
                    LPAREN29=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_cfgProductionElement668); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN29);

                    pushFollow(FOLLOW_cfgNonterminal_in_cfgProductionElement670);
                    cfgNonterminal30=cfgNonterminal();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_cfgNonterminal.add(cfgNonterminal30.getTree());
                    RPAREN31=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_cfgProductionElement672); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN31);

                    QUESTION32=(Token)match(input,QUESTION,FOLLOW_QUESTION_in_cfgProductionElement674); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_QUESTION.add(QUESTION32);



                    // AST REWRITE
                    // elements: cfgNonterminal
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 73:63: -> ^( CFGOPTION cfgNonterminal )
                    {
                        // src/hampi/parser/Hampi.g:73:66: ^( CFGOPTION cfgNonterminal )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CFGOPTION, "CFGOPTION"), root_1);

                        adaptor.addChild(root_1, stream_cfgNonterminal.nextTree());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 4 :
                    // src/hampi/parser/Hampi.g:74:25: LPAREN cfgNonterminal RPAREN STAR
                    {
                    LPAREN33=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_cfgProductionElement708); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN33);

                    pushFollow(FOLLOW_cfgNonterminal_in_cfgProductionElement710);
                    cfgNonterminal34=cfgNonterminal();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_cfgNonterminal.add(cfgNonterminal34.getTree());
                    RPAREN35=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_cfgProductionElement712); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN35);

                    STAR36=(Token)match(input,STAR,FOLLOW_STAR_in_cfgProductionElement714); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_STAR.add(STAR36);



                    // AST REWRITE
                    // elements: cfgNonterminal
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 74:63: -> ^( CFGSTAR cfgNonterminal )
                    {
                        // src/hampi/parser/Hampi.g:74:66: ^( CFGSTAR cfgNonterminal )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CFGSTAR, "CFGSTAR"), root_1);

                        adaptor.addChild(root_1, stream_cfgNonterminal.nextTree());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 5 :
                    // src/hampi/parser/Hampi.g:75:25: LPAREN cfgNonterminal RPAREN PLUS
                    {
                    LPAREN37=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_cfgProductionElement756); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN37);

                    pushFollow(FOLLOW_cfgNonterminal_in_cfgProductionElement758);
                    cfgNonterminal38=cfgNonterminal();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_cfgNonterminal.add(cfgNonterminal38.getTree());
                    RPAREN39=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_cfgProductionElement760); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN39);

                    PLUS40=(Token)match(input,PLUS,FOLLOW_PLUS_in_cfgProductionElement762); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_PLUS.add(PLUS40);



                    // AST REWRITE
                    // elements: cfgNonterminal
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 75:60: -> ^( CFGPLUS cfgNonterminal )
                    {
                        // src/hampi/parser/Hampi.g:75:63: ^( CFGPLUS cfgNonterminal )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CFGPLUS, "CFGPLUS"), root_1);

                        adaptor.addChild(root_1, stream_cfgNonterminal.nextTree());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 6 :
                    // src/hampi/parser/Hampi.g:76:25: LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE
                    {
                    LSQUARE41=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_cfgProductionElement801); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE41);

                    CHAR_LIT42=(Token)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_cfgProductionElement803); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_CHAR_LIT.add(CHAR_LIT42);

                    MINUS43=(Token)match(input,MINUS,FOLLOW_MINUS_in_cfgProductionElement805); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_MINUS.add(MINUS43);

                    CHAR_LIT44=(Token)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_cfgProductionElement807); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_CHAR_LIT.add(CHAR_LIT44);

                    RSQUARE45=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_cfgProductionElement809); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE45);



                    // AST REWRITE
                    // elements: CHAR_LIT, CHAR_LIT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 76:65: -> ^( CFGCHARRANGE CHAR_LIT CHAR_LIT )
                    {
                        // src/hampi/parser/Hampi.g:76:68: ^( CFGCHARRANGE CHAR_LIT CHAR_LIT )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CFGCHARRANGE, "CFGCHARRANGE"), root_1);

                        adaptor.addChild(root_1, stream_CHAR_LIT.nextNode());
                        adaptor.addChild(root_1, stream_CHAR_LIT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 7 :
                    // src/hampi/parser/Hampi.g:77:28: LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE
                    {
                    LSQUARE46=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_cfgProductionElement848); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE46);

                    CHAR_SEQ47=(Token)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_cfgProductionElement850); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_CHAR_SEQ.add(CHAR_SEQ47);

                    MINUS48=(Token)match(input,MINUS,FOLLOW_MINUS_in_cfgProductionElement852); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_MINUS.add(MINUS48);

                    CHAR_SEQ49=(Token)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_cfgProductionElement854); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_CHAR_SEQ.add(CHAR_SEQ49);

                    RSQUARE50=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_cfgProductionElement856); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE50);



                    // AST REWRITE
                    // elements: CHAR_SEQ, CHAR_SEQ
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 77:68: -> ^( CFGCHARSEQRANGE CHAR_SEQ CHAR_SEQ )
                    {
                        // src/hampi/parser/Hampi.g:77:71: ^( CFGCHARSEQRANGE CHAR_SEQ CHAR_SEQ )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CFGCHARSEQRANGE, "CFGCHARSEQRANGE"), root_1);

                        adaptor.addChild(root_1, stream_CHAR_SEQ.nextNode());
                        adaptor.addChild(root_1, stream_CHAR_SEQ.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgProductionElement

    public static class cfgTerminal_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgTerminal
    // src/hampi/parser/Hampi.g:80:5: cfgTerminal : ( STR_LIT | CHAR_SEQ );
    public final HampiParser.cfgTerminal_return cfgTerminal() throws RecognitionException {
        HampiParser.cfgTerminal_return retval = new HampiParser.cfgTerminal_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token set51=null;

        Object set51_tree=null;

        try {
            // src/hampi/parser/Hampi.g:80:17: ( STR_LIT | CHAR_SEQ )
            // src/hampi/parser/Hampi.g:
            {
            root_0 = (Object)adaptor.nil();

            set51=(Token)input.LT(1);
            if ( (input.LA(1)>=CHAR_SEQ && input.LA(1)<=STR_LIT) ) {
                input.consume();
                if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set51));
                state.errorRecovery=false;state.failed=false;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }


            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgTerminal

    public static class cfgNonterminal_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgNonterminal
    // src/hampi/parser/Hampi.g:83:5: cfgNonterminal : ID ;
    public final HampiParser.cfgNonterminal_return cfgNonterminal() throws RecognitionException {
        HampiParser.cfgNonterminal_return retval = new HampiParser.cfgNonterminal_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token ID52=null;

        Object ID52_tree=null;

        try {
            // src/hampi/parser/Hampi.g:83:20: ( ID )
            // src/hampi/parser/Hampi.g:83:22: ID
            {
            root_0 = (Object)adaptor.nil();

            ID52=(Token)match(input,ID,FOLLOW_ID_in_cfgNonterminal957); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
            ID52_tree = (Object)adaptor.create(ID52);
            adaptor.addChild(root_0, ID52_tree);
            }

            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgNonterminal

    public static class regStmt_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start regStmt
    // src/hampi/parser/Hampi.g:85:5: regStmt : ( KW_REG ID ASSIGN regDefinition ) -> ^( REG ID regDefinition ) ;
    public final HampiParser.regStmt_return regStmt() throws RecognitionException {
        HampiParser.regStmt_return retval = new HampiParser.regStmt_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token KW_REG53=null;
        Token ID54=null;
        Token ASSIGN55=null;
        HampiParser.regDefinition_return regDefinition56 = null;


        Object KW_REG53_tree=null;
        Object ID54_tree=null;
        Object ASSIGN55_tree=null;
        RewriteRuleTokenStream stream_KW_REG=new RewriteRuleTokenStream(adaptor,"token KW_REG");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
        RewriteRuleSubtreeStream stream_regDefinition=new RewriteRuleSubtreeStream(adaptor,"rule regDefinition");
        try {
            // src/hampi/parser/Hampi.g:85:13: ( ( KW_REG ID ASSIGN regDefinition ) -> ^( REG ID regDefinition ) )
            // src/hampi/parser/Hampi.g:85:15: ( KW_REG ID ASSIGN regDefinition )
            {
            // src/hampi/parser/Hampi.g:85:15: ( KW_REG ID ASSIGN regDefinition )
            // src/hampi/parser/Hampi.g:85:16: KW_REG ID ASSIGN regDefinition
            {
            KW_REG53=(Token)match(input,KW_REG,FOLLOW_KW_REG_in_regStmt974); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_KW_REG.add(KW_REG53);

            ID54=(Token)match(input,ID,FOLLOW_ID_in_regStmt976); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_ID.add(ID54);

            ASSIGN55=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_regStmt978); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_ASSIGN.add(ASSIGN55);

            pushFollow(FOLLOW_regDefinition_in_regStmt980);
            regDefinition56=regDefinition();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) stream_regDefinition.add(regDefinition56.getTree());

            }



            // AST REWRITE
            // elements: ID, regDefinition
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (Object)adaptor.nil();
            // 85:48: -> ^( REG ID regDefinition )
            {
                // src/hampi/parser/Hampi.g:85:51: ^( REG ID regDefinition )
                {
                Object root_1 = (Object)adaptor.nil();
                root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(REG, "REG"), root_1);

                adaptor.addChild(root_1, stream_ID.nextNode());
                adaptor.addChild(root_1, stream_regDefinition.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end regStmt

    public static class regDefinition_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start regDefinition
    // src/hampi/parser/Hampi.g:87:5: regDefinition : ( ID -> ID | STR_LIT -> STR_LIT | CHAR_SEQ -> CHAR_SEQ | ( KW_FIX LPAREN ID COMMA INT RPAREN ) -> ^( FIX ID INT ) | ( KW_STAR LPAREN regDefinition RPAREN ) -> ^( STAR regDefinition ) | ( LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE ) -> ^( RANGE CHAR_LIT CHAR_LIT ) | ( LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE ) -> ^( CHARSEQRANGE CHAR_SEQ CHAR_SEQ ) | ( KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( OR ( regDefinition )+ ) | ( KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( CONCAT ( regDefinition )+ ) );
    public final HampiParser.regDefinition_return regDefinition() throws RecognitionException {
        HampiParser.regDefinition_return retval = new HampiParser.regDefinition_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token ID57=null;
        Token STR_LIT58=null;
        Token CHAR_SEQ59=null;
        Token KW_FIX60=null;
        Token LPAREN61=null;
        Token ID62=null;
        Token COMMA63=null;
        Token INT64=null;
        Token RPAREN65=null;
        Token KW_STAR66=null;
        Token LPAREN67=null;
        Token RPAREN69=null;
        Token LSQUARE70=null;
        Token CHAR_LIT71=null;
        Token MINUS72=null;
        Token CHAR_LIT73=null;
        Token RSQUARE74=null;
        Token LSQUARE75=null;
        Token CHAR_SEQ76=null;
        Token MINUS77=null;
        Token CHAR_SEQ78=null;
        Token RSQUARE79=null;
        Token KW_OR80=null;
        Token LPAREN81=null;
        Token COMMA83=null;
        Token RPAREN85=null;
        Token KW_CONCAT86=null;
        Token LPAREN87=null;
        Token COMMA89=null;
        Token RPAREN91=null;
        HampiParser.regDefinition_return regDefinition68 = null;

        HampiParser.regDefinition_return regDefinition82 = null;

        HampiParser.regDefinition_return regDefinition84 = null;

        HampiParser.regDefinition_return regDefinition88 = null;

        HampiParser.regDefinition_return regDefinition90 = null;


        Object ID57_tree=null;
        Object STR_LIT58_tree=null;
        Object CHAR_SEQ59_tree=null;
        Object KW_FIX60_tree=null;
        Object LPAREN61_tree=null;
        Object ID62_tree=null;
        Object COMMA63_tree=null;
        Object INT64_tree=null;
        Object RPAREN65_tree=null;
        Object KW_STAR66_tree=null;
        Object LPAREN67_tree=null;
        Object RPAREN69_tree=null;
        Object LSQUARE70_tree=null;
        Object CHAR_LIT71_tree=null;
        Object MINUS72_tree=null;
        Object CHAR_LIT73_tree=null;
        Object RSQUARE74_tree=null;
        Object LSQUARE75_tree=null;
        Object CHAR_SEQ76_tree=null;
        Object MINUS77_tree=null;
        Object CHAR_SEQ78_tree=null;
        Object RSQUARE79_tree=null;
        Object KW_OR80_tree=null;
        Object LPAREN81_tree=null;
        Object COMMA83_tree=null;
        Object RPAREN85_tree=null;
        Object KW_CONCAT86_tree=null;
        Object LPAREN87_tree=null;
        Object COMMA89_tree=null;
        Object RPAREN91_tree=null;
        RewriteRuleTokenStream stream_CHAR_SEQ=new RewriteRuleTokenStream(adaptor,"token CHAR_SEQ");
        RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
        RewriteRuleTokenStream stream_KW_FIX=new RewriteRuleTokenStream(adaptor,"token KW_FIX");
        RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
        RewriteRuleTokenStream stream_KW_CONCAT=new RewriteRuleTokenStream(adaptor,"token KW_CONCAT");
        RewriteRuleTokenStream stream_KW_OR=new RewriteRuleTokenStream(adaptor,"token KW_OR");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_STR_LIT=new RewriteRuleTokenStream(adaptor,"token STR_LIT");
        RewriteRuleTokenStream stream_INT=new RewriteRuleTokenStream(adaptor,"token INT");
        RewriteRuleTokenStream stream_KW_STAR=new RewriteRuleTokenStream(adaptor,"token KW_STAR");
        RewriteRuleTokenStream stream_CHAR_LIT=new RewriteRuleTokenStream(adaptor,"token CHAR_LIT");
        RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
        RewriteRuleTokenStream stream_MINUS=new RewriteRuleTokenStream(adaptor,"token MINUS");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
        RewriteRuleSubtreeStream stream_regDefinition=new RewriteRuleSubtreeStream(adaptor,"rule regDefinition");
        try {
            // src/hampi/parser/Hampi.g:87:19: ( ID -> ID | STR_LIT -> STR_LIT | CHAR_SEQ -> CHAR_SEQ | ( KW_FIX LPAREN ID COMMA INT RPAREN ) -> ^( FIX ID INT ) | ( KW_STAR LPAREN regDefinition RPAREN ) -> ^( STAR regDefinition ) | ( LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE ) -> ^( RANGE CHAR_LIT CHAR_LIT ) | ( LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE ) -> ^( CHARSEQRANGE CHAR_SEQ CHAR_SEQ ) | ( KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( OR ( regDefinition )+ ) | ( KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( CONCAT ( regDefinition )+ ) )
            int alt9=9;
            alt9 = dfa9.predict(input);
            switch (alt9) {
                case 1 :
                    // src/hampi/parser/Hampi.g:87:21: ID
                    {
                    ID57=(Token)match(input,ID,FOLLOW_ID_in_regDefinition1003); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID57);



                    // AST REWRITE
                    // elements: ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 87:24: -> ID
                    {
                        adaptor.addChild(root_0, stream_ID.nextNode());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 2 :
                    // src/hampi/parser/Hampi.g:88:21: STR_LIT
                    {
                    STR_LIT58=(Token)match(input,STR_LIT,FOLLOW_STR_LIT_in_regDefinition1029); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_STR_LIT.add(STR_LIT58);



                    // AST REWRITE
                    // elements: STR_LIT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 88:29: -> STR_LIT
                    {
                        adaptor.addChild(root_0, stream_STR_LIT.nextNode());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 3 :
                    // src/hampi/parser/Hampi.g:89:21: CHAR_SEQ
                    {
                    CHAR_SEQ59=(Token)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regDefinition1055); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_CHAR_SEQ.add(CHAR_SEQ59);



                    // AST REWRITE
                    // elements: CHAR_SEQ
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 89:30: -> CHAR_SEQ
                    {
                        adaptor.addChild(root_0, stream_CHAR_SEQ.nextNode());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 4 :
                    // src/hampi/parser/Hampi.g:90:21: ( KW_FIX LPAREN ID COMMA INT RPAREN )
                    {
                    // src/hampi/parser/Hampi.g:90:21: ( KW_FIX LPAREN ID COMMA INT RPAREN )
                    // src/hampi/parser/Hampi.g:90:22: KW_FIX LPAREN ID COMMA INT RPAREN
                    {
                    KW_FIX60=(Token)match(input,KW_FIX,FOLLOW_KW_FIX_in_regDefinition1083); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_FIX.add(KW_FIX60);

                    LPAREN61=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_regDefinition1085); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN61);

                    ID62=(Token)match(input,ID,FOLLOW_ID_in_regDefinition1087); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID62);

                    COMMA63=(Token)match(input,COMMA,FOLLOW_COMMA_in_regDefinition1089); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_COMMA.add(COMMA63);

                    INT64=(Token)match(input,INT,FOLLOW_INT_in_regDefinition1091); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_INT.add(INT64);

                    RPAREN65=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_regDefinition1093); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN65);


                    }



                    // AST REWRITE
                    // elements: ID, INT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 90:57: -> ^( FIX ID INT )
                    {
                        // src/hampi/parser/Hampi.g:90:60: ^( FIX ID INT )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FIX, "FIX"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_INT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 5 :
                    // src/hampi/parser/Hampi.g:91:21: ( KW_STAR LPAREN regDefinition RPAREN )
                    {
                    // src/hampi/parser/Hampi.g:91:21: ( KW_STAR LPAREN regDefinition RPAREN )
                    // src/hampi/parser/Hampi.g:91:22: KW_STAR LPAREN regDefinition RPAREN
                    {
                    KW_STAR66=(Token)match(input,KW_STAR,FOLLOW_KW_STAR_in_regDefinition1127); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_STAR.add(KW_STAR66);

                    LPAREN67=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_regDefinition1129); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN67);

                    pushFollow(FOLLOW_regDefinition_in_regDefinition1131);
                    regDefinition68=regDefinition();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_regDefinition.add(regDefinition68.getTree());
                    RPAREN69=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_regDefinition1133); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN69);


                    }



                    // AST REWRITE
                    // elements: regDefinition
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 91:59: -> ^( STAR regDefinition )
                    {
                        // src/hampi/parser/Hampi.g:91:62: ^( STAR regDefinition )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STAR, "STAR"), root_1);

                        adaptor.addChild(root_1, stream_regDefinition.nextTree());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 6 :
                    // src/hampi/parser/Hampi.g:92:21: ( LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE )
                    {
                    // src/hampi/parser/Hampi.g:92:21: ( LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE )
                    // src/hampi/parser/Hampi.g:92:22: LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE
                    {
                    LSQUARE70=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_regDefinition1165); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE70);

                    CHAR_LIT71=(Token)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_regDefinition1167); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_CHAR_LIT.add(CHAR_LIT71);

                    MINUS72=(Token)match(input,MINUS,FOLLOW_MINUS_in_regDefinition1169); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_MINUS.add(MINUS72);

                    CHAR_LIT73=(Token)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_regDefinition1171); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_CHAR_LIT.add(CHAR_LIT73);

                    RSQUARE74=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_regDefinition1173); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE74);


                    }



                    // AST REWRITE
                    // elements: CHAR_LIT, CHAR_LIT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 92:63: -> ^( RANGE CHAR_LIT CHAR_LIT )
                    {
                        // src/hampi/parser/Hampi.g:92:66: ^( RANGE CHAR_LIT CHAR_LIT )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(RANGE, "RANGE"), root_1);

                        adaptor.addChild(root_1, stream_CHAR_LIT.nextNode());
                        adaptor.addChild(root_1, stream_CHAR_LIT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 7 :
                    // src/hampi/parser/Hampi.g:93:21: ( LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE )
                    {
                    // src/hampi/parser/Hampi.g:93:21: ( LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE )
                    // src/hampi/parser/Hampi.g:93:22: LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE
                    {
                    LSQUARE75=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_regDefinition1207); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE75);

                    CHAR_SEQ76=(Token)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regDefinition1209); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_CHAR_SEQ.add(CHAR_SEQ76);

                    MINUS77=(Token)match(input,MINUS,FOLLOW_MINUS_in_regDefinition1211); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_MINUS.add(MINUS77);

                    CHAR_SEQ78=(Token)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regDefinition1213); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_CHAR_SEQ.add(CHAR_SEQ78);

                    RSQUARE79=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_regDefinition1215); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE79);


                    }



                    // AST REWRITE
                    // elements: CHAR_SEQ, CHAR_SEQ
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 93:63: -> ^( CHARSEQRANGE CHAR_SEQ CHAR_SEQ )
                    {
                        // src/hampi/parser/Hampi.g:93:66: ^( CHARSEQRANGE CHAR_SEQ CHAR_SEQ )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CHARSEQRANGE, "CHARSEQRANGE"), root_1);

                        adaptor.addChild(root_1, stream_CHAR_SEQ.nextNode());
                        adaptor.addChild(root_1, stream_CHAR_SEQ.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 8 :
                    // src/hampi/parser/Hampi.g:94:21: ( KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN )
                    {
                    // src/hampi/parser/Hampi.g:94:21: ( KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN )
                    // src/hampi/parser/Hampi.g:94:22: KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN
                    {
                    KW_OR80=(Token)match(input,KW_OR,FOLLOW_KW_OR_in_regDefinition1250); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_OR.add(KW_OR80);

                    LPAREN81=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_regDefinition1252); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN81);

                    pushFollow(FOLLOW_regDefinition_in_regDefinition1254);
                    regDefinition82=regDefinition();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_regDefinition.add(regDefinition82.getTree());
                    // src/hampi/parser/Hampi.g:94:49: ( COMMA regDefinition )*
                    loop7:
                    do {
                        int alt7=2;
                        int LA7_0 = input.LA(1);

                        if ( (LA7_0==COMMA) ) {
                            alt7=1;
                        }


                        switch (alt7) {
                    	case 1 :
                    	    // src/hampi/parser/Hampi.g:94:50: COMMA regDefinition
                    	    {
                    	    COMMA83=(Token)match(input,COMMA,FOLLOW_COMMA_in_regDefinition1257); if (state.failed) return retval; 
                    	    if ( state.backtracking==0 ) stream_COMMA.add(COMMA83);

                    	    pushFollow(FOLLOW_regDefinition_in_regDefinition1259);
                    	    regDefinition84=regDefinition();

                    	    state._fsp--;
                    	    if (state.failed) return retval;
                    	    if ( state.backtracking==0 ) stream_regDefinition.add(regDefinition84.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop7;
                        }
                    } while (true);

                    RPAREN85=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_regDefinition1263); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN85);


                    }



                    // AST REWRITE
                    // elements: regDefinition
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 94:80: -> ^( OR ( regDefinition )+ )
                    {
                        // src/hampi/parser/Hampi.g:94:83: ^( OR ( regDefinition )+ )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OR, "OR"), root_1);

                        if ( !(stream_regDefinition.hasNext()) ) {
                            throw new RewriteEarlyExitException();
                        }
                        while ( stream_regDefinition.hasNext() ) {
                            adaptor.addChild(root_1, stream_regDefinition.nextTree());

                        }
                        stream_regDefinition.reset();

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 9 :
                    // src/hampi/parser/Hampi.g:95:21: ( KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN )
                    {
                    // src/hampi/parser/Hampi.g:95:21: ( KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN )
                    // src/hampi/parser/Hampi.g:95:22: KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN
                    {
                    KW_CONCAT86=(Token)match(input,KW_CONCAT,FOLLOW_KW_CONCAT_in_regDefinition1296); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_CONCAT.add(KW_CONCAT86);

                    LPAREN87=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_regDefinition1298); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN87);

                    pushFollow(FOLLOW_regDefinition_in_regDefinition1300);
                    regDefinition88=regDefinition();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_regDefinition.add(regDefinition88.getTree());
                    // src/hampi/parser/Hampi.g:95:53: ( COMMA regDefinition )*
                    loop8:
                    do {
                        int alt8=2;
                        int LA8_0 = input.LA(1);

                        if ( (LA8_0==COMMA) ) {
                            alt8=1;
                        }


                        switch (alt8) {
                    	case 1 :
                    	    // src/hampi/parser/Hampi.g:95:54: COMMA regDefinition
                    	    {
                    	    COMMA89=(Token)match(input,COMMA,FOLLOW_COMMA_in_regDefinition1303); if (state.failed) return retval; 
                    	    if ( state.backtracking==0 ) stream_COMMA.add(COMMA89);

                    	    pushFollow(FOLLOW_regDefinition_in_regDefinition1305);
                    	    regDefinition90=regDefinition();

                    	    state._fsp--;
                    	    if (state.failed) return retval;
                    	    if ( state.backtracking==0 ) stream_regDefinition.add(regDefinition90.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop8;
                        }
                    } while (true);

                    RPAREN91=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_regDefinition1309); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN91);


                    }



                    // AST REWRITE
                    // elements: regDefinition
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 95:84: -> ^( CONCAT ( regDefinition )+ )
                    {
                        // src/hampi/parser/Hampi.g:95:87: ^( CONCAT ( regDefinition )+ )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CONCAT, "CONCAT"), root_1);

                        if ( !(stream_regDefinition.hasNext()) ) {
                            throw new RewriteEarlyExitException();
                        }
                        while ( stream_regDefinition.hasNext() ) {
                            adaptor.addChild(root_1, stream_regDefinition.nextTree());

                        }
                        stream_regDefinition.reset();

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end regDefinition

    public static class valDeclStmt_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start valDeclStmt
    // src/hampi/parser/Hampi.g:98:2: valDeclStmt : ( KW_VAL ID ASSIGN expr ) -> ^( VAL ID expr ) ;
    public final HampiParser.valDeclStmt_return valDeclStmt() throws RecognitionException {
        HampiParser.valDeclStmt_return retval = new HampiParser.valDeclStmt_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token KW_VAL92=null;
        Token ID93=null;
        Token ASSIGN94=null;
        HampiParser.expr_return expr95 = null;


        Object KW_VAL92_tree=null;
        Object ID93_tree=null;
        Object ASSIGN94_tree=null;
        RewriteRuleTokenStream stream_KW_VAL=new RewriteRuleTokenStream(adaptor,"token KW_VAL");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
        RewriteRuleSubtreeStream stream_expr=new RewriteRuleSubtreeStream(adaptor,"rule expr");
        try {
            // src/hampi/parser/Hampi.g:98:14: ( ( KW_VAL ID ASSIGN expr ) -> ^( VAL ID expr ) )
            // src/hampi/parser/Hampi.g:98:16: ( KW_VAL ID ASSIGN expr )
            {
            // src/hampi/parser/Hampi.g:98:16: ( KW_VAL ID ASSIGN expr )
            // src/hampi/parser/Hampi.g:98:17: KW_VAL ID ASSIGN expr
            {
            KW_VAL92=(Token)match(input,KW_VAL,FOLLOW_KW_VAL_in_valDeclStmt1350); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_KW_VAL.add(KW_VAL92);

            ID93=(Token)match(input,ID,FOLLOW_ID_in_valDeclStmt1352); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_ID.add(ID93);

            ASSIGN94=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_valDeclStmt1354); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_ASSIGN.add(ASSIGN94);

            pushFollow(FOLLOW_expr_in_valDeclStmt1356);
            expr95=expr();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) stream_expr.add(expr95.getTree());

            }



            // AST REWRITE
            // elements: ID, expr
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (Object)adaptor.nil();
            // 98:40: -> ^( VAL ID expr )
            {
                // src/hampi/parser/Hampi.g:98:43: ^( VAL ID expr )
                {
                Object root_1 = (Object)adaptor.nil();
                root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(VAL, "VAL"), root_1);

                adaptor.addChild(root_1, stream_ID.nextNode());
                adaptor.addChild(root_1, stream_expr.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end valDeclStmt

    public static class expr_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start expr
    // src/hampi/parser/Hampi.g:100:2: expr : ( STR_LIT -> STR_LIT | ID -> ID | ( KW_CONCAT LPAREN expr ( COMMA expr )* RPAREN ) -> ^( CONCAT ( expr )+ ) | ID LSQUARE INT COLON INT RSQUARE -> ^( SUBSEQUENCE ID INT INT ) );
    public final HampiParser.expr_return expr() throws RecognitionException {
        HampiParser.expr_return retval = new HampiParser.expr_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token STR_LIT96=null;
        Token ID97=null;
        Token KW_CONCAT98=null;
        Token LPAREN99=null;
        Token COMMA101=null;
        Token RPAREN103=null;
        Token ID104=null;
        Token LSQUARE105=null;
        Token INT106=null;
        Token COLON107=null;
        Token INT108=null;
        Token RSQUARE109=null;
        HampiParser.expr_return expr100 = null;

        HampiParser.expr_return expr102 = null;


        Object STR_LIT96_tree=null;
        Object ID97_tree=null;
        Object KW_CONCAT98_tree=null;
        Object LPAREN99_tree=null;
        Object COMMA101_tree=null;
        Object RPAREN103_tree=null;
        Object ID104_tree=null;
        Object LSQUARE105_tree=null;
        Object INT106_tree=null;
        Object COLON107_tree=null;
        Object INT108_tree=null;
        Object RSQUARE109_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
        RewriteRuleTokenStream stream_INT=new RewriteRuleTokenStream(adaptor,"token INT");
        RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
        RewriteRuleTokenStream stream_KW_CONCAT=new RewriteRuleTokenStream(adaptor,"token KW_CONCAT");
        RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
        RewriteRuleTokenStream stream_STR_LIT=new RewriteRuleTokenStream(adaptor,"token STR_LIT");
        RewriteRuleSubtreeStream stream_expr=new RewriteRuleSubtreeStream(adaptor,"rule expr");
        try {
            // src/hampi/parser/Hampi.g:100:7: ( STR_LIT -> STR_LIT | ID -> ID | ( KW_CONCAT LPAREN expr ( COMMA expr )* RPAREN ) -> ^( CONCAT ( expr )+ ) | ID LSQUARE INT COLON INT RSQUARE -> ^( SUBSEQUENCE ID INT INT ) )
            int alt11=4;
            switch ( input.LA(1) ) {
            case STR_LIT:
                {
                alt11=1;
                }
                break;
            case ID:
                {
                int LA11_2 = input.LA(2);

                if ( (LA11_2==LSQUARE) ) {
                    alt11=4;
                }
                else if ( (LA11_2==EOF||LA11_2==SEMI||LA11_2==RPAREN||LA11_2==COMMA) ) {
                    alt11=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 11, 2, input);

                    throw nvae;
                }
                }
                break;
            case KW_CONCAT:
                {
                alt11=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 11, 0, input);

                throw nvae;
            }

            switch (alt11) {
                case 1 :
                    // src/hampi/parser/Hampi.g:100:9: STR_LIT
                    {
                    STR_LIT96=(Token)match(input,STR_LIT,FOLLOW_STR_LIT_in_expr1377); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_STR_LIT.add(STR_LIT96);



                    // AST REWRITE
                    // elements: STR_LIT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 100:17: -> STR_LIT
                    {
                        adaptor.addChild(root_0, stream_STR_LIT.nextNode());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 2 :
                    // src/hampi/parser/Hampi.g:101:9: ID
                    {
                    ID97=(Token)match(input,ID,FOLLOW_ID_in_expr1391); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID97);



                    // AST REWRITE
                    // elements: ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 101:17: -> ID
                    {
                        adaptor.addChild(root_0, stream_ID.nextNode());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 3 :
                    // src/hampi/parser/Hampi.g:102:9: ( KW_CONCAT LPAREN expr ( COMMA expr )* RPAREN )
                    {
                    // src/hampi/parser/Hampi.g:102:9: ( KW_CONCAT LPAREN expr ( COMMA expr )* RPAREN )
                    // src/hampi/parser/Hampi.g:102:10: KW_CONCAT LPAREN expr ( COMMA expr )* RPAREN
                    {
                    KW_CONCAT98=(Token)match(input,KW_CONCAT,FOLLOW_KW_CONCAT_in_expr1411); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_CONCAT.add(KW_CONCAT98);

                    LPAREN99=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_expr1413); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN99);

                    pushFollow(FOLLOW_expr_in_expr1415);
                    expr100=expr();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ) stream_expr.add(expr100.getTree());
                    // src/hampi/parser/Hampi.g:102:32: ( COMMA expr )*
                    loop10:
                    do {
                        int alt10=2;
                        int LA10_0 = input.LA(1);

                        if ( (LA10_0==COMMA) ) {
                            alt10=1;
                        }


                        switch (alt10) {
                    	case 1 :
                    	    // src/hampi/parser/Hampi.g:102:33: COMMA expr
                    	    {
                    	    COMMA101=(Token)match(input,COMMA,FOLLOW_COMMA_in_expr1418); if (state.failed) return retval; 
                    	    if ( state.backtracking==0 ) stream_COMMA.add(COMMA101);

                    	    pushFollow(FOLLOW_expr_in_expr1420);
                    	    expr102=expr();

                    	    state._fsp--;
                    	    if (state.failed) return retval;
                    	    if ( state.backtracking==0 ) stream_expr.add(expr102.getTree());

                    	    }
                    	    break;

                    	default :
                    	    break loop10;
                        }
                    } while (true);

                    RPAREN103=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_expr1424); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN103);


                    }



                    // AST REWRITE
                    // elements: expr
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 102:54: -> ^( CONCAT ( expr )+ )
                    {
                        // src/hampi/parser/Hampi.g:102:57: ^( CONCAT ( expr )+ )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CONCAT, "CONCAT"), root_1);

                        if ( !(stream_expr.hasNext()) ) {
                            throw new RewriteEarlyExitException();
                        }
                        while ( stream_expr.hasNext() ) {
                            adaptor.addChild(root_1, stream_expr.nextTree());

                        }
                        stream_expr.reset();

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 4 :
                    // src/hampi/parser/Hampi.g:103:9: ID LSQUARE INT COLON INT RSQUARE
                    {
                    ID104=(Token)match(input,ID,FOLLOW_ID_in_expr1444); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID104);

                    LSQUARE105=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_expr1446); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE105);

                    INT106=(Token)match(input,INT,FOLLOW_INT_in_expr1448); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_INT.add(INT106);

                    COLON107=(Token)match(input,COLON,FOLLOW_COLON_in_expr1450); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_COLON.add(COLON107);

                    INT108=(Token)match(input,INT,FOLLOW_INT_in_expr1452); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_INT.add(INT108);

                    RSQUARE109=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_expr1454); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE109);



                    // AST REWRITE
                    // elements: INT, INT, ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 103:42: -> ^( SUBSEQUENCE ID INT INT )
                    {
                        // src/hampi/parser/Hampi.g:103:45: ^( SUBSEQUENCE ID INT INT )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(SUBSEQUENCE, "SUBSEQUENCE"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_INT.nextNode());
                        adaptor.addChild(root_1, stream_INT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end expr

    public static class assertStmt_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start assertStmt
    // src/hampi/parser/Hampi.g:105:2: assertStmt : ( KW_ASSERT boolExpr ) -> ^( ASSERT boolExpr ) ;
    public final HampiParser.assertStmt_return assertStmt() throws RecognitionException {
        HampiParser.assertStmt_return retval = new HampiParser.assertStmt_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token KW_ASSERT110=null;
        HampiParser.boolExpr_return boolExpr111 = null;


        Object KW_ASSERT110_tree=null;
        RewriteRuleTokenStream stream_KW_ASSERT=new RewriteRuleTokenStream(adaptor,"token KW_ASSERT");
        RewriteRuleSubtreeStream stream_boolExpr=new RewriteRuleSubtreeStream(adaptor,"rule boolExpr");
        try {
            // src/hampi/parser/Hampi.g:105:13: ( ( KW_ASSERT boolExpr ) -> ^( ASSERT boolExpr ) )
            // src/hampi/parser/Hampi.g:105:15: ( KW_ASSERT boolExpr )
            {
            // src/hampi/parser/Hampi.g:105:15: ( KW_ASSERT boolExpr )
            // src/hampi/parser/Hampi.g:105:16: KW_ASSERT boolExpr
            {
            KW_ASSERT110=(Token)match(input,KW_ASSERT,FOLLOW_KW_ASSERT_in_assertStmt1477); if (state.failed) return retval; 
            if ( state.backtracking==0 ) stream_KW_ASSERT.add(KW_ASSERT110);

            pushFollow(FOLLOW_boolExpr_in_assertStmt1479);
            boolExpr111=boolExpr();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ) stream_boolExpr.add(boolExpr111.getTree());

            }



            // AST REWRITE
            // elements: boolExpr
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = (Object)adaptor.nil();
            // 105:36: -> ^( ASSERT boolExpr )
            {
                // src/hampi/parser/Hampi.g:105:39: ^( ASSERT boolExpr )
                {
                Object root_1 = (Object)adaptor.nil();
                root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ASSERT, "ASSERT"), root_1);

                adaptor.addChild(root_1, stream_boolExpr.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end assertStmt

    public static class boolExpr_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };

    // $ANTLR start boolExpr
    // src/hampi/parser/Hampi.g:107:5: boolExpr : ( ( ID KW_IN ID ) -> ^( IN ID ID ) | ( ID KW_CONTAINS STR_LIT ) -> ^( CONTAINS ID STR_LIT ) | ( ID KW_NOT KW_IN ID ) -> ^( NOTIN ID ID ) | ( ID KW_NOT KW_CONTAINS STR_LIT ) -> ^( NOTCONTAINS ID STR_LIT ) | ( ID KW_EQUALS ID ) -> ^( TEQUALS ID ID ) | ( ID KW_NOT KW_EQUALS ID ) -> ^( TNOTEQUALS ID ID ) );
    public final HampiParser.boolExpr_return boolExpr() throws RecognitionException {
        HampiParser.boolExpr_return retval = new HampiParser.boolExpr_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token ID112=null;
        Token KW_IN113=null;
        Token ID114=null;
        Token ID115=null;
        Token KW_CONTAINS116=null;
        Token STR_LIT117=null;
        Token ID118=null;
        Token KW_NOT119=null;
        Token KW_IN120=null;
        Token ID121=null;
        Token ID122=null;
        Token KW_NOT123=null;
        Token KW_CONTAINS124=null;
        Token STR_LIT125=null;
        Token ID126=null;
        Token KW_EQUALS127=null;
        Token ID128=null;
        Token ID129=null;
        Token KW_NOT130=null;
        Token KW_EQUALS131=null;
        Token ID132=null;

        Object ID112_tree=null;
        Object KW_IN113_tree=null;
        Object ID114_tree=null;
        Object ID115_tree=null;
        Object KW_CONTAINS116_tree=null;
        Object STR_LIT117_tree=null;
        Object ID118_tree=null;
        Object KW_NOT119_tree=null;
        Object KW_IN120_tree=null;
        Object ID121_tree=null;
        Object ID122_tree=null;
        Object KW_NOT123_tree=null;
        Object KW_CONTAINS124_tree=null;
        Object STR_LIT125_tree=null;
        Object ID126_tree=null;
        Object KW_EQUALS127_tree=null;
        Object ID128_tree=null;
        Object ID129_tree=null;
        Object KW_NOT130_tree=null;
        Object KW_EQUALS131_tree=null;
        Object ID132_tree=null;
        RewriteRuleTokenStream stream_KW_IN=new RewriteRuleTokenStream(adaptor,"token KW_IN");
        RewriteRuleTokenStream stream_KW_EQUALS=new RewriteRuleTokenStream(adaptor,"token KW_EQUALS");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_KW_CONTAINS=new RewriteRuleTokenStream(adaptor,"token KW_CONTAINS");
        RewriteRuleTokenStream stream_KW_NOT=new RewriteRuleTokenStream(adaptor,"token KW_NOT");
        RewriteRuleTokenStream stream_STR_LIT=new RewriteRuleTokenStream(adaptor,"token STR_LIT");

        try {
            // src/hampi/parser/Hampi.g:107:14: ( ( ID KW_IN ID ) -> ^( IN ID ID ) | ( ID KW_CONTAINS STR_LIT ) -> ^( CONTAINS ID STR_LIT ) | ( ID KW_NOT KW_IN ID ) -> ^( NOTIN ID ID ) | ( ID KW_NOT KW_CONTAINS STR_LIT ) -> ^( NOTCONTAINS ID STR_LIT ) | ( ID KW_EQUALS ID ) -> ^( TEQUALS ID ID ) | ( ID KW_NOT KW_EQUALS ID ) -> ^( TNOTEQUALS ID ID ) )
            int alt12=6;
            int LA12_0 = input.LA(1);

            if ( (LA12_0==ID) ) {
                switch ( input.LA(2) ) {
                case KW_IN:
                    {
                    alt12=1;
                    }
                    break;
                case KW_CONTAINS:
                    {
                    alt12=2;
                    }
                    break;
                case KW_NOT:
                    {
                    switch ( input.LA(3) ) {
                    case KW_IN:
                        {
                        alt12=3;
                        }
                        break;
                    case KW_CONTAINS:
                        {
                        alt12=4;
                        }
                        break;
                    case KW_EQUALS:
                        {
                        alt12=6;
                        }
                        break;
                    default:
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 12, 4, input);

                        throw nvae;
                    }

                    }
                    break;
                case KW_EQUALS:
                    {
                    alt12=5;
                    }
                    break;
                default:
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 12, 1, input);

                    throw nvae;
                }

            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 12, 0, input);

                throw nvae;
            }
            switch (alt12) {
                case 1 :
                    // src/hampi/parser/Hampi.g:108:16: ( ID KW_IN ID )
                    {
                    // src/hampi/parser/Hampi.g:108:16: ( ID KW_IN ID )
                    // src/hampi/parser/Hampi.g:108:17: ID KW_IN ID
                    {
                    ID112=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1516); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID112);

                    KW_IN113=(Token)match(input,KW_IN,FOLLOW_KW_IN_in_boolExpr1518); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_IN.add(KW_IN113);

                    ID114=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1520); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID114);


                    }



                    // AST REWRITE
                    // elements: ID, ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 108:30: -> ^( IN ID ID )
                    {
                        // src/hampi/parser/Hampi.g:108:33: ^( IN ID ID )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(IN, "IN"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_ID.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 2 :
                    // src/hampi/parser/Hampi.g:109:16: ( ID KW_CONTAINS STR_LIT )
                    {
                    // src/hampi/parser/Hampi.g:109:16: ( ID KW_CONTAINS STR_LIT )
                    // src/hampi/parser/Hampi.g:109:17: ID KW_CONTAINS STR_LIT
                    {
                    ID115=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1549); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID115);

                    KW_CONTAINS116=(Token)match(input,KW_CONTAINS,FOLLOW_KW_CONTAINS_in_boolExpr1551); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_CONTAINS.add(KW_CONTAINS116);

                    STR_LIT117=(Token)match(input,STR_LIT,FOLLOW_STR_LIT_in_boolExpr1553); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_STR_LIT.add(STR_LIT117);


                    }



                    // AST REWRITE
                    // elements: STR_LIT, ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 109:41: -> ^( CONTAINS ID STR_LIT )
                    {
                        // src/hampi/parser/Hampi.g:109:44: ^( CONTAINS ID STR_LIT )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CONTAINS, "CONTAINS"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_STR_LIT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 3 :
                    // src/hampi/parser/Hampi.g:110:16: ( ID KW_NOT KW_IN ID )
                    {
                    // src/hampi/parser/Hampi.g:110:16: ( ID KW_NOT KW_IN ID )
                    // src/hampi/parser/Hampi.g:110:17: ID KW_NOT KW_IN ID
                    {
                    ID118=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1582); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID118);

                    KW_NOT119=(Token)match(input,KW_NOT,FOLLOW_KW_NOT_in_boolExpr1584); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_NOT.add(KW_NOT119);

                    KW_IN120=(Token)match(input,KW_IN,FOLLOW_KW_IN_in_boolExpr1586); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_IN.add(KW_IN120);

                    ID121=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1588); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID121);


                    }



                    // AST REWRITE
                    // elements: ID, ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 110:48: -> ^( NOTIN ID ID )
                    {
                        // src/hampi/parser/Hampi.g:110:51: ^( NOTIN ID ID )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(NOTIN, "NOTIN"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_ID.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 4 :
                    // src/hampi/parser/Hampi.g:111:16: ( ID KW_NOT KW_CONTAINS STR_LIT )
                    {
                    // src/hampi/parser/Hampi.g:111:16: ( ID KW_NOT KW_CONTAINS STR_LIT )
                    // src/hampi/parser/Hampi.g:111:17: ID KW_NOT KW_CONTAINS STR_LIT
                    {
                    ID122=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1628); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID122);

                    KW_NOT123=(Token)match(input,KW_NOT,FOLLOW_KW_NOT_in_boolExpr1630); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_NOT.add(KW_NOT123);

                    KW_CONTAINS124=(Token)match(input,KW_CONTAINS,FOLLOW_KW_CONTAINS_in_boolExpr1632); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_CONTAINS.add(KW_CONTAINS124);

                    STR_LIT125=(Token)match(input,STR_LIT,FOLLOW_STR_LIT_in_boolExpr1634); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_STR_LIT.add(STR_LIT125);


                    }



                    // AST REWRITE
                    // elements: ID, STR_LIT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 111:48: -> ^( NOTCONTAINS ID STR_LIT )
                    {
                        // src/hampi/parser/Hampi.g:111:51: ^( NOTCONTAINS ID STR_LIT )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(NOTCONTAINS, "NOTCONTAINS"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_STR_LIT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 5 :
                    // src/hampi/parser/Hampi.g:112:16: ( ID KW_EQUALS ID )
                    {
                    // src/hampi/parser/Hampi.g:112:16: ( ID KW_EQUALS ID )
                    // src/hampi/parser/Hampi.g:112:17: ID KW_EQUALS ID
                    {
                    ID126=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1663); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID126);

                    KW_EQUALS127=(Token)match(input,KW_EQUALS,FOLLOW_KW_EQUALS_in_boolExpr1665); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_EQUALS.add(KW_EQUALS127);

                    ID128=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1667); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID128);


                    }



                    // AST REWRITE
                    // elements: ID, ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 112:34: -> ^( TEQUALS ID ID )
                    {
                        // src/hampi/parser/Hampi.g:112:37: ^( TEQUALS ID ID )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TEQUALS, "TEQUALS"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_ID.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 6 :
                    // src/hampi/parser/Hampi.g:113:16: ( ID KW_NOT KW_EQUALS ID )
                    {
                    // src/hampi/parser/Hampi.g:113:16: ( ID KW_NOT KW_EQUALS ID )
                    // src/hampi/parser/Hampi.g:113:17: ID KW_NOT KW_EQUALS ID
                    {
                    ID129=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1696); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID129);

                    KW_NOT130=(Token)match(input,KW_NOT,FOLLOW_KW_NOT_in_boolExpr1698); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_NOT.add(KW_NOT130);

                    KW_EQUALS131=(Token)match(input,KW_EQUALS,FOLLOW_KW_EQUALS_in_boolExpr1700); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_KW_EQUALS.add(KW_EQUALS131);

                    ID132=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1702); if (state.failed) return retval; 
                    if ( state.backtracking==0 ) stream_ID.add(ID132);


                    }



                    // AST REWRITE
                    // elements: ID, ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = (Object)adaptor.nil();
                    // 113:41: -> ^( TNOTEQUALS ID ID )
                    {
                        // src/hampi/parser/Hampi.g:113:44: ^( TNOTEQUALS ID ID )
                        {
                        Object root_1 = (Object)adaptor.nil();
                        root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TNOTEQUALS, "TNOTEQUALS"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_ID.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end boolExpr

    // Delegated rules


    protected DFA6 dfa6 = new DFA6(this);
    protected DFA9 dfa9 = new DFA9(this);
    static final String DFA6_eotS =
        "\14\uffff";
    static final String DFA6_eofS =
        "\14\uffff";
    static final String DFA6_minS =
        "\1\42\2\uffff\1\42\1\55\1\50\2\uffff\1\51\3\uffff";
    static final String DFA6_maxS =
        "\1\61\2\uffff\1\42\1\60\1\50\2\uffff\1\53\3\uffff";
    static final String DFA6_acceptS =
        "\1\uffff\1\1\1\2\3\uffff\1\6\1\7\1\uffff\1\3\1\5\1\4";
    static final String DFA6_specialS =
        "\14\uffff}>";
    static final String[] DFA6_transitionS = {
            "\1\2\4\uffff\1\3\4\uffff\1\4\3\uffff\2\1",
            "",
            "",
            "\1\5",
            "\1\6\2\uffff\1\7",
            "\1\10",
            "",
            "",
            "\1\11\1\13\1\12",
            "",
            "",
            ""
    };

    static final short[] DFA6_eot = DFA.unpackEncodedString(DFA6_eotS);
    static final short[] DFA6_eof = DFA.unpackEncodedString(DFA6_eofS);
    static final char[] DFA6_min = DFA.unpackEncodedStringToUnsignedChars(DFA6_minS);
    static final char[] DFA6_max = DFA.unpackEncodedStringToUnsignedChars(DFA6_maxS);
    static final short[] DFA6_accept = DFA.unpackEncodedString(DFA6_acceptS);
    static final short[] DFA6_special = DFA.unpackEncodedString(DFA6_specialS);
    static final short[][] DFA6_transition;

    static {
        int numStates = DFA6_transitionS.length;
        DFA6_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA6_transition[i] = DFA.unpackEncodedString(DFA6_transitionS[i]);
        }
    }

    class DFA6 extends DFA {

        public DFA6(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 6;
            this.eot = DFA6_eot;
            this.eof = DFA6_eof;
            this.min = DFA6_min;
            this.max = DFA6_max;
            this.accept = DFA6_accept;
            this.special = DFA6_special;
            this.transition = DFA6_transition;
        }
        public String getDescription() {
            return "71:2: cfgProductionElement : ( cfgTerminal -> cfgTerminal | cfgNonterminal -> cfgNonterminal | LPAREN cfgNonterminal RPAREN QUESTION -> ^( CFGOPTION cfgNonterminal ) | LPAREN cfgNonterminal RPAREN STAR -> ^( CFGSTAR cfgNonterminal ) | LPAREN cfgNonterminal RPAREN PLUS -> ^( CFGPLUS cfgNonterminal ) | LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE -> ^( CFGCHARRANGE CHAR_LIT CHAR_LIT ) | LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE -> ^( CFGCHARSEQRANGE CHAR_SEQ CHAR_SEQ ) );";
        }
    }
    static final String DFA9_eotS =
        "\13\uffff";
    static final String DFA9_eofS =
        "\13\uffff";
    static final String DFA9_minS =
        "\1\42\5\uffff\1\55\4\uffff";
    static final String DFA9_maxS =
        "\1\67\5\uffff\1\60\4\uffff";
    static final String DFA9_acceptS =
        "\1\uffff\1\1\1\2\1\3\1\4\1\5\1\uffff\1\10\1\11\1\6\1\7";
    static final String DFA9_specialS =
        "\13\uffff}>";
    static final String[] DFA9_transitionS = {
            "\1\1\11\uffff\1\6\3\uffff\1\3\1\2\1\uffff\1\4\1\uffff\1\5\1"+
            "\7\1\10",
            "",
            "",
            "",
            "",
            "",
            "\1\11\2\uffff\1\12",
            "",
            "",
            "",
            ""
    };

    static final short[] DFA9_eot = DFA.unpackEncodedString(DFA9_eotS);
    static final short[] DFA9_eof = DFA.unpackEncodedString(DFA9_eofS);
    static final char[] DFA9_min = DFA.unpackEncodedStringToUnsignedChars(DFA9_minS);
    static final char[] DFA9_max = DFA.unpackEncodedStringToUnsignedChars(DFA9_maxS);
    static final short[] DFA9_accept = DFA.unpackEncodedString(DFA9_acceptS);
    static final short[] DFA9_special = DFA.unpackEncodedString(DFA9_specialS);
    static final short[][] DFA9_transition;

    static {
        int numStates = DFA9_transitionS.length;
        DFA9_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA9_transition[i] = DFA.unpackEncodedString(DFA9_transitionS[i]);
        }
    }

    class DFA9 extends DFA {

        public DFA9(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 9;
            this.eot = DFA9_eot;
            this.eof = DFA9_eof;
            this.min = DFA9_min;
            this.max = DFA9_max;
            this.accept = DFA9_accept;
            this.special = DFA9_special;
            this.transition = DFA9_transition;
        }
        public String getDescription() {
            return "87:5: regDefinition : ( ID -> ID | STR_LIT -> STR_LIT | CHAR_SEQ -> CHAR_SEQ | ( KW_FIX LPAREN ID COMMA INT RPAREN ) -> ^( FIX ID INT ) | ( KW_STAR LPAREN regDefinition RPAREN ) -> ^( STAR regDefinition ) | ( LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE ) -> ^( RANGE CHAR_LIT CHAR_LIT ) | ( LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE ) -> ^( CHARSEQRANGE CHAR_SEQ CHAR_SEQ ) | ( KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( OR ( regDefinition )+ ) | ( KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( CONCAT ( regDefinition )+ ) );";
        }
    }
 

    public static final BitSet FOLLOW_statement_in_program300 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_SEMI_in_program302 = new BitSet(new long[]{0x0304002200000002L});
    public static final BitSet FOLLOW_vardeclStmt_in_statement323 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgStmt_in_statement339 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regStmt_in_statement354 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_valDeclStmt_in_statement369 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_assertStmt_in_statement384 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_VAR_in_vardeclStmt419 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_vardeclStmt421 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_COLON_in_vardeclStmt423 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_vardeclStmt425 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_70_in_vardeclStmt427 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_vardeclStmt429 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_VAR_in_vardeclStmt465 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_vardeclStmt467 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_COLON_in_vardeclStmt469 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_vardeclStmt471 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_CFG_in_cfgStmt510 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_cfgProduction_in_cfgStmt512 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_cfgProduction532 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ASSIGN_in_cfgProduction534 = new BitSet(new long[]{0x000310C400000000L});
    public static final BitSet FOLLOW_cfgProductionSet_in_cfgProduction537 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgProductionElementSet_in_cfgProductionSet561 = new BitSet(new long[]{0x0000004000000002L});
    public static final BitSet FOLLOW_BAR_in_cfgProductionSet564 = new BitSet(new long[]{0x000310C400000000L});
    public static final BitSet FOLLOW_cfgProductionElementSet_in_cfgProductionSet566 = new BitSet(new long[]{0x0000004000000002L});
    public static final BitSet FOLLOW_cfgProductionElement_in_cfgProductionElementSet585 = new BitSet(new long[]{0x0003108400000002L});
    public static final BitSet FOLLOW_cfgTerminal_in_cfgProductionElement608 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgNonterminal_in_cfgProductionElement638 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LPAREN_in_cfgProductionElement668 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_cfgNonterminal_in_cfgProductionElement670 = new BitSet(new long[]{0x0000010000000000L});
    public static final BitSet FOLLOW_RPAREN_in_cfgProductionElement672 = new BitSet(new long[]{0x0000020000000000L});
    public static final BitSet FOLLOW_QUESTION_in_cfgProductionElement674 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LPAREN_in_cfgProductionElement708 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_cfgNonterminal_in_cfgProductionElement710 = new BitSet(new long[]{0x0000010000000000L});
    public static final BitSet FOLLOW_RPAREN_in_cfgProductionElement712 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_STAR_in_cfgProductionElement714 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LPAREN_in_cfgProductionElement756 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_cfgNonterminal_in_cfgProductionElement758 = new BitSet(new long[]{0x0000010000000000L});
    public static final BitSet FOLLOW_RPAREN_in_cfgProductionElement760 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_PLUS_in_cfgProductionElement762 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LSQUARE_in_cfgProductionElement801 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_cfgProductionElement803 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_MINUS_in_cfgProductionElement805 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_cfgProductionElement807 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_RSQUARE_in_cfgProductionElement809 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LSQUARE_in_cfgProductionElement848 = new BitSet(new long[]{0x0001000000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_cfgProductionElement850 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_MINUS_in_cfgProductionElement852 = new BitSet(new long[]{0x0001000000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_cfgProductionElement854 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_RSQUARE_in_cfgProductionElement856 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_cfgTerminal0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_cfgNonterminal957 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_REG_in_regStmt974 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_regStmt976 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ASSIGN_in_regStmt978 = new BitSet(new long[]{0x00EB100400000000L});
    public static final BitSet FOLLOW_regDefinition_in_regStmt980 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_regDefinition1003 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_STR_LIT_in_regDefinition1029 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regDefinition1055 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_FIX_in_regDefinition1083 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_LPAREN_in_regDefinition1085 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_regDefinition1087 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_COMMA_in_regDefinition1089 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_regDefinition1091 = new BitSet(new long[]{0x0000010000000000L});
    public static final BitSet FOLLOW_RPAREN_in_regDefinition1093 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_STAR_in_regDefinition1127 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_LPAREN_in_regDefinition1129 = new BitSet(new long[]{0x00EB100400000000L});
    public static final BitSet FOLLOW_regDefinition_in_regDefinition1131 = new BitSet(new long[]{0x0000010000000000L});
    public static final BitSet FOLLOW_RPAREN_in_regDefinition1133 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LSQUARE_in_regDefinition1165 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_regDefinition1167 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_MINUS_in_regDefinition1169 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_regDefinition1171 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_RSQUARE_in_regDefinition1173 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LSQUARE_in_regDefinition1207 = new BitSet(new long[]{0x0001000000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regDefinition1209 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_MINUS_in_regDefinition1211 = new BitSet(new long[]{0x0001000000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regDefinition1213 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_RSQUARE_in_regDefinition1215 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_OR_in_regDefinition1250 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_LPAREN_in_regDefinition1252 = new BitSet(new long[]{0x00EB100400000000L});
    public static final BitSet FOLLOW_regDefinition_in_regDefinition1254 = new BitSet(new long[]{0x0010010000000000L});
    public static final BitSet FOLLOW_COMMA_in_regDefinition1257 = new BitSet(new long[]{0x00EB100400000000L});
    public static final BitSet FOLLOW_regDefinition_in_regDefinition1259 = new BitSet(new long[]{0x0010010000000000L});
    public static final BitSet FOLLOW_RPAREN_in_regDefinition1263 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_CONCAT_in_regDefinition1296 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_LPAREN_in_regDefinition1298 = new BitSet(new long[]{0x00EB100400000000L});
    public static final BitSet FOLLOW_regDefinition_in_regDefinition1300 = new BitSet(new long[]{0x0010010000000000L});
    public static final BitSet FOLLOW_COMMA_in_regDefinition1303 = new BitSet(new long[]{0x00EB100400000000L});
    public static final BitSet FOLLOW_regDefinition_in_regDefinition1305 = new BitSet(new long[]{0x0010010000000000L});
    public static final BitSet FOLLOW_RPAREN_in_regDefinition1309 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_VAL_in_valDeclStmt1350 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_valDeclStmt1352 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ASSIGN_in_valDeclStmt1354 = new BitSet(new long[]{0x0082000400000000L});
    public static final BitSet FOLLOW_expr_in_valDeclStmt1356 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_STR_LIT_in_expr1377 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_expr1391 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_CONCAT_in_expr1411 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_LPAREN_in_expr1413 = new BitSet(new long[]{0x0082000400000000L});
    public static final BitSet FOLLOW_expr_in_expr1415 = new BitSet(new long[]{0x0010010000000000L});
    public static final BitSet FOLLOW_COMMA_in_expr1418 = new BitSet(new long[]{0x0082000400000000L});
    public static final BitSet FOLLOW_expr_in_expr1420 = new BitSet(new long[]{0x0010010000000000L});
    public static final BitSet FOLLOW_RPAREN_in_expr1424 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_expr1444 = new BitSet(new long[]{0x0000100000000000L});
    public static final BitSet FOLLOW_LSQUARE_in_expr1446 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_expr1448 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_COLON_in_expr1450 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_INT_in_expr1452 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_RSQUARE_in_expr1454 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_ASSERT_in_assertStmt1477 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_boolExpr_in_assertStmt1479 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_boolExpr1516 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_KW_IN_in_boolExpr1518 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1520 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_boolExpr1549 = new BitSet(new long[]{0x0800000000000000L});
    public static final BitSet FOLLOW_KW_CONTAINS_in_boolExpr1551 = new BitSet(new long[]{0x0002000000000000L});
    public static final BitSet FOLLOW_STR_LIT_in_boolExpr1553 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_boolExpr1582 = new BitSet(new long[]{0x1000000000000000L});
    public static final BitSet FOLLOW_KW_NOT_in_boolExpr1584 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_KW_IN_in_boolExpr1586 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1588 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_boolExpr1628 = new BitSet(new long[]{0x1000000000000000L});
    public static final BitSet FOLLOW_KW_NOT_in_boolExpr1630 = new BitSet(new long[]{0x0800000000000000L});
    public static final BitSet FOLLOW_KW_CONTAINS_in_boolExpr1632 = new BitSet(new long[]{0x0002000000000000L});
    public static final BitSet FOLLOW_STR_LIT_in_boolExpr1634 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_boolExpr1663 = new BitSet(new long[]{0x2000000000000000L});
    public static final BitSet FOLLOW_KW_EQUALS_in_boolExpr1665 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1667 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_boolExpr1696 = new BitSet(new long[]{0x1000000000000000L});
    public static final BitSet FOLLOW_KW_NOT_in_boolExpr1698 = new BitSet(new long[]{0x2000000000000000L});
    public static final BitSet FOLLOW_KW_EQUALS_in_boolExpr1700 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1702 = new BitSet(new long[]{0x0000000000000002L});

}