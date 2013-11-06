package hampi.parser;

public final class TokenTypes{
  public static String getTokenType(int tokenType){
    switch (tokenType){
    case HampiLexer.KW_QUERY:
      return "QUERY";
    case HampiLexer.KW_REG:
      return "REG";
    case HampiLexer.KW_VAL:
      return "VAL";
    case HampiLexer.KW_VAR:
      return "VAR";
    case HampiLexer.KW_CONCAT:
      return "CONCAT";
    case HampiLexer.KW_FIX:
      return "FIX";
    case HampiLexer.KW_OR:
      return "OR";
    case HampiLexer.KW_NOT:
      return "NOT";
    case HampiLexer.KW_ASSERT:
      return "ASSERT";
    case HampiLexer.KW_CONTAINS:
      return "CONTAINS";
    case HampiLexer.KW_IN:
      return "IN";
    case HampiLexer.KW_CFG:
      return "CFG";
    case HampiLexer.ID:
      return "ID";
    case HampiLexer.SEMI:
      return "SEMI";
    case HampiLexer.COLON:
      return "COLON";
    case HampiLexer.ASSIGN:
      return "ASSIGN";
    case HampiLexer.STR_LIT:
      return "STR_LIT";
    case HampiLexer.BAR:
      return "BAR";
    case HampiLexer.MINUS:
      return "MINUS";
    case HampiLexer.CHAR_LIT:
      return "CHAR_LIT";

    case HampiLexer.LPAREN:
      return "LPAREN";
    case HampiLexer.RPAREN:
      return "RPAREN";
    case HampiLexer.COMMA:
      return "COMMA";
    case HampiLexer.EQUALS:
      return "EQUALS";
    case HampiLexer.OR:
      return "OR";
    case HampiLexer.STAR:
      return "STAR";
    case HampiLexer.PLUS:
      return "PLUS";
    case HampiLexer.QUESTION:
      return "QUESTION";
    case HampiLexer.LSQUARE:
      return "LSQUARE";
    case HampiLexer.RSQUARE:
      return "RSQUARE";
    case HampiLexer.INT:
      return "INT";

    default:
      //      return "OTHER";
      return "OTHER(" + tokenType + ")";
    }
  }

}
