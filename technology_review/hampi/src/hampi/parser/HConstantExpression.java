package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;
import hampi.utils.Utils;

public final class HConstantExpression extends HExpression{

  private final String text;

  public HConstantExpression(String text){
    super(HGrammarElementKind.EXPR_CONST);
    this.text = Utils.stripQuotes(text);
  }

  public String getValue(){
    return text;
  }

  @Override
  public String unparse(){
    return Utils.quotes(text);
  }

  @Override
  public HType getType(HTypeEnvironment tenv){
    return HType.STRING_TYPE;
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv, HVarDeclStatement varDecl){
    //nothing
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitConstantExpression(this);
  }
}
