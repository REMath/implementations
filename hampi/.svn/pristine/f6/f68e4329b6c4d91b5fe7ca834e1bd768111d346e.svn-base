package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;
import hampi.utils.Utils;

public class HConstRegexp extends HRegDefinition{

  private final String text;

  public HConstRegexp(String text){
    super(HGrammarElementKind.REG_CONST);
    this.text = Utils.stripQuotes(text);
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    //nothing
  }

  @Override
  public String unparse(){
    return Utils.quotes(text);
  }

  public String getString(){
    return text;
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitConstRegexp(this);
  }
}
