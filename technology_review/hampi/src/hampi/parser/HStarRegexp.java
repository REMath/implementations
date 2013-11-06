package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

public class HStarRegexp extends HRegDefinition{

  private final HRegDefinition r;

  public HStarRegexp(HRegDefinition r){
    super(HGrammarElementKind.REG_STAR);
    this.r = r;
  }

  public HRegDefinition getSubRegexp(){
    return r;
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    r.typeCheck(tenv);
  }

  @Override
  public String unparse(){
    return "star(" + r.unparse() + ")";
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitStarRegexp(this);
    r.accept(v);
  }
}
