package hampi.parser;

import hampi.HampiException;
import hampi.parser.HProgram.HTypeEnvironment;

public class HEqualsExpression extends HBooleanExpression{

  private final String id1;
  private final String id2;
  private final boolean equals;

  public HEqualsExpression(String id1, String id2, boolean equals){
    super(HGrammarElementKind.BEXPR_EQUALS);
    this.id1 = id1;
    this.id2 = id2;
    this.equals = equals;
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv, HVarDeclStatement varDecl){
    if (tenv.getType(id1) == null)
      throw new HampiException("undefined variable " + id1 + " in 'equals'");
    if (tenv.getType(id2) == null)
      throw new HampiException("undefined variable " + id2 + " in 'equals'");
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitEqualsExpression(this);
  }

  @Override
  public String unparse(){
    return id1 + (equals ? "=" : "!=") + id2;
  }

  public String getId1(){
    return id1;
  }

  public String getId2(){
    return id2;
  }

  public boolean equals(){
    return equals;
  }

}
