package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

public final class HRegVarRef extends HRegDefinition{

  private final String name;

  protected HRegVarRef(String name){
    super(HGrammarElementKind.REG_VAR);
    this.name = name;
  }

  public String getName(){
    return name;
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    // TODO Auto-generated method stub
  }

  @Override
  public String unparse(){
    return name;
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitRegVarRef(this);
  }
}
