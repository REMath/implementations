package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

public final class HVarReferenceExpression extends HExpression{

  private final String id;

  public HVarReferenceExpression(String id){
    super(HGrammarElementKind.EXPR_VAR);
    this.id = id;
  }

  @Override
  public String unparse(){
    return id;
  }

  public String getName(){
    return id;
  }

  @Override
  public HType getType(HTypeEnvironment tenv){
    return tenv.getType(id);
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv, HVarDeclStatement varDecl){
    //nothing
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitVarReferenceExpression(this);
  }
}
