package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;


public final class HValDeclStatement extends HStatement{

  private final String     id;
  private final HExpression e;

  public HValDeclStatement(String text, HExpression e){
    super(HGrammarElementKind.STMT_VALDECL);
    assert text != null;
    assert e != null;
    this.id = text;
    this.e = e;
  }

  @Override
  public String unparse(){
    return "val " + id + " := " + e.toString() + ";";
  }

  public String getVarName(){
    return id;
  }

  public HExpression getExpression(){
    return e;
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv, HVarDeclStatement varDecl){
    e.typeCheck(tenv, varDecl);
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitValDeclStatement(this);
    e.accept(v);
  }
}
