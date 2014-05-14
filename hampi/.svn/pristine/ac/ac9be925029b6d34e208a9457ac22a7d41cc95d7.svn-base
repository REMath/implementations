package hampi.parser;

import hampi.HampiException;
import hampi.parser.HProgram.HTypeEnvironment;

public final class HSubsequenceExpression extends HExpression{
  private final String id;
  private final int startIndex, len;

  public HSubsequenceExpression(String id, String startIndex, String len){
    super(HGrammarElementKind.EXPR_SUBSEQUENCE);
    this.id = id;
    this.startIndex = Integer.parseInt(startIndex);
    this.len = Integer.parseInt(len);
  }

  public String getName(){
    return id;
  }

  @Override
  public String unparse(){
    return id + "[" + startIndex + ":" + len + "]";
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv, HVarDeclStatement varDecl){
    if (startIndex + len > varDecl.getSizeMax())
      throw new HampiException("subsequence cannot end after the variable ends");
  }

  public int getStartIndex(){
    return startIndex;
  }

  public int getLength(){
    return len;
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitSubsequenceExpr(this);
  }


  @Override
  public HType getType(HTypeEnvironment tenv){
    return tenv.getType(id);
  }

}
