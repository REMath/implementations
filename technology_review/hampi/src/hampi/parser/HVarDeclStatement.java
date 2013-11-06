package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

public final class HVarDeclStatement extends HStatement{

  private final String name;
  private final int    sizeMin;
  private final int    sizeMax;

  public HVarDeclStatement(String text, String size){
      this(text, size, size);
  }

  public HVarDeclStatement(String text, String sizeMin, String sizeMax){
    super(HGrammarElementKind.STMT_VARDECL);
    this.name = text;
    int s1 = Integer.parseInt(sizeMin);
    int s2 = Integer.parseInt(sizeMax);
    this.sizeMin = Math.min(s1, s2);
    this.sizeMax = Math.max(s1, s2);
  }

  @Override
  public String unparse(){
    if (sizeMin == sizeMax)
	return "var " + name + ":" + sizeMin + ";";
    else
        return "var " + name + ":" + sizeMin + ".." + sizeMax + ";";
  }

  /**
   * Returns the variable's name.
   */
  public String getVarName(){
    return name;
  }

  /**
   * Returns the declared minimal size of the variable.
   */
  public int getSizeMin(){
    return sizeMin;
  }

  /**
   * Returns the declared maximal size of the variable.
   */
  public int getSizeMax(){
    return sizeMax;
  }


  @Override
  public void typeCheck(HTypeEnvironment tenv, HVarDeclStatement varDecl){
    //nothing
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitVarDeclStatement(this);
  }
}
