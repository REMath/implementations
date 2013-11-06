package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

public abstract class HExpression extends HAbstractGrammarElement{

  protected HExpression(HGrammarElementKind kind){
    super(kind);
  }

  /**
   * Returns the type of the expression.
   */
  public abstract HType getType(HTypeEnvironment tenv);

  public abstract void typeCheck(HTypeEnvironment tenv, HVarDeclStatement varDecl);
}
