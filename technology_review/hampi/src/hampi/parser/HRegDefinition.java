package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

public abstract class HRegDefinition extends HAbstractGrammarElement{

  protected HRegDefinition(HGrammarElementKind kind){
    super(kind);
  }

  public abstract void typeCheck(HTypeEnvironment tenv);
}
