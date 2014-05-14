package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

import java.util.Set;

public abstract class CFGProductionElement extends HAbstractGrammarElement{

  protected CFGProductionElement(HGrammarElementKind kind){
    super(kind);
  }

  public abstract void typeCheck(HTypeEnvironment tenv);

  /**
   * Returns the set of terminals.
   */
  public abstract Set<String> getTerminals();
}
