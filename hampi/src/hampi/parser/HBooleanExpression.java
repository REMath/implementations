package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

public abstract class HBooleanExpression extends HExpression{

  protected HBooleanExpression(HGrammarElementKind kind){
    super(kind);
  }

  @Override
  public final HType getType(HTypeEnvironment tenv){
    return HType.BOOLEAN_TYPE;
  }

}
