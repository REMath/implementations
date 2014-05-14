package hampi.parser;

import hampi.HampiException;
import hampi.parser.HProgram.HTypeEnvironment;
import hampi.utils.Utils;

public final class HContainsExpression extends HBooleanExpression{

  private final String  id;
  private final String  str;
  private final boolean contains;

  public HContainsExpression(String id, String str, boolean contains){
    super(HGrammarElementKind.BEXPR_CONTAINS);
    this.id = id;
    this.str = Utils.stripQuotes(str);
    this.contains = contains;
  }

  /**
   * Returns the v from: v contains "foo"
   */
  public String getVariableName(){
    return id;
  }

  /**
   * Returns the "foo" from: v contains "foo"
   */
  public String getString(){
    return str;
  }

  @Override
  public String unparse(){
    return id + (contains ? "" : " not") + " contains " + Utils.quotes(str);
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv, HVarDeclStatement varDecl){
    if (tenv.getType(id) == null)
      throw new HampiException("undefined variable " + id + " in 'contains'");
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitContainsExpression(this);
  }

  public boolean contains(){
    return contains;
  }
}
