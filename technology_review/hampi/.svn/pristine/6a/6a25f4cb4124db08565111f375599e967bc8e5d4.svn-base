package hampi.parser;

import hampi.HampiException;
import hampi.parser.HProgram.HTypeEnvironment;

import java.util.*;

public final class HConcatExpression extends HExpression{

  public HConcatExpression(){
    super(HGrammarElementKind.EXPR_CONCAT);
    this.subexprs = new ArrayList<HExpression>();
  }

  private final List<HExpression> subexprs;

  public void add(HExpression sube){
    this.subexprs.add(sube);
  }

  public List<HExpression> getSubExpressions(){
    return subexprs;
  }

  @Override
  public String unparse(){
    StringBuilder b = new StringBuilder();
    b.append("concat(");
    for (Iterator<HExpression> iter = subexprs.iterator(); iter.hasNext();){
      HExpression type = iter.next();
      b.append(type.toString());
      if (iter.hasNext()){
        b.append(", ");
      }
    }
    b.append(")");
    return b.toString();
  }

  @Override
  public HType getType(HTypeEnvironment tenv){
    return HType.STRING_TYPE;
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv, HVarDeclStatement varDecl){
    for (HExpression sube : subexprs){
      sube.typeCheck(tenv, varDecl);
      HType type = sube.getType(tenv);
      if (type != HType.STRING_TYPE)
        throw new HampiException("invalid type in concat " + sube + " type " + type + " (expected string)");
    }
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitConcatExpression(this);
    for (HExpression expr : subexprs){
      expr.accept(v);
    }
  }

}
