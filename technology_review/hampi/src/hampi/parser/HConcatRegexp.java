package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

import java.util.*;

public class HConcatRegexp extends HRegDefinition{

  private final List<HRegDefinition> exprs;

  protected HConcatRegexp(){
    super(HGrammarElementKind.REG_CONCAT);
    this.exprs = new ArrayList<HRegDefinition>();
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    // TODO Auto-generated method stub
  }

  @Override
  public String unparse(){
    StringBuilder b = new StringBuilder();
    b.append("concat(");
    for (Iterator<HRegDefinition> iter = exprs.iterator(); iter.hasNext();){
      HRegDefinition sub = iter.next();
      b.append(sub.unparse());
      if (iter.hasNext()){
        b.append(", ");
      }
    }
    b.append(")");
    return b.toString();
  }

  public void add(HRegDefinition r){
    exprs.add(r);
  }

  public List<HRegDefinition> getExpressions(){
    return exprs;
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitConcatRegexp(this);
    for (HRegDefinition def : exprs){
      def.accept(v);
    }
  }
}
