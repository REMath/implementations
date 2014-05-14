package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

import java.util.Set;

public final class CFGStar extends CFGProductionElement{

  private final CFGProductionElement el;

  public CFGStar(CFGProductionElement el){
    super(HGrammarElementKind.CFG_STAR);
    this.el = el;
  }

  @Override
  public String unparse(){
    return "(" + el.toString() + ")*";
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    el.typeCheck(tenv);
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitStar(this);
    el.accept(v);
  }

  public CFGProductionElement getSubelement(){
    return el;
  }

  @Override
  public Set<String> getTerminals(){
    return el.getTerminals();
  }
}