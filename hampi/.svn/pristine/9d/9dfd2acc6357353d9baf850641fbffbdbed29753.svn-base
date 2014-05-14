package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

import java.util.Set;

public final class CFGPlus extends CFGProductionElement{

  private final CFGProductionElement el;

  public CFGPlus(CFGProductionElement el){
    super(HGrammarElementKind.CFG_PLUS);
    this.el = el;
  }

  @Override
  public String unparse(){
    return "(" + el.toString() + ")+";
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    el.typeCheck(tenv);
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitCFGPlus(this);
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
