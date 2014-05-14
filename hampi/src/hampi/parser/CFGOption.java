package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

import java.util.Set;

public final class CFGOption extends CFGProductionElement{

  private final CFGProductionElement el;

  public CFGOption(CFGProductionElement el){
    super(HGrammarElementKind.CFG_OPTION);
    this.el = el;
  }

  public CFGProductionElement getSubelement(){
    return el;
  }

  @Override
  public String unparse(){
    return "(" + el.toString() + ")?";
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    el.typeCheck(tenv);
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitCFGOption(this);
    el.accept(v);
  }

  @Override
  public Set<String> getTerminals(){
    return el.getTerminals();
  }
}
