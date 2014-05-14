package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

import java.util.*;

public final class CFGTerminal extends CFGProductionElement{

  private final String text;

  public CFGTerminal(String text){
    super(HGrammarElementKind.CFG_TERMINAL);
    this.text = text;
  }

  @Override
  public String unparse(){
    return text;
  }

  public String getText(){
    return text;
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    //ok
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitTerminal(this);
  }

  @Override
  public Set<String> getTerminals(){
    return Collections.singleton(text);
  }
}
