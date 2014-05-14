package hampi.parser;

import hampi.HampiException;
import hampi.parser.HProgram.HTypeEnvironment;

import java.util.*;

public final class CFGNonterminal extends CFGProductionElement{

  private final String name;

  public CFGNonterminal(String text){
    super(HGrammarElementKind.CFG_NONTERMINAL);
    this.name = text;
  }

  public String getName(){
    return name;
  }

  @Override
  public String unparse(){
    return name;
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    if (tenv.getType(name) == null)
      throw new HampiException("undefined nonterminal " + name);
    if (tenv.getType(name) != HType.CFG_TYPE)
      throw new HampiException("expected a nonterminal " + name);
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitCFGNonterminal(this);
  }

  @Override
  public Set<String> getTerminals(){
    return Collections.emptySet();
  }
}
