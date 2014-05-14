package hampi.grammars.apps;

import hampi.grammars.*;

import java.util.List;

/**
 * Removes production cycles like S = S; <Br>
 * TODO remove cycles like S = T; T = S;
 */
public final class UselessProductionCycleRemover{

  public void remove(Grammar g, String startSymbol){
    List<GrammarProduction> productions = g.getProductions();
    for (GrammarProduction prod : productions){
      if (isUselessCycle(prod)){
        prod.getRule().removeProduction(prod);
      }
    }
  }

  //returns whether the production is S = S;
  private boolean isUselessCycle(GrammarProduction prod){
    return prod.getElements().size() == 1 && prod.getNonterminal().equals(prod.getElements().get(0));
  }

}
