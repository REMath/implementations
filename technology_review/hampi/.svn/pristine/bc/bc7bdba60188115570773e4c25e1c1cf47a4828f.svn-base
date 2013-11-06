package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

import java.util.*;

public final class CFGStatement extends HStatement{

  private String                                 id;
  private final List<List<CFGProductionElement>> elementSets;

  public CFGStatement(){
    super(HGrammarElementKind.STMT_CFG);
    this.elementSets = new ArrayList<List<CFGProductionElement>>();
  }

  @Override
  public String unparse(){
    StringBuilder b = new StringBuilder();
    b.append("cfg ");
    b.append(id);
    b.append(" := ");
    for (Iterator<List<CFGProductionElement>> elemSetIter = elementSets.iterator(); elemSetIter.hasNext();){
      List<CFGProductionElement> elemSet = elemSetIter.next();
      for (Iterator<CFGProductionElement> elemIter = elemSet.iterator(); elemIter.hasNext();){
        CFGProductionElement elem = elemIter.next();
        b.append(elem);
        if (elemIter.hasNext()){
          b.append(" ");
        }
      }
      if (elemSetIter.hasNext()){
        b.append(" | ");
      }
    }
    b.append(";");
    return b.toString();
  }

  public void setId(String id){
    this.id = id;
  }

  public List<List<CFGProductionElement>> getElementSets(){
    return elementSets;
  }

  public void appendElementSet(List<CFGProductionElement> cfgElemSet){
    this.elementSets.add(cfgElemSet);
  }

  public String getVarName(){
    return id;
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv, HVarDeclStatement varDecl){
    for (List<CFGProductionElement> elems : elementSets){
      for (CFGProductionElement elem : elems){
        elem.typeCheck(tenv);
      }
    }
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitCFGStatement(this);
    for (List<CFGProductionElement> elemSet : elementSets){
      for (CFGProductionElement elem : elemSet){
        elem.accept(v);
      }
    }
  }

  public Set<String> getTerminals(){
    Set<String> result = new LinkedHashSet<String>();
    for (List<CFGProductionElement> elementSet : elementSets){
      for (CFGProductionElement elem : elementSet){
        result.addAll(elem.getTerminals());
      }
    }
    return result;
  }

}