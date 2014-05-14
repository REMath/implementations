package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

import java.util.*;

public final class CFGCharRange extends CFGProductionElement{

  private final char low;
  private final char high;

  public CFGCharRange(String ch1, String ch2){
    super(HGrammarElementKind.CFG_CHAR_RANGE);
    assert ch1.length() == 3;
    assert ch2.length() == 3;
    this.low = ch1.charAt(1);
    this.high = ch2.charAt(1);
    assert this.low <= this.high;
  }

  public char getLow(){
    return low;
  }

  public char getHigh(){
    return high;
  }

  @Override
  public String unparse(){
    return "[\'" + low + "'-'" + high + "']";
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    // ok
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitCFGCharRange(this);
  }

  /**
   * Returns all chars in the range.
   */
  public char[] getChars(){
    char[] chars = new char[high - low + 1];
    for (int i = low; i <= high; i++){
      chars[i - low] = (char) i;
    }
    return chars;
  }

  @Override
  public Set<String> getTerminals(){
    Set<String> result = new LinkedHashSet<String>();
    for (char c : getChars()){
      result.add(String.valueOf(c));
    }
    return result;
  }
}
