package hampi.parser;

import hampi.parser.HProgram.HTypeEnvironment;

public class HRangeRegexp extends HRegDefinition{

  private final char ch1;
  private final char ch2;

  public HRangeRegexp(String ch1, String ch2){
    super(HGrammarElementKind.REG_RANGE);
    assert ch1.length() == 3;
    assert ch2.length() == 3;
    this.ch1 = ch1.charAt(1);
    this.ch2 = ch2.charAt(1);
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    // TODO Auto-generated method stub
  }

  @Override
  public String unparse(){
    return "[\'" + ch1 + "'-'" + ch2 + "']";
  }

  public char getLow(){
    return ch1;
  }

  public char getHigh(){
    return ch2;
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitRangeRegexp(this);
  }

}
