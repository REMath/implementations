package hampi.stp;

import stp.VC;

public class SolvingContext{
  private VC vc;
  private final ChoiceGenerator<STPExpr> cg;
  private final CharacterEncoding enc;

  public SolvingContext(ChoiceGenerator<STPExpr> cg, CharacterEncoding enc){
    this.cg = cg;
    this.enc = enc;
  }

  public VC getVC(){
    return vc;
  }

  public CharacterEncoding getEncoding(){
    return enc;
  }

  public ChoiceGenerator<STPExpr> getChoiceGenerator(){
    return cg;
  }

  public void setVC(VC vc){
    this.vc= vc;
  }
}
