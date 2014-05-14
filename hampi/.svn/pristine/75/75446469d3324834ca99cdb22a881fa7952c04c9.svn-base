package hampi.stp;

import hampi.utils.Utils;
import stp.Expr;

/**
 * Constant boolean value.
 */
public final class BoolConstSTPExpr extends STPExpr{
  private final boolean       isTrue;

  BoolConstSTPExpr(STPSolver solver, boolean isTrue){
    super(STPExprKind.BoolConstExpr, solver);
    this.isTrue = isTrue;
  }

  @Override
  public String toString(int indent){
    return Utils.spaces(indent) + (isTrue ? "TRUE" : "FALSE");
  }

  @Override
  public Expr internalGetExpr(SolvingContext sc, int shift){
    getSolver().nativeSTPObjectCreationTimer.start();
    Expr result = isTrue ? sc.getVC().trueExpr() : sc.getVC().falseExpr();
    getSolver().nativeSTPObjectCreationTimer.stop();
    return result;
  }

  @Override
  public int size(){
    return 1;
  }
}
