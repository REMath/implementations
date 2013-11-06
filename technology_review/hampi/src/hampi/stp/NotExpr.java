package hampi.stp;

import hampi.utils.Utils;
import stp.Expr;

/**
 * Negation.
 */
public final class NotExpr extends STPExpr{

  private final STPExpr e;

  public static STPExpr create(STPExpr e, STPSolver solver){
    return new NotExpr(e, solver);
  }

  private NotExpr(STPExpr e, STPSolver solver){
    super(STPExprKind.NotExpr, solver);
    assert e != null;
    this.e = e;
  }

  @Override
  public String toString(int indent){
    return Utils.spaces(indent) + "NOT(\n" + e.toString(indent + "NOT(".length()) + ")";
  }

  @Override
  public Expr internalGetExpr(SolvingContext sc, int shift){
    Expr expr = e.getExpr(sc, shift);
    getSolver().nativeSTPObjectCreationTimer.start();
    Expr result = sc.getVC().notExpr(expr);
    getSolver().nativeSTPObjectCreationTimer.stop();
    return result;
  }

  @Override
  public int size(){
    return e.size() + 1;
  }
}
