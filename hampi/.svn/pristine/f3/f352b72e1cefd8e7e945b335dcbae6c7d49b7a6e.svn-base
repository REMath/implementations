package hampi.stp;

import hampi.utils.Utils;
import stp.Expr;

/**
 * Constant value.
 */
public final class ConstExpr extends STPExpr{

  private final int                          val;

  public static STPExpr create(STPSolver solver, int val){
    STPExpr cached = solver.getCache().getConst(val);
    if (cached != null)
      return cached;
    ConstExpr e = new ConstExpr(solver, val);
    solver.getCache().putConst(val, e);
    return e;
  }

  private ConstExpr(STPSolver solver, int val){
    super(STPExprKind.ConstExpr, solver);
    this.val = val;
  }

  @Override
  public Expr internalGetExpr(SolvingContext sc, int shift){
    getSolver().nativeSTPObjectCreationTimer.start();
    Expr result = sc.getEncoding().stpConst(sc.getVC(), val);
    getSolver().nativeSTPObjectCreationTimer.stop();
    return result;
  }

  @Override
  public String toString(int indent){
    return Utils.spaces(indent) + String.valueOf(val);
  }

  @Override
  public int size(){
    return 1;
  }
}
