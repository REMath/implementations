package hampi.stp;

import hampi.utils.Utils;
import stp.Expr;

/**
 * Binary operator expression.
 */
public final class BinOpExpr extends STPExpr{

  private final BinOpKind binopKind;
  private final STPExpr   e1;
  private final STPExpr   e2;

  //made package visible because it's called from outside
  BinOpExpr(BinOpKind kind, STPExpr e1, STPExpr e2, STPSolver solver){
    super(STPExprKind.BinOpExpr, solver);
    assert kind != null;
    assert e1 != null;
    assert e2 != null;
    this.binopKind = kind;
    this.e1 = e1;
    this.e2 = e2;
  }

  @Override
  public String toString(int indent){
    StringBuilder b = new StringBuilder();
    b.append(Utils.spaces(indent));
    b.append(e1.toString(0));
    b.append(binopKind.toString());
    b.append(e2.toString(0));
    return b.toString();
  }

  @Override
  public Expr internalGetExpr(SolvingContext sc, int shift){
    Expr expr1 = e1.getExpr(sc, shift);
    Expr expr2 = e2.getExpr(sc, shift);
    Expr result = null;
    getSolver().nativeSTPObjectCreationTimer.start();
    switch (binopKind){
    case EQ_OP:
      result = sc.getVC().eqExpr(expr1, expr2);
      break;
    case GE_OP:
      result = sc.getVC().bvGeExpr(expr1, expr2);
      break;
    case GT_OP:
      result = sc.getVC().bvGtExpr(expr1, expr2);
      break;
    case LE_OP:
      result = sc.getVC().bvLeExpr(expr1, expr2);
      break;
    case LT_OP:
      result = sc.getVC().bvLtExpr(expr1, expr2);
      break;
    default:
      throw new IllegalStateException("unexpected kind " + binopKind);
    }
    getSolver().nativeSTPObjectCreationTimer.stop();
    return result;
  }

  @Override
  public int size(){
    int size = 1;//for this node
    size += e1.size();
    size += e2.size();
    return size;

  }
}
