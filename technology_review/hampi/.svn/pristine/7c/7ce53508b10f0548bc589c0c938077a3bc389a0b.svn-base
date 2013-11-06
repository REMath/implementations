package hampi.stp;

import hampi.utils.Utils;
import stp.Expr;

/**
 * Extraction from a bitvector.
 */
public final class ExtractExpr extends STPExpr{
  private final int    high;
  private final int    low;
  private final BVExpr bv;
  private final int    encodingSize;

  //made package visible because it's called from outside (from the BVExpr which also does caching)
  ExtractExpr(STPSolver solver, BVExpr bv, int high_bit_no, int low_bit_no, int encodingSize){
    super(STPExprKind.ExtractExpr, solver);
    assert high_bit_no >= low_bit_no;
    assert low_bit_no >= 0;
    assert bv != null;
    assert high_bit_no <= bv.vectorSize() : high_bit_no + " " + bv.vectorSize();
    assert encodingSize >= 1;
    this.bv = bv;
    this.high = high_bit_no;
    this.low = low_bit_no;
    this.encodingSize = encodingSize;
  }

  @Override
  public String toString(int indent){
    return Utils.spaces(indent) + bv.getName() + "[" + low + ":" + high + "]";
  }

  @Override
  public Expr internalGetExpr(SolvingContext sc, int shift){
    Expr expr = bv.getExpr(sc, shift);
    getSolver().nativeSTPObjectCreationTimer.start();
    Expr result = sc.getVC().bvExtract(expr, shifted(high, shift), shifted(low, shift));
    getSolver().nativeSTPObjectCreationTimer.stop();
    return result;
  }

  private int shifted(int lowOrHigh, int diff){
    return lowOrHigh + (diff * encodingSize);
  }

  @Override
  public int size(){
    return bv.size() + 1;
  }
}
