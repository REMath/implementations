package hampi.stp;

import hampi.utils.*;
import stp.Expr;

/**
 * Bitvector declaration.
 */
public class BVExpr extends STPExpr{

  private final String name;
  private final int    size;

  public static BVExpr create(STPSolver solver, String name, int size){
    return new BVExpr(solver, name, size);
  }

  private BVExpr(STPSolver solver, String name, int size){
    super(STPExprKind.BVExpr, solver);
    assert name != null;
    assert size > 0;
    this.name = name;
    this.size = size;
  }

  @Override
  public String toString(int indent){
    return Utils.spaces(indent) + name + "(" + size + ")";
  }

  public int vectorSize(){
    return size;
  }

  public String getName(){
    return name;
  }

  @Override
  public Expr internalGetExpr(SolvingContext sc, int shift){
    getSolver().nativeSTPObjectCreationTimer.start();
    Expr results = sc.getVC().varExpr(name, sc.getVC().bvType(size));
    getSolver().nativeSTPObjectCreationTimer.stop();
    return results;
  }

  private final DoubleKeyMap<Integer, Integer, STPExpr> cachedExtract = new DoubleKeyMap<Integer, Integer, STPExpr>();

  /**
   * Returns an expression that denotes a specified subvector.
   */
  public STPExpr extract(int high_bit_no, int low_bit_no, int encodingSize){
    STPExpr cached = cachedExtract.get(high_bit_no, low_bit_no);
    if (cached != null)
      return cached;
    ExtractExpr exp = new ExtractExpr(getSolver(), this, high_bit_no, low_bit_no, encodingSize);
    cachedExtract.put(high_bit_no, low_bit_no, exp);
    return exp;
  }

  @Override
  public int size(){
    return 1;
  }
}
