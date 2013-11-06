package hampi.stp;

import hampi.utils.Utils;
import stp.Expr;

/**
 * This is a lazy representation of a shifted STP expression. Instead of
 * shifting right away, this class delays the shifting until necessary.
 *
 * This class represents what the paper calls 'constraint templates'. It's a
 * space- and time-efficient representation of related STP expressions. Shift of
 * an STP expression e1 by i is represents an STP expression e2 that is
 * identical to e1 but has every offset o of a character changed to o+i.
 */
public final class ShiftedSTPExpr extends STPExpr{

  private final STPExpr e;
  private final int     diff;

  private ShiftedSTPExpr(STPSolver solver, STPExpr e, int diff){
    super(e.getKind(), solver);
    if (e instanceof ShiftedSTPExpr)
      throw new IllegalArgumentException("do not nest shifts");
    this.e = e;
    this.diff = diff;
  }

  public static STPExpr shift(STPExpr e, int diff){
    if (diff == 0)
      return e;
    STPExpr shiftee;
    int shiftDiff;
    if (e instanceof ShiftedSTPExpr){
      //no not nest shifts
      ShiftedSTPExpr shifted = (ShiftedSTPExpr) e;
      shiftee = shifted.e;
      shiftDiff = shifted.diff + diff;
    }else{
      shiftee = e;
      shiftDiff = diff;
    }

    if (shiftee.shiftCache.containsKey(shiftDiff))
      return shiftee.shiftCache.get(shiftDiff);
    ShiftedSTPExpr shiftedSTPExpr = new ShiftedSTPExpr(e.getSolver(), shiftee, shiftDiff);
    shiftee.shiftCache.put(shiftDiff, shiftedSTPExpr);
    return shiftedSTPExpr;
  }

  @Override
  public Expr internalGetExpr(SolvingContext sc, int shift){
    return e.getExpr(sc, shift + diff);
  }

  @Override
  public String toString(int indent){
    return Utils.spaces(indent) + "SHIFT(" + diff + ",\n" + e.toString(indent + "SHIFT(".length()) + ")";
  }

  @Override
  public int size(){
    return 1 + e.size();
  }
}