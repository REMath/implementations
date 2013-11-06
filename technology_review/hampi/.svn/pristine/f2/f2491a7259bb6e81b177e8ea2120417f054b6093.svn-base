package hampi.stp;

import hampi.utils.DoubleKeyMap;

import java.util.*;

import stp.*;

/**
 * This hierarchy describes STP expressions but without creating their native
 * peers right away (like the Expr hierarchy does). This allows more
 * manipulation of the expression before it's converted to STP format and
 * solved.
 *
 * In particular, it enables 2 features: <br>
 * a) solving of the STP formula either by command-line STP or by the JNI
 * binding (useful for debugging) <br>
 * b) using one STPExpr as a template for another (e.g., they may be identical
 * modulo extracted ranges in the bitvector on which they operate)
 */
public abstract class STPExpr{
  private final STPExprKind kind;
  private final STPSolver solver;

  protected STPExpr(STPExprKind kind, STPSolver solver){
    assert kind != null;
    this.kind = kind;
    this.solver = solver;
  }

  public STPSolver getSolver(){
    return solver;
  }
  public STPExprKind getKind(){
    return kind;
  }

  @Override
  public final String toString(){
    return toString(0);
  }

  public abstract String toString(int indent);

  private final Map<Integer, Expr> cachedShiftToNativeSTPObject = new LinkedHashMap<Integer, Expr>();
  private VC cachedVC;

  /**
   * Creates an STP expression (backed by native objects) using the given
   * encoding.
   */
  public final Expr getExpr(SolvingContext sc, int shift){
    if (!STPSolver.INCREMENTAL){
    //We use cached value but only if shift and vc is the same
        if (cachedShiftToNativeSTPObject.containsKey(shift) && cachedVC.equals(sc.getVC()))
          return cachedShiftToNativeSTPObject.get(shift);
    }
    Expr e = internalGetExpr(sc, shift);

    if (!STPSolver.INCREMENTAL){
      cachedShiftToNativeSTPObject.put(shift, e);
    }
    cachedVC = sc.getVC();
    return e;
  }

  /**
   * Creates an STP expression (backed by native objects). Not to be called from
   * client code (use getExpr instead, which goes through the cache).
   */
  public abstract Expr internalGetExpr(SolvingContext sc, int shift);

  public static List<Expr> exprList(SolvingContext sc, List<STPExpr> exprs, int shift){
    List<Expr> res = new ArrayList<Expr>(exprs.size());
    for (STPExpr expr : exprs){
      res.add(expr.getExpr(sc, shift));
    }
    return res;
  }

  @Override
  public final boolean equals(Object obj){//all objects will be made canonical so we force identity as equals
    return obj == this;
  }

  @Override
  public final int hashCode(){//all objects will be made canonical so we force identity as equals
    return System.identityHashCode(this);
  }

  /*
   * Cache of binops.
   */
  private final DoubleKeyMap<BinOpKind, STPExpr, STPExpr> cachedBinops = new DoubleKeyMap<BinOpKind, STPExpr, STPExpr>();

  /**
   * Creates a binop for this expression. Placed here for efficient caching
   * (storing cache in the object itself avoids 1 hashtable lookup on every
   * binop created).
   */
  STPExpr binOp(BinOpKind opKind, STPExpr e2){
    STPExpr cached = cachedBinops.get(opKind, e2);
    if (cached != null)
      return cached;

    STPExpr e = new BinOpExpr(opKind, this, e2, getSolver());
    cachedBinops.put(opKind, e2, e);
    return e;
  }

  /**
   * Cache of diff->shifted expressions. Stored here but managed by
   * ShiftedSTPExpr because one expression can have many shifts and the
   * expression does not know its shifts.
   */
  protected final Map<Integer, STPExpr> shiftCache = new LinkedHashMap<Integer, STPExpr>();

  /**
   * Returns the size of the expression. This counts one for each node (internal
   * and leaf).
   */
  public abstract int size();
}
