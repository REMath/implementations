package hampi.stp;

import hampi.utils.Utils;

import java.util.*;

import stp.Expr;

/**
 * The logical AND expression.
 */
public final class AndExpr extends STPExpr{
  private final List<STPExpr> exprs;

  public static STPExpr create(STPSolver solver, STPExpr... exprs){
    return create(solver, Arrays.asList(exprs));
  }

  public static STPExpr create(STPSolver solver, List<STPExpr> expressions){
    STPExpr cached = solver.getCache().getAnd(expressions);
    if (cached != null)
      return cached;

    if (expressions.isEmpty())
      return solver.falseExpr();

    List<STPExpr> noFalsesNoTrues = new ArrayList<STPExpr>(expressions.size());
    for (STPExpr expr : expressions){
      if (expr.equals(solver.falseExpr()))
        return solver.falseExpr();
      if (expr.equals(solver.trueExpr())){
        continue;
      }
      noFalsesNoTrues.add(expr);
    }
    if (noFalsesNoTrues.isEmpty())
      return solver.trueExpr();
    else if (noFalsesNoTrues.size() == 1)
      return noFalsesNoTrues.get(0);

    cached = solver.getCache().getAnd(noFalsesNoTrues);
    if (cached != null)
      return cached;

    AndExpr e = new AndExpr(noFalsesNoTrues, solver);
    solver.getCache().putAnd(expressions, e);
    solver.getCache().putAnd(noFalsesNoTrues, e);
    return e;
  }

  private AndExpr(List<STPExpr> exprs, STPSolver solver){
    super(STPExprKind.AndExpr, solver);
    assert exprs != null;
    this.exprs = exprs;
  }

  @Override
  public String toString(int indent){
    StringBuilder b = new StringBuilder();
    b.append(Utils.spaces(indent));
    b.append("AND(\n");
    for (Iterator<STPExpr> iter = exprs.iterator(); iter.hasNext();){
      STPExpr e = iter.next();
      b.append(e.toString(indent + "AND(".length()));
      if (iter.hasNext()){
        b.append(", \n");
      }
    }
    b.append("\n");
    b.append(Utils.spaces(indent) + ")");
    return b.toString();
  }

  @Override
  public Expr internalGetExpr(SolvingContext sc, int shift){
    Expr fal = getSolver().falseExpr().getExpr(sc, shift);
    Expr tru = getSolver().trueExpr().getExpr(sc, shift);
    List<Expr> exprList = STPExpr.exprList(sc, exprs, shift);
    getSolver().nativeSTPObjectCreationTimer.start();
    Expr and = STPExpressions.and(sc.getVC(), fal, tru, exprList);
    getSolver().nativeSTPObjectCreationTimer.stop();
    return and;
  }

  @Override
  public int size(){
    int size = 1;//for this node
    for (STPExpr expr : exprs){
      size += expr.size();
    }
    return size;
  }
}
