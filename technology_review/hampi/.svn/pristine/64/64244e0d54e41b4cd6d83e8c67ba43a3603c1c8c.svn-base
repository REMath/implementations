package hampi.stp;

import hampi.utils.Utils;

import java.util.*;

import stp.Expr;

/**
 * The logical OR expression.
 */
public final class OrExpr extends STPExpr{
  private final List<STPExpr> exprs;

  public static STPExpr create(STPSolver solver, STPExpr... exprs){
    return create(solver, Arrays.asList(exprs));
  }

  public static STPExpr create(STPSolver solver, List<STPExpr> expressions){
    STPExpr cached = solver.getCache().getOr(expressions);
    if (cached != null)
      return cached;

    if (expressions.isEmpty())
      return solver.falseExpr();

    List<STPExpr> noFalsesNoTrues = new ArrayList<STPExpr>(expressions.size());//this list contains no trues and no falses
    for (STPExpr expr : expressions){
      if (!expr.equals(solver.falseExpr())){
        noFalsesNoTrues.add(expr);
      }
      if (expr.equals(solver.trueExpr()))
        return solver.trueExpr();
    }
    if (noFalsesNoTrues.size() == 0)
      return solver.falseExpr();
    else if (noFalsesNoTrues.size() == 1)
      return noFalsesNoTrues.get(0);

    cached = solver.getCache().getOr(noFalsesNoTrues);
    if (cached != null)
      return cached;

    STPExpr e = new OrExpr(solver, noFalsesNoTrues);
    solver.getCache().putOr(expressions, e);
    solver.getCache().putOr(noFalsesNoTrues, e);
    return e;
  }

  private OrExpr(STPSolver solver, List<STPExpr> exprs){
    super(STPExprKind.OrExpr, solver);
    assert exprs != null;
    this.exprs = exprs;
  }

  @Override
  public String toString(int indent){
    StringBuilder b = new StringBuilder();
    b.append(Utils.spaces(indent));
    b.append("OR(\n");
    for (Iterator<STPExpr> iter = exprs.iterator(); iter.hasNext();){
      STPExpr e = iter.next();
      b.append(e.toString(indent + "OR(".length()));
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
    List<STPExpr> choose = sc.getChoiceGenerator().choose(exprs);
    List<Expr> exprList = STPExpr.exprList(sc, choose, shift);
    getSolver().nativeSTPObjectCreationTimer.start();
    Expr result = STPExpressions.or(sc.getVC(), fal, tru, exprList);
    getSolver().nativeSTPObjectCreationTimer.stop();
    return result;
  }

  public List<STPExpr> getSubexpressions(){
    return exprs;
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
