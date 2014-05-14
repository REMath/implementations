package hampi.stp;

import java.util.*;

import stp.*;

public final class STPExpressions{

  private STPExpressions(){
    throw new IllegalStateException("no instances");
  }

  /**
   * Creates an or expression and makes trivial simplifications.
   */
  public static Expr or(VC vc, Expr f, Expr t, Expr[] children){
    return or(vc, f, t, Arrays.asList(children));
  }

  /**
   * Creates an or expression and makes trivial simplifications.
   */
  public static Expr or(VC vc, Expr f, Expr t, List<Expr> children){
    if (children.isEmpty())
      return f;

    List<Expr> noFalsesNoTrues = new ArrayList<Expr>(children.size());//this list contains no trues and no falses
    for (Expr expr : children){
      if (expr != f){
        noFalsesNoTrues.add(expr);
      }
      if (expr == t)
        return t;
    }
    if (noFalsesNoTrues.size() == 0)
      return f;
    else if (noFalsesNoTrues.size() == 1)
      return noFalsesNoTrues.get(0);
    else{
      Expr[] arr = noFalsesNoTrues.toArray(new Expr[noFalsesNoTrues.size()]);
      return vc.orExprN(arr);

    }
  }

  /**
   * Creates an and expression and makes trivial simplifications.
   */
  public static Expr and(VC vc, Expr falseExpr, Expr trueExpr, Expr e1, Expr e2){
    if (e1 == falseExpr || e2 == falseExpr)
      return falseExpr;
    else if (e1 == trueExpr)
      return e2;
    else if (e2 == trueExpr)
      return e1;
    else
      return vc.andExpr(e1, e2);
  }

  /**
   * Creates an and expression and makes trivial simplifications.
   */
  public static Expr and(VC vc, Expr f, Expr t, Expr... expressions){
    return and(vc, f, t, Arrays.asList(expressions));
  }

  /**
   * Creates an and expression and makes trivial simplifications.
   */
  public static Expr and(VC vc, Expr f, Expr t, List<Expr> expressions){
    if (expressions.isEmpty())
      return f;

    List<Expr> noFalsesNoTrues = new ArrayList<Expr>(expressions.size());
    for (Expr expr : expressions){
      if (expr == f)
        return f;
      if (expr == t){
        continue;
      }
      noFalsesNoTrues.add(expr);
    }
    if (noFalsesNoTrues.isEmpty())
      return t;
    else if (noFalsesNoTrues.size() == 1)
      return noFalsesNoTrues.get(0);
    Expr[] children = noFalsesNoTrues.toArray(new Expr[noFalsesNoTrues.size()]);
    return vc.andExprN(children);
  }
}
