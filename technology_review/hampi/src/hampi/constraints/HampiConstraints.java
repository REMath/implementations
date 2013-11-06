package hampi.constraints;

import java.util.List;

/**
 * A facade for constraints.
 */
public final class HampiConstraints{

  public static Constraint andConstraint(Constraint... constraints){
    if (constraints.length == 1)
      return constraints[0];
    return new AndConstraint(constraints);
  }

  public static Constraint andConstraint(List<Constraint> conjuncts){
    if (conjuncts.size() == 1)
      return conjuncts.get(0);
    return new AndConstraint(conjuncts);
  }

  public static Expression concatExpr(Expression... exprs){
    if (exprs.length == 1)
      return exprs[0];
    return new ConcatExpression(exprs);
  }

  public static Expression concatExpr(List<Expression> exprs){
    if (exprs.size() == 1)
      return exprs.get(0);
    return new ConcatExpression(exprs);
  }

  public static Regexp concatRegexp(List<Regexp> exps){
    if (exps.size() == 1)
      return exps.get(0);
    return new ConcatRegexp(exps);
  }

  public static Regexp concatRegexp(Regexp... exps){
    if (exps.length == 1)
      return exps[0];
    return new ConcatRegexp(exps);
  }

  public static Expression constExpr(String value){
    return new ConstantExpression(value);
  }

  public static Regexp constRegexp(String str){
    return new ConstRegexp(str);
  }

  public static Regexp orRegexp(Regexp... exps){
    if (exps.length == 1)
      return exps[0];
    return new OrRegexp(exps);
  }

  public static Regexp plusRegexp(Regexp r){
    return concatRegexp(r, starRegexp(r));
  }

  public static Regexp rangeRegexp(char c, char d){
    if (c == d)
      return constRegexp(String.valueOf(c));
    return new OrRegexp(ConstRegexp.createRange(c, d));
  }

  public static Constraint regexpConstraint(Expression e1, boolean member, Regexp e2){
    return new RegexpConstraint(e1, member, e2);
  }

  public static Regexp starRegexp(Regexp r){
    if (r.getKind() == ElementKind.STAR_REGEXP)
      return r;
    return new StarRegexp(r);
  }

  public static VariableExpression varExpr(String name){
    return new VariableExpression(name);
  }

  public static SubsequenceExpression subsequenceExpr(VariableExpression expr, int fromIndex, int len){
    return new SubsequenceExpression(expr, fromIndex, len);
  }

  public static Constraint equalsConstraint(Expression e1, boolean equals, Expression e2){
    return new EqualsConstraint(e1, equals, e2);
  }

}
