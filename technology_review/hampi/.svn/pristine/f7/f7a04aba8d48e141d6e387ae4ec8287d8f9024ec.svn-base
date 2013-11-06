package stp.examples;
import junit.framework.TestCase;
import stp.*;

public class push_pop_1 extends TestCase{
public void test() {
  VC vc = new VC();
  VC.setFlags('n');
  VC.setFlags('d');
  VC.setFlags('p');
  VC.setFlags('v');
  VC.setFlags('s');
  VC.setFlags('c');
  vc.push();

  Type bv8 = vc.bvType( 8);

  Expr a = vc.varExpr( "a", bv8);
  Expr ct_0 = vc.bvConstExprFromInt( 8, 0);

  Expr a_eq_0 = vc.eqExpr( a, ct_0);

  int query;
  //query = vc.query( a_eq_0);
  //printf("query = %d\n", query);

  Expr a_neq_0 = vc.notExpr(a_eq_0);
  vc.assertFormula(a_eq_0);
  vc.printAsserts(false);
  vc.push();

  Expr queryexp = vc.eqExpr( a, vc.bvConstExprFromInt( 8, 0));
  vc.printExpr( queryexp);
  
  query = vc.query( queryexp);
  vc.printCounterExample();
  vc.pop();
  vc.pop();

  System.out.printf("query = %d\n", query);
}
}
