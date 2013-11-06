package stp.examples;
import junit.framework.TestCase;
import stp.*;

public class vcdestroy_segfault extends TestCase{
public void test(){
  int r;
  VC vc = new VC();
  //  VC.setFlags ('n');
  VC.setFlags ('d');
  VC.setFlags ('p');

  // 32-bit variable
  Expr i = vc.varExpr1( "i", 0, 32);

  // 32-bit constant, value is 7.
  Expr c7 = vc.bvConstExprFromInt( 32, 7);

  // assert that both (i < 7) AND (i > 7) are true.
  Expr ilt7 = vc.bvLtExpr ( i, c7);
  Expr igt7 = vc.bvGtExpr ( i, c7);
  vc.assertFormula ( ilt7);
  vc.assertFormula ( igt7);

  // check if constraint set is satisifable.
  Expr falsee = vc.falseExpr();
  r = vc.query ( falsee);
  if (r == 0)
    System.out.printf ("cs is satisfiable\n");
  else
    System.out.printf ("cs is not satisfiable\n");

  i.DeleteExpr();
  c7.DeleteExpr();
  ilt7.DeleteExpr();
  igt7.DeleteExpr();
  falsee.DeleteExpr();
  vc.Destroy();

}
}
