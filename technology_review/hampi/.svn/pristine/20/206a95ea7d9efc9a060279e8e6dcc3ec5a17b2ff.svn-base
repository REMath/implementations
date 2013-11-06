package hampi.tests.stp;

import junit.framework.TestCase;
import stp.*;

public class STPExamples extends TestCase{
  public void testSimple() throws Exception{
    VC vc = new VC();
    VC.setFlags('n');
    VC.setFlags('d');
    VC.setFlags('p');

    Expr bv = vc.varExpr("concat", vc.bvType(32));
    Expr sub = vc.bvExtract(bv, 31, 0);
    System.out.println("sub:" + sub);
    Expr eq = vc.eqExpr(sub, vc.bvConstExprFromInt(32, 97));
    System.out.println(eq);

    vc.assertFormula(eq);
    int query = vc.query(vc.falseExpr());
    if (query == 0){
      vc.printCounterExample();
    }
  }

  public void test0(){
    VC vc = new VC();
    VC.setFlags('n');
    VC.setFlags('d');
    VC.setFlags('p');

    Expr bv = vc.varExpr("at", vc.bvType(100000));
    System.out.println("at:" + bv);
    Expr sub = vc.bvExtract(bv, 4, 2);
    System.out.println("sub:" + sub);
    Expr concat = vc.bvConcatExpr(sub, vc.bvConstExprFromInt(3, 7));
    Expr gt = vc.bvLeExpr(concat, vc.bvConstExprFromInt(6, (2 << 6) - 1));
    System.out.println(gt);

    Expr eq = vc.bvGeExpr(sub, vc.bvConstExprFromInt(3, 7));
    System.out.println(eq);

    vc.assertFormula(gt);
    vc.assertFormula(eq);
    vc.query(vc.falseExpr());

  }

  public void test1(){
    VC vc = new VC();
    VC.setFlags('n');
    VC.setFlags('d');
    VC.setFlags('p');

    Expr cvcl_array = vc.varExpr1("a", 32, 32);
    //    System.out.println(cvcl_array);
    Expr i = vc.varExpr1("i", 0, 8);
    Expr i32 = vc.bvConcatExpr(vc.bvConstExprFromStr("000000000000000000000000"), i);
    Expr no_underflow = vc.bvLeExpr(vc.bvConstExprFromInt(32, 0), i32);
    Expr no_overflow = vc.bvLeExpr(i32, vc.bvConstExprFromInt(32, 9));
    Expr in_bounds = vc.andExpr(no_underflow, no_overflow);
    Expr readExpr = vc.readExpr(cvcl_array, i32);
    System.out.println("read expr:" + readExpr);
    Expr a_of_i = vc.bvSignExtend(readExpr, 32);
    System.out.println("a of i: " + a_of_i);
    Expr a_of_i_eq_11 = vc.eqExpr(a_of_i, vc.bvConstExprFromInt(32, 11));

    //    System.out.println(a_of_i_eq_11);
    vc.assertFormula(in_bounds);
    vc.assertFormula(a_of_i_eq_11);
    vc.query(vc.falseExpr());

    //long long v; 
    Expr pre = vc.bvConstExprFromInt(24, 0);
    for (int j = 0; j < 10; j++){
      Expr exprj = vc.bvConstExprFromInt(8, j);
      Expr index = vc.bvConcatExpr(pre, exprj);
      index = vc.simplify(index);
      Expr a_of_j = vc.readExpr(cvcl_array, index);
      Expr ce = vc.getCounterExample(a_of_j);
    }
  }
}
