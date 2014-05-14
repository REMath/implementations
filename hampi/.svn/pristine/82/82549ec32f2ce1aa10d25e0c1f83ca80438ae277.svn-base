package stp.examples;
import junit.framework.TestCase;
import stp.*;
public class array_cvcl_02 extends TestCase{
public void test(){  
  VC vc = new VC();
  VC.setFlags('n');
  VC.setFlags('d');
  VC.setFlags('p');

  Expr cvcl_array = vc.varExpr1( "a",32,32);
  Expr i = vc.varExpr1( "i", 0, 8);   
  Expr i32 = vc.bvConcatExpr(
 			     vc.bvConstExprFromStr(
 						   "000000000000000000000000"),
 			     i); 
  Expr no_underflow = vc.bvLeExpr(
				  vc.bvConstExprFromInt( 32, 0),
				  i32);  
  Expr no_overflow = vc.bvLeExpr(
				 i32,
				 vc.bvConstExprFromInt( 32, 9));  
  Expr in_bounds = vc.andExpr( no_underflow, no_overflow);  
  Expr a_of_i = vc.bvSignExtend(
				vc.readExpr(cvcl_array,i32),
				32);  
  Expr a_of_i_eq_11 = vc.eqExpr( a_of_i,
				vc.bvConstExprFromInt( 32, 11));
 
  vc.assertFormula( in_bounds);
  vc.assertFormula( a_of_i_eq_11);  
  vc.query( vc.falseExpr());

  //long long v; 
  Expr pre = vc.bvConstExprFromInt(24,0);
  for(int j=0;j<10;j++) {
    Expr exprj = vc.bvConstExprFromInt(8,j);
    Expr index = vc.bvConcatExpr( pre, exprj);
    index = vc.simplify(index);
    Expr a_of_j = vc.readExpr( cvcl_array, index);
    Expr ce = vc.getCounterExample(a_of_j);    
  }

  //vc.printCounterExample();
}
}
