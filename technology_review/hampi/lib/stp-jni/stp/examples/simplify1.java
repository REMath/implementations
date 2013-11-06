package stp.examples;
import junit.framework.TestCase;
import stp.*;

public class simplify1 extends TestCase{
public void test(){
  for(int j=0;j < 3; j++) {
    VC vc = new VC();
    VC.setFlags('n');
    VC.setFlags('d');
    VC.setFlags('p');
    VC.setFlags('x');
    
    Type bv8 = vc.bvType( 8);
    Expr a =  vc.bvCreateMemoryArray( "a");
    Expr index_3 = vc.bvConstExprFromInt( 32, 3);
    Expr a_of_0 = vc.readExpr( a, index_3);
  int i;
  for (i = 2; i >= 0; i--)
    a_of_0 = vc.bvConcatExpr(
			     a_of_0,
			     vc.readExpr( a,
					 vc.bvConstExprFromInt( 32, i)));
  Expr cast_32_to_8 = vc.bvExtract( a_of_0, 7, 0);
  Expr cast_8_to_32 = vc.bvSignExtend( cast_32_to_8, 32);
  vc.printExpr( cast_8_to_32);
  cast_8_to_32 = vc.simplify( cast_8_to_32);
  vc.Destroy();
  }
}
}
