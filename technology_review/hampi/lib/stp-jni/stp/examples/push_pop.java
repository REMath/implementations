/* g++ -I$(HOME)/stp/c_interface push-pop.c -L$(HOME)/lib -lstp -o cc*/

package stp.examples;
import junit.framework.TestCase;
import stp.*;

public class push_pop extends TestCase{
public void test(){
  VC vc = new VC();
  VC.setFlags('n');
  VC.setFlags('d');
  VC.setFlags('p');
  //VC.setFlags('v');
  //VC.setFlags('s');

  Type bv8 = vc.bvType( 8);

  Expr a = vc.varExpr( "a", bv8);
  Expr ct_0 = vc.bvConstExprFromInt( 8, 0);

  Expr a_eq_0 = vc.eqExpr( a, ct_0);

  int query = vc.query( a_eq_0);
  System.out.printf("query = %d\n", query);

  vc.push();
  query = vc.query( a_eq_0);
  vc.pop();

  System.out.printf("query = %d\n", query);
}
}
