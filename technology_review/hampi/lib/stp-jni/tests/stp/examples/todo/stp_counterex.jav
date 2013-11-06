package stp.examples.todo;
import stp.*;

public class stp_counterex {
public static void main(String[] args) {  
  VC vc = new VC();
  VC.setFlags('n');
  VC.setFlags('d');
  //VC.setFlags('p');
  
  Type bv8 = vc.bvType( 8);

  Expr a =  vc.bvCreateMemoryArray( "a");  
 
  Expr index_1 = vc.bvConstExprFromInt( 32, 1);
  Expr a_of_1 = vc.readExpr( a, index_1);  
 
  Expr ct_100 = vc.bvConstExprFromInt( 8, 100);
  Expr a_of_1_eq_100 = vc.eqExpr( a_of_1, ct_100);

  /* Query 1 */  
  vc.push();
  int query = vc.query( a_of_1_eq_100);
  vc.pop();
  System.out.printf("query = %d\n", query);

  vc.assertFormula( a_of_1_eq_100);
  
  /* query(false) */
  vc.push();
  query = vc.query( vc.falseExpr());
  vc.pop();
  System.out.printf("query = %d\n", query);
  
  if (vc.counterexample_size() == 0) {
    System.out.printf("Counterexample size is 0\n");
    System.exit(1);
  }
      
  a_of_1 = vc.simplify( a_of_1);  
  //vc.printExpr( a_of_1);
  Expr ce = vc.getCounterExample( a_of_1);
  unsigned long long v = getBVUnsigned(ce);
  
  System.err.printf("a[1] = %ld\n", v);
}
}
