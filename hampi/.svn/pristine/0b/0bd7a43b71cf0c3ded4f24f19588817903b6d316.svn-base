package stp.examples.todo;
import stp.*;

public class stp_dvi_001{
public static void main(String[] args) {  
  VC vc = vc.createValidityChecker();
  VC.setFlags('n');
  VC.setFlags('d');
  //VC.setFlags('p');
  
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
  
 
  Expr ct_5 = vc.bvConstExprFromInt( 32, 5);
  Expr a_of_0_div_5 = vc.bvDivExpr( 32, a_of_0, ct_5);
  
  Expr a_of_0_div_5_eq_5 = vc.eqExpr( a_of_0_div_5, ct_5);
  vc.printExpr( a_of_0_div_5_eq_5); System.out.printf("\n");
  
  /* Query 1 */
  vc.push();
  int query = vc.query( a_of_0_div_5_eq_5);
  vc.pop();
  System.out.printf("query = %d\n", query);

  vc.assertFormula( a_of_0_div_5_eq_5);
  vc.printExpr( a_of_0_div_5_eq_5);
  
  /* query(false) */
  vc.push();
  query = vc.query( vc.falseExpr());
  vc.pop();
  System.out.printf("query = %d\n", query);
  assert(query == 0);
  
  assert(vc.counterexample_size() != 0);
  
  int* a_val = (int*) malloc(sizeof *a_val);
  char *p = (char*) a_val;
  //a_of_1 = vc.simplify( a_of_1);  // BUG here
  for (i=0; i<=3; i++) {
    Expr elem = vc.readExpr( a, vc.bvConstExprFromInt( 32, i));
    Expr ce = vc.getCounterExample( elem);
    unsigned long long v = getBVUnsigned(ce);
    System.err.printf("a[%d] = %ld\n", i, v);
    *p = v; p++;
  }
  System.out.printf("a = %d\n", *a_val);
  assert((*a_val)/5  == 5);
}
}
