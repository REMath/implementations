package stp.examples.todo;

import stp.*;

public class regr_001 {
public static void main(String[] args) {  
  VC vc = new VC();
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
  
 
  Expr ct_100 = vc.bvConstExprFromInt( 32, 100);
  Expr a_of_1_sgt_100 = vc.sbvGtExpr( a_of_0, ct_100);

  /* Query 1 */  
  vc.push();
  int query = vc.query( a_of_1_sgt_100);
  vc.pop();
  System.out.printf("query = %d\n", query);

  vc.assertFormula( a_of_1_sgt_100);
  vc.printExpr( a_of_1_sgt_100);
  
  /* query(false) */
  vc.push();
  query = vc.query( vc.falseExpr());
  vc.pop();
  System.out.printf("query = %d\n", query);
  assert(query != 0);
  
  assert(vc.counterexample_size());
  
  int[] a_val = new int[];(int*) malloc(sizeof *a_val);
  char *p = (char*) a_val;
  //a_of_1 = vc.simplify( a_of_1);  // BUG here
  for (i=0; i<=3; i++) {
    Expr elem = vc.readExpr( a, vc.bvConstExprFromInt( 32, i));
    Expr ce = vc.getCounterExample( elem);
    unsigned long long v = getBVUnsigned(ce);
    fprintf(stderr, "a[%d] = %ld\n", i, v);
    *p = v; p++;
  }
  printf("a = %d\n", *a_val);
  assert(*a_val > 100);
}



