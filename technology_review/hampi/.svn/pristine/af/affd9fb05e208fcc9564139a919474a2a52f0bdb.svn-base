package stp.examples;

import junit.framework.TestCase;
import stp.Expr;
import stp.Type;
import stp.VC;

public class multiple_queries extends TestCase{
    public void test() {

        VC vc = new VC();

        VC.setFlags('n');
        VC.setFlags('c');
        VC.setFlags('d');
        VC.setFlags('p');

        Type bv8 = vc.bvType(8);
        Expr a = vc.varExpr("a", bv8);
        Expr ct_0 = vc.bvConstExprFromInt(8, 0);
        Expr a_eq_0 = vc.eqExpr(a, ct_0);

        // /* Query 1 */
        vc.push();

//        vc.printQuery();
        System.out.println("\nChecking:" + a_eq_0);
        int query = vc.query(a_eq_0);
        vc.printQuery();

        vc.pop();

//        System.out.printf("query = %d\n", query);

        // /* Query 2 */
        Expr a_neq_0 = vc.notExpr(a_eq_0);

        vc.push();

        System.out.println("\nChecking:" + a_neq_0);
        query = vc.query(a_neq_0);

        vc.pop();

//        System.out.printf("query = %d\n", query);
    }

}
