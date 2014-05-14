package stp.examples;

import junit.framework.TestCase;
import stp.Expr;
import stp.VC;

public class print extends TestCase{
    public void test(){
        VC vc = new VC();

        VC.setFlags('n');
        VC.setFlags('d');
        VC.setFlags('p');

        Expr ct_3 = vc.bvConstExprFromStr("00000000000000000000000000000011");

        vc.printExpr(ct_3); System.out.printf("\n");

        ct_3 = vc.bvConstExprFromInt(32, 5);

        vc.printExpr(ct_3);   System.out.printf("\n");
    }

}