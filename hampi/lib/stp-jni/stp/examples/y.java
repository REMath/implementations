package stp.examples;
import junit.framework.TestCase;
import stp.*;

public class y extends TestCase{
public void test(){
  VC vc = new VC();
  VC.setFlags('n');
  VC.setFlags('d');
  VC.setFlags('p');
  
  Expr nresp1 = vc.varExpr("nresp1", vc.bv32Type());
  Expr packet_get_int0 = vc.varExpr("packet_get_int0", vc.bv32Type());
  Expr exprs[] = {
    // nresp1 == packet_get_int0
    vc.eqExpr(nresp1, packet_get_int0),
    // nresp1 > 0
    vc.bvGtExpr(nresp1, vc.bv32ConstExprFromInt(0))
  };
  
  Expr res = vc.andExprN(exprs);
  vc.printExpr(res);
  
  int x = vc.query(res);
  System.out.printf("vc_query result = %d\n", x);
  vc.printCounterExample();
  
  Expr cex = vc.getCounterExample(res);
  //vc_printExpr(vc, cex);
}
}
