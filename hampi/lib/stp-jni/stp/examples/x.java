package stp.examples;

import junit.framework.TestCase;
import stp.*;
public class x extends TestCase{
public void test(){
  VC vc = new VC();
  VC.setFlags('n');
  VC.setFlags('d');
  VC.setFlags('p'); 
 
  Expr nresp1 = vc.varExpr("nresp1", vc.bv32Type());
  Expr packet_get_int0 = vc.varExpr("packet_get_int0", vc.bv32Type());
  Expr sz = vc.varExpr("sz", vc.bv32Type());
  Expr exprs[] = {
    // nresp1 == packet_get_int0
    vc.eqExpr(nresp1, packet_get_int0),
    
    // nresp1 > 0
    vc.bvGtExpr(nresp1, vc.bv32ConstExprFromInt(0)),
    
    // sz == nresp1 * 4
    vc.eqExpr(sz, vc.bv32MultExpr(nresp1, vc.bv32ConstExprFromInt(4))),
    
    // sz > nresp1 || sz < 0
    vc.orExpr(vc.sbvGeExpr(sz, nresp1), vc.sbvLtExpr(sz, vc.bv32ConstExprFromInt(0))),
  };
  
   Expr res = vc.andExprN(exprs);
  //vc_printExpr(vc, res);
  vc.query(res);
}

}
