package hampi.tests;

import hampi.*;
import hampi.constraints.*;
import hampi.grammars.Grammar;
import hampi.grammars.apps.GrammarStringBounder;
import hampi.grammars.parser.Parser;
import hampi.stp.STPSolver;
import hampi.tests.gramgren.GrammarTests;

import java.util.*;

import junit.framework.TestCase;

public class SolverBenchmarks extends TestCase{
  private STPSolver stp(){
    return new STPSolver();
  }

  private List<Regexp> charRegexp(Set<Character> alpha, Hampi h){
    List<Regexp> result = new ArrayList<Regexp>();
    for (char ch : alpha){
      result.add(h.constRegexp(ch));
    }
    return result;
  }

  public void testGrammarBound5() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "tiny_SQL.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 21;
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "UpdateStmt", bound, false);
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));

    Expression query = h.concatExpr(h.constExpr("UPDATE c SET"), h.varExpr("v"));
    Constraint rc = h.regexpConstraint(query, true, boundedRegexp);
    Regexp expr1 = h.concatRegexp(sigmaStar, h.constRegexp("'1'='1'"), sigmaStar);
    Constraint rc1 = h.regexpConstraint(query, true, expr1);
    Constraint c = h.andConstraint(rc, rc1);
    //        System.out.println(c);
    Solution solve = h.solve(c, 10);
    assertTrue(solve.isSatisfiable());
    System.out.println(solve);
  }

  public void testGrammarBound6() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "tiny_SQL.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 21;
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "UpdateStmt", bound, false);
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Expression query = h.concatExpr(h.constExpr("UPDATE c SET w='"), h.varExpr("v"), h.constExpr("'"));
    Constraint rc1 = h.regexpConstraint(query, true, boundedRegexp);
    Regexp badnessRE = h.concatRegexp(sigmaStar, h.constRegexp("'1'='1'"), sigmaStar);
    Constraint rc2 = h.regexpConstraint(query, true, badnessRE);
    Constraint c = h.andConstraint(rc1, rc2);
    //        System.out.println(c);
    Solution solve = h.solve(c, 10);
    assertTrue(solve.isSatisfiable());
    System.out.println(solve);
  }

  public void testGrammarBound7_comment() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "tiny_SQL.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 20;
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "S", bound, false);
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Expression query = h.concatExpr(h.constExpr("UPDATE c SET w='"), h.varExpr("v"), h.constExpr("'"));
    Constraint rc1 = h.regexpConstraint(query, true, boundedRegexp);
    Regexp badnessRE = h.concatRegexp(sigmaStar, h.constRegexp("foo bar"), sigmaStar);//enforces a comment
    Constraint rc2 = h.regexpConstraint(query, true, badnessRE);
    Constraint c = h.andConstraint(rc1, rc2);
    //        System.out.println(c);
    Solution solve = h.solve(c, 10);
    assertTrue(solve.isSatisfiable());
    System.out.println(solve);
  }

  public void testGrammarBound8_comment() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "tiny_SQL.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 21;
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "S", bound, false);
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Expression query = h.concatExpr(h.constExpr("UPDATE"), h.varExpr("v"), h.constExpr("'"));
    Constraint rc1 = h.regexpConstraint(query, true, boundedRegexp);
    Regexp badnessRE = h.concatRegexp(sigmaStar, h.constRegexp("SELECT *"), sigmaStar);//enforces comment
    Constraint rc2 = h.regexpConstraint(query, true, badnessRE);
    Constraint c = h.andConstraint(rc1, rc2);
    Solution solve = h.solve(c, 10);
    assertTrue(solve.isSatisfiable());
    System.out.println(solve);
  }

  public void testGrammarBound9() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "tiny_SQL.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 40;
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "SelectStmt", bound, false);
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Expression query = h.concatExpr(h.constExpr("SELECT * FROM Faq WHERE context = '"), h.varExpr("v"), h.constExpr("'"));
    Constraint rc1 = h.regexpConstraint(query, true, boundedRegexp);
    Regexp badnessRE = h.concatRegexp(sigmaStar, h.constRegexp("'1'='1'"), sigmaStar);//enforces comment
    Constraint rc2 = h.regexpConstraint(query, true, badnessRE);
    Constraint c = h.andConstraint(rc1, rc2);
    Solution solve = h.solve(c, 10);
    assertTrue(solve.isSatisfiable());
    System.out.println(solve);
  }

  /**
   * UPDATE m SET n=' VAR ', D='1' in SQL^N<br>
   * UPDATE m SET n=' VAR ', D='1' in Sigma* '1'='1' Sigma*<br>
   * Intended solution:<br>
   * UPDATE m SET n='1' WHERE '1'='1'--', D='1' (length 30 tokens)<br>
   * VAR=1' WHERE '1'='1'-- (length 18 chars)<br>
   * <br>
   * NOTE: out of memory
   */
  public void testGrammarBound10() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "tiny_SQL.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 30;
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "S", bound, false);

    assertTrue(boundedRegexp.matches("UPDATE m SET n='1' WHERE '1'='1'--', D='1'"));//make sure the intended solution works
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Expression query = h.concatExpr(h.constExpr("UPDATE m SET n='"), h.varExpr("v"), h.constExpr("', D='1'"));
    Constraint rc1 = h.regexpConstraint(query, true, boundedRegexp);
    Regexp badnessRE = h.concatRegexp(sigmaStar, h.constRegexp("'1'='1'"), sigmaStar);//enforces comment
    Constraint rc2 = h.regexpConstraint(query, true, badnessRE);
    Constraint c = h.andConstraint(rc1, rc2);
    Solution solve = h.solve(c, 10);
    assertTrue(solve.isSatisfiable());
    System.out.println(solve);
  }

  /**
   * The real version of test 10
   *
   * Query = UPDATE MembersMain SET Name = ' VAR ', Division = '1', RankCorp =
   * '1', Vacation = '1', Comment = '1', LastUpdate = Now(), Deleted = '1' WHERE
   * MemberID = '1'<br>
   *
   * Query contains '1'='1'<br>
   *
   * Intended solution:<br>
   * Query = UPDATE MembersMain SET Name = '1' WHERE '1'='1'--', Division = '1',
   * RankCorp = '1', Vacation = '1', Comment = '1', LastUpdate = Now(), Deleted
   * = '1' WHERE MemberID = '1'<br>
   *
   * VAR=1' WHERE '1'='1'-- (length 18 chars)<br>
   * <br>
   * NOTE: way out of memory
   */
  public void testGrammarBound11() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "tiny_SQL.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 110; //at least
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "S", bound, false);

    assertTrue(boundedRegexp
        .matches("UPDATE MembersMain SET Name = '1' WHERE '1'='1'--', Division = '1', RankCorp = '1', Vacation = '1', Comment = '1', LastUpdate = Now(), Deleted = '1' WHERE MemberID = '1'"));//make sure the intended solution works
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Expression query = h.concatExpr(h.constExpr("UPDATE m SET n='"), h.varExpr("v"), h.constExpr("', D='1'"));
    Constraint rc1 = h.regexpConstraint(query, true, boundedRegexp);
    Regexp badnessRE = h.concatRegexp(sigmaStar, h.constRegexp("'1'='1'"), sigmaStar);//enforces comment
    Constraint rc2 = h.regexpConstraint(query, true, badnessRE);
    Constraint c = h.andConstraint(rc1, rc2);
    Solution solve = h.solve(c, 10);
    assertTrue(solve.isSatisfiable());
    System.out.println(solve);
  }

  /**
   * Query = SELECT MemberID, Name, Division, DateJoined, RankCorp, Vacation,
   * Comment, Deleted FROM MembersMain WHERE MemberID=' VAR '<br>
   *
   * Query contains '1'='1'<br>
   *
   * Intended Solution <br>
   * Query = SELECT MemberID, Name, Division, DateJoined, RankCorp, Vacation,
   * Comment, Deleted FROM MembersMain WHERE MemberID='1' OR '1'='1'<br>
   * <br>
   * VAR = 1' OR '1'='1<br>
   */
  public void testGrammarBound12() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "tiny_SQL.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 110; //at least
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "S", bound, false);

    assertTrue(boundedRegexp
        .matches("SELECT MemberID, Name, Division, DateJoined, RankCorp, Vacation, Comment, Deleted FROM MembersMain WHERE MemberID='1' OR '1'='1'"));//make sure the intended solution works
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Expression prefix = h.constExpr("SELECT MemberID, Name, Division, DateJoined, RankCorp, Vacation, Comment, Deleted FROM MembersMain WHERE MemberID='");
    Expression query = h.concatExpr(prefix, h.varExpr("v"), h.constExpr("'"));
    Constraint rc1 = h.regexpConstraint(query, true, boundedRegexp);
    Regexp badnessRE = h.concatRegexp(sigmaStar, h.constRegexp("'1'='1'"), sigmaStar);
    Constraint rc2 = h.regexpConstraint(query, true, badnessRE);
    Constraint c = h.andConstraint(rc1, rc2);
    Solution solve = h.solve(c, 10);
    assertTrue(solve.isSatisfiable());
    System.out.println(solve);
  }

  /**
   * Small version of test 12 <br>
   * Query = SELECT M FROM m WHERE d=' VAR '<br>
   * Query contains '1'='1'<br>
   *
   * Intended Solution <br>
   * Query = SELECT M FROM m WHERE d='1' OR '1'='1' (25 tokens)<br>
   * <br>
   * VAR = 1' OR '1'='1 (length 12 chars)<br>
   */
  public void testGrammarBound12_small() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "tiny_SQL.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 25;
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "SelectStmt", bound, false);

    assertTrue(boundedRegexp.matches("SELECT M FROM m WHERE d='1' OR '1'='1'"));//make sure the intended solution works
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Expression prefix = h.constExpr("SELECT M FROM m WHERE d='");
    Expression query = h.concatExpr(prefix, h.varExpr("v"), h.constExpr("'"));
    Constraint rc1 = h.regexpConstraint(query, true, boundedRegexp);
    Regexp badnessRE = h.concatRegexp(sigmaStar, h.constRegexp("'1'='1'"), sigmaStar);
    Constraint rc2 = h.regexpConstraint(query, true, badnessRE);
    Constraint c = h.andConstraint(rc1, rc2);
    Solution solve = h.solve(c, 10);
    assertTrue(solve.isSatisfiable());
    System.out.println(solve);
  }

  /*
   * Query = UPDATE MembersMain SET Vacation = ' VAR ' WHERE Name = '1'<br>
   * Query contains '1'='1'<br>
   *
   *Intended solution:
   * Query = UPDATE MembersMain SET Vacation = 'x' WHERE '1'='1'--' WHERE Name = '1' (length 56 tokens)
   * VAR = x' WHERE '1'='1'-- (length 18 chars)
   */
  public void testGrammarBound13() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "tiny_SQL.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 56;
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "SelectStmt", bound, false);

    assertTrue(boundedRegexp.matches("SELECT M FROM m WHERE d='1' OR '1'='1'"));//make sure the intended solution works
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Expression prefix = h.constExpr("SELECT M FROM m WHERE d='");
    Expression query = h.concatExpr(prefix, h.varExpr("v"), h.constExpr("'"));
    Constraint rc1 = h.regexpConstraint(query, true, boundedRegexp);
    Regexp badnessRE = h.concatRegexp(sigmaStar, h.constRegexp("'1'='1'"), sigmaStar);
    Constraint rc2 = h.regexpConstraint(query, true, badnessRE);
    Constraint c = h.andConstraint(rc1, rc2);
    Solution solve = h.solve(c, 10);
    assertTrue(solve.isSatisfiable());
    System.out.println(solve);
  }

}
