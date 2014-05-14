package hampi.parser;

import hampi.*;
import hampi.constraints.*;
import hampi.grammars.*;
import hampi.grammars.apps.GrammarStringBounder;
import hampi.utils.*;

import java.util.*;

import jpaul.Graphs.*;

/**
 * Converts the AST form the parser into a Hampi (core string) constraint.
 */
public final class HConstraintPreparer{

  private final Hampi hampi;
  private final int varSize;

  public HConstraintPreparer(Hampi hampi, int varSize){
    this.hampi = hampi;
    this.varSize = varSize;
  }

  /**
   * Converts ast to constraint. Assume ast is well-formed.
   */
  public Constraint prepare(HProgram ast){
    List<HStatement> asserts = ast.getStatements(HGrammarElementKind.STMT_ASSERT);

    List<Constraint> conjuncts = new ArrayList<Constraint>(asserts.size());
    for (HStatement assertStmt : asserts){
      Constraint p = prepare((HAssertStatement) assertStmt, ast);
      assert p != null : assertStmt;
      conjuncts.add(p);
    }
    return hampi.andConstraint(conjuncts);
  }

  private Constraint prepare(HAssertStatement asrt, HProgram ast){
    HBooleanExpression boolExpr = asrt.getBooleanExpression();
    switch (boolExpr.getKind()){
    case BEXPR_CONTAINS:
      return prepareContains((HContainsExpression) boolExpr, ast);
    case BEXPR_IN:
      return prepareIn((HInExpression) boolExpr, ast);
    case BEXPR_EQUALS:
      return prepareEquals((HEqualsExpression) boolExpr, ast);
    default:
      throw new IllegalStateException("invalid kind:" + asrt);
    }
  }

  private Constraint prepareEquals(HEqualsExpression equalExpr, HProgram ast){
    String leftId = equalExpr.getId1();
    String rightId = equalExpr.getId2();
    return hampi.equalsConstraint(getExpandedExpression(leftId, ast), equalExpr.equals(), getExpandedExpression(rightId, ast));
  }

  private Constraint prepareContains(HContainsExpression containsExpr, HProgram ast){
    String varName = containsExpr.getVariableName();
    String string = containsExpr.getString();
    Regexp sigma = getAlphabet(ast);
    Regexp sigmaStar = hampi.starRegexp(sigma);
    Regexp contains = hampi.concatRegexp(sigmaStar, hampi.constRegexp(string), sigmaStar);
    Expression varExpr = getExpandedExpression(varName, ast);
    return hampi.regexpConstraint(varExpr, containsExpr.contains(), contains);
  }

  /**
   * Creates an expression by inlining all var definitions (assumption is that
   * there are no cycles there.)
   */
  private Expression getExpandedExpression(String varName, HProgram ast){
    HStatement decl = ast.getDecl(varName);
    switch (decl.getKind()){
    case STMT_VALDECL: {
      HValDeclStatement val = (HValDeclStatement) decl;
      HExpression expression = val.getExpression();
      return getExpression(expression, ast);
    }
    case STMT_VARDECL: {
      HVarDeclStatement v = (HVarDeclStatement) decl;
      return hampi.varExpr(v.getVarName());
    }
    default:
      throw new IllegalStateException("invalid usage of variable reference " + varName + " \n" + ast);
    }
  }

  private Expression getExpression(HExpression expression, HProgram ast){
    switch (expression.getKind()){
    case EXPR_CONCAT: {
      HConcatExpression ce = (HConcatExpression) expression;
      List<Expression> exprs = new ArrayList<Expression>();
      for (HExpression subExpr : ce.getSubExpressions()){
        exprs.add(getExpression(subExpr, ast));
      }
      return hampi.concatExpr(exprs);
    }
    case EXPR_SUBSEQUENCE: {
      HSubsequenceExpression ce = (HSubsequenceExpression) expression;
      HStatement decl = ast.getDecl(ce.getName());
      switch (decl.getKind()){
      case STMT_VARDECL: {
        HVarDeclStatement v = (HVarDeclStatement) decl;
        return hampi.subsequenceExpr(hampi.varExpr(v.getVarName()), ce.getStartIndex(), ce.getLength());
      }
      default:
        throw new IllegalStateException("subsequence can only be used on var declaration " + ce.getName() + " \n" + ast);
      }
    }
    case EXPR_VAR: {
      HVarReferenceExpression var = (HVarReferenceExpression) expression;
      return getExpandedExpression(var.getName(), ast);
    }
    case EXPR_CONST: {
      HConstantExpression constEx = (HConstantExpression) expression;
      return hampi.constExpr(constEx.getValue());
    }
    default:
      throw new IllegalStateException("invalid expression in variable declaration: " + expression);
    }
  }

  //XXX hardwire
  private Regexp getAlphabet(HProgram ast){
    return hampi.rangeRegexp(ASCIITable.lowestChar, ASCIITable.highestChar);
  }

  /*
   * Processes expressions 'x in A'.
   * A must be either a regular variable,
   * or a context-free variable.
   * In the latter case, bound inference is required.
   */
  private Constraint prepareIn(HInExpression inExpr, HProgram ast){
    Expression exp = getExpandedExpression(inExpr.getVarName(), ast);
    String varName = inExpr.getRegVarName();
    HRegDeclStatement regDecl = ast.getRegDecl(varName);
    if (regDecl != null){
      //regular case
      Regexp reg = prepareRegForVar(varName, ast);
      assert reg != null : "null reg for " + inExpr.getRegVarName();
      return hampi.regexpConstraint(exp, inExpr.isIn(), reg);
    }else{
      //context-free case
      CFGStatement cfg = ast.getCFGDecl(varName);
      assert cfg != null : "null cfg for " + inExpr.getRegVarName();
      int boundSize = computeExpressionSize(exp, varSize);
      Regexp reg = prepareSizeFixRegexp(varName, boundSize, ast);
      return hampi.regexpConstraint(exp, inExpr.isIn(), reg);
    }
  }

  /*
   * Compute the length of the expression given the size of the string variable.
   */
  private int computeExpressionSize(Expression exp, int varSize){
    assert exp.getVariables().size() <= 1 : exp.getVariables().toString();//expect at most 1 var
    Solution solution= Solution.createSAT();
    if (!exp.getVariables().isEmpty()) {
      solution.setValue(exp.getVariables().iterator().next(), Utils.spaces(varSize));
    }
    return exp.getValue(solution).length();
  }

  private Regexp prepareRegForVar(String varName, HProgram ast){
    HRegDeclStatement regDecl = ast.getRegDecl(varName);
    HRegDefinition regexp = regDecl.getRegexp();
    return prepareRegexp(regexp, ast);
  }

  private Regexp prepareRegexp(HRegDefinition regexp, HProgram ast){
    switch (regexp.getKind()){
    case REG_CONST: {
      HConstRegexp cr = (HConstRegexp) regexp;
      return hampi.constRegexp(cr.getString());
    }
    case REG_FIX: {
      HSizeFixRegDefinition fix = (HSizeFixRegDefinition) regexp;
      return prepareSizeFixRegexp(fix, ast);
    }
    case REG_STAR: {
      HStarRegexp sr = (HStarRegexp) regexp;
      HRegDefinition subRegexp = sr.getSubRegexp();
      return hampi.starRegexp(prepareRegexp(subRegexp, ast));
    }
    case REG_RANGE: {
      HRangeRegexp range = (HRangeRegexp) regexp;
      return hampi.rangeRegexp(range.getLow(), range.getHigh());
    }
    case REG_CONCAT: {
      HConcatRegexp concat = (HConcatRegexp) regexp;
      return hampi.concatRegexp(prepareRegexps(concat.getExpressions(), ast));
    }
    case REG_OR: {
      HOrRegexp or = (HOrRegexp) regexp;
      return hampi.orRegexp(prepareRegexps(or.getExpressions(), ast));
    }
    case REG_VAR: {
      HRegVarRef var = (HRegVarRef) regexp;
      return prepareRegForVar(var.getName(), ast);
    }
    default:
      throw new IllegalStateException(regexp.toString());
    }
  }

  private List<Regexp> prepareRegexps(List<HRegDefinition> expressions, HProgram ast){
    List<Regexp> res = new ArrayList<Regexp>(expressions.size());
    for (HRegDefinition regDefinition : expressions){
      res.add(prepareRegexp(regDefinition, ast));
    }
    return res;
  }

  /*
   * Creates the regular expression that describes
   * all strings of given size in the CFG.
   */
  private Regexp prepareSizeFixRegexp(HSizeFixRegDefinition fix, HProgram ast){
    return prepareSizeFixRegexp(fix.getNonterminal(), fix.getSize(), ast);
  }

  /*
   * Creates the regular expression that describes
   * all strings of given size in the CFG.
   */
  private Regexp prepareSizeFixRegexp(String cfg, int size, HProgram ast){
    Grammar g = extractGrammar(cfg, ast);
    StopWatch w = new StopWatch("grammar bounding for " + cfg);
    w.start();
    GrammarStringBounder gsb = new GrammarStringBounder();
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, cfg, size, false);
    w.stop();
    System.out.println(w);
    if (boundedRegexp == null)
      throw HampiResultException.unsat();
    return boundedRegexp;
  }

  /**
   * Converts the CFG from the front-end format to the internal format.<br>
   * TODO revisit whether this 2-format story could be simplified.
   */
  private Grammar extractGrammar(String nonterminal, HProgram ast){
    Set<String> reachableNonterminals = reachableNonterminals(nonterminal, ast);
    Set<CFGStatement> cfgDecl = ast.getCFGDecls(reachableNonterminals);
    Grammar grammar = new Grammar();
    for (CFGStatement stmt : cfgDecl){
      grammar.addRule(extractRule(stmt, ast, grammar));
    }
    return grammar;
  }

  private GrammarRule extractRule(CFGStatement stmt, HProgram ast, Grammar grammar){
    List<List<CFGProductionElement>> elemSets = stmt.getElementSets();
    GrammarRule rule = new GrammarRule();
    for (List<CFGProductionElement> elems : elemSets){
      rule.addProduction(extractProduction(rule, elems, ast, grammar));
    }
    rule.setNonterminal(new NonterminalElement(stmt.getVarName(), grammar));
    return rule;
  }

  private GrammarProduction extractProduction(GrammarRule rule, List<CFGProductionElement> elems, HProgram ast, Grammar grammar){
    GrammarProduction gp = new GrammarProduction(rule);
    for (CFGProductionElement elem : elems){
      GrammarProductionElement element = extractProductionElement(elem, ast, grammar);
      gp.addElement(element);
    }
    return gp;
  }

  private final Set<String> newNonterminals = new LinkedHashSet<String>();

  private GrammarProductionElement extractProductionElement(CFGProductionElement elem, HProgram ast, Grammar grammar){
    switch (elem.getKind()){
    case CFG_CHAR_RANGE: {
      //the other model does not have ranges or OR so we introduce a new nonterminal and expand the range
      CFGCharRange range = (CFGCharRange) elem;
      String name = "range" + range.getLow() + "_" + range.getHigh();
      NonterminalElement newNt = new NonterminalElement(name, grammar);
      if (!newNonterminals.contains(name)){
        newNonterminals.add(name);
        GrammarRule newRule = new GrammarRule();
        newRule.setNonterminal(newNt);
        for (char c : range.getChars()){
          GrammarProduction p = new GrammarProduction(newRule);
          p.addElement(new TerminalElement("\"" + String.valueOf(c) + "\"", grammar));
          newRule.addProduction(p);
        }
        grammar.addRule(newRule);
      }
      return newNt;
    }
    case CFG_NONTERMINAL: {
      CFGNonterminal nt = (CFGNonterminal) elem;
      return new NonterminalElement(nt.getName(), grammar);
    }
    case CFG_OPTION: {
      CFGOption opt = (CFGOption) elem;
      List<GrammarProductionElement> elems = new ArrayList<GrammarProductionElement>(1);
      elems.add(extractProductionElement(opt.getSubelement(), ast, grammar));
      return new OptionElement(elems, grammar);
    }
    case CFG_PLUS: {
      CFGPlus plus = (CFGPlus) elem;
      List<GrammarProductionElement> elems = new ArrayList<GrammarProductionElement>(1);
      elems.add(extractProductionElement(plus.getSubelement(), ast, grammar));
      return new PlusElement(elems, grammar);
    }
    case CFG_STAR: {
      CFGStar star = (CFGStar) elem;
      List<GrammarProductionElement> elems = new ArrayList<GrammarProductionElement>(1);
      elems.add(extractProductionElement(star.getSubelement(), ast, grammar));
      return new StarElement(elems, grammar);
    }
    case CFG_TERMINAL: {
      CFGTerminal term = (CFGTerminal) elem;
      return new TerminalElement(term.getText(), grammar);
    }
    default:
      throw new IllegalStateException("unknown kind " + elem);
    }
  }

  private Set<String> reachableNonterminals(String nonterminal, final HProgram ast){
    DiGraph<String> graph = new DiGraph<String>(){
      @Override
      public Collection<String> getRoots(){
        List<HStatement> statements = ast.getStatements(HGrammarElementKind.STMT_CFG);
        List<String> l = new ArrayList<String>(statements.size());
        for (HStatement statement : statements){
          l.add(((CFGStatement) statement).getVarName());
        }
        return l;
      }

      @Override
      public ForwardNavigator<String> getForwardNavigator(){
        return new ForwardNavigator<String>(){

          @Override
          public List<String> next(String vertex){
            CFGStatement decl = ast.getCFGDecls(Collections.singleton(vertex)).iterator().next();
            final List<String> res = new ArrayList<String>();
            for (List<CFGProductionElement> elemSet : decl.getElementSets()){
              for (CFGProductionElement elem : elemSet){
                elem.accept(new HGrammarVisitor(){
                  @Override
                  public void visitCFGNonterminal(CFGNonterminal nonterminal){
                    res.add(nonterminal.getName());
                  }
                });
              }
            }
            return res;
          }

        };
      }
    };
    return graph.transitiveSucc(nonterminal);
  }

}
