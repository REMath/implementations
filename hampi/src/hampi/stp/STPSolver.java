package hampi.stp;

import static java.lang.Math.*;
import hampi.*;
import hampi.constraints.*;
import hampi.utils.*;

import java.util.*;

import stp.*;

/**
 * A string solver implemented using the STP prover.
 */
public class STPSolver extends AbstractSolver{

  /**
   * Flag to control the 'split-top-level-ors' optimization.
   */
  private static final boolean OPT_TOP_DISJ_SPLIT = true;

  /**
   * If true, Hampi calls STP separately for each conjuction, otherwise Hampi
   * puts all conjunctions in 1 STP formula with disjunction.
   * XXX this is not fully implemented yet.
   */
  public static final boolean INCREMENTAL = false;

  public final StopWatch shiftingTimer = new StopWatch("shifting");
  private final StopWatch distroTimer = new StopWatch("distro");
  private final StopWatch nativeEncodingTimer = new StopWatch("native encoding");
  private final StopWatch solvingTimer = new StopWatch("native STP solving");
  private final StopWatch createTimer = new StopWatch("create STP formula");
  public final StopWatch nativeSTPObjectCreationTimer = new StopWatch("create STP native objects creation");

  private CharacterEncoding encoding;
  private final STPSolverCache cache;
  private final STPExpr TRUE = new BoolConstSTPExpr(this, true);
  private final STPExpr FALSE = new BoolConstSTPExpr(this, false);

  private final PigeonHoleDistributor distributor;

  public STPSolver(){
    super("STP-regexp");
    cache = new STPSolverCache();
    distributor = new PigeonHoleDistributor();
  }

  @Override
  public Solution solve(Constraint constraint, int size){
    try{
      if (verbose){
        System.out.println();
        System.out.println("size:" + size);
        //                System.out.println(c);
      }
      if (constraint.getConjuncts().isEmpty())
        return Solution.createSAT();

      if (constraint.getVariables().size() == 0)
        throw new UnsupportedOperationException("Must supply at least one variable");

      if (constraint.getVariables().size() > 1)
        throw new UnsupportedOperationException("multi-variable constraints are not supported yet");

      VariableExpression v = constraint.getVariables().iterator().next();
      Constraint c = addVarInSigmaStarConstraint(constraint, v);
      c.removeUnequalSizeEqualities(size);
      if (!isValidSubsequencesLength(constraint, size) || !isValidEqualityLength(constraint.getEqualsConjuncts(), size))
        return Solution.createUNSAT(); //cut this short

      if (size == 0){//try empty string without calling STP
        Solution emptyStringSol = Solution.createSAT();
        emptyStringSol.setValue(v, "");
        boolean checkSolution = new SolutionChecker().checkSolution(c, emptyStringSol);
        if (checkSolution)
          return emptyStringSol;
      }

      int varlength = size;
      if (!constraint.isLegal(varlength))
        return Solution.createUNSAT();
      if (verbose){
        System.out.println("length:" + varlength);
      }

      createTimer.start();

      encoding = new CharacterEncoding();

      List<RegexpConstraint> regExpConjuncts = c.getRegExpConjuncts();
      List<EqualsConstraint> equalsConjuncts = c.getEqualsConjuncts();

      List<STPExpr> expressions = new ArrayList<STPExpr>(equalsConjuncts.size() + regExpConjuncts.size());

      BVExpr[] regularExpressionBvs = new BVExpr[regExpConjuncts.size()];
      int[] regularExpressionBvLens = new int[regExpConjuncts.size()];
      if (!makeBitVectorsForRegularExpressions(regExpConjuncts, varlength, expressions, regularExpressionBvs, regularExpressionBvLens))
        return Solution.createUNSAT();

      BVExpr[] equalsBvs = new BVExpr[2 * equalsConjuncts.size()];
      int[] equalsBvLens = new int[2 * equalsConjuncts.size()];
      if (!makeBitVectorsForEqualsExpressions(equalsConjuncts, varlength, expressions, equalsBvs, equalsBvLens, regularExpressionBvs.length))
        return Solution.createUNSAT();

      STPExpr stpFormula = AndExpr.create(this, expressions);
      STPExpr stpVarFormula = AndExpr.create(this, stpFormula, linkVars(regExpConjuncts, regularExpressionBvs, equalsConjuncts, equalsBvs, varlength));
      STPExpr fullFormula = AndExpr.create(this, stpVarFormula, linkSubsequenceVals(regExpConjuncts, regularExpressionBvs, equalsConjuncts, equalsBvs, varlength));
      createTimer.stop();
      List<STPExpr> alternatives;
      if (OPT_TOP_DISJ_SPLIT && fullFormula.getKind() == STPExprKind.OrExpr){
        List<STPExpr> subexpressions = ((OrExpr) fullFormula).getSubexpressions();
        alternatives = subexpressions;
      }else{
        alternatives = Collections.singletonList(fullFormula);
      }
      if (INCREMENTAL){
        alternatives = Arrays.asList(OrExpr.create(this, alternatives));//all alternatives together
      }
      for (STPExpr expr : alternatives){
        SolvingContext sc;
        if (INCREMENTAL){
          sc=new SolvingContext(ChoiceGenerator.<STPExpr>createOneByOne(), encoding);//XXX does not work yet
        }else{
          sc = new SolvingContext(ChoiceGenerator.<STPExpr>createFull(), encoding);
        }
        while (!sc.getChoiceGenerator().isDone()){//TODO replace the 'alternatives' loop with this loop
          VC vc = new VC();
          VC.setFlags('a');//turn off optimizations - it makes it faster because our constraints are simple
          sc.setVC(vc);
          nativeEncodingTimer.start();
          Expr full = expr.getExpr(sc, 0);
          nativeEncodingTimer.stop();
          solvingTimer.start();
          vc.assertFormula(full);
          int query = vc.query(falseExpr().getExpr(sc, 0));
          solvingTimer.stop();
          //          System.out.println("Solving STP " + (query == 0) + "\n------------------------");
          if (query == 0){
            Solution sat = Solution.createSAT();
            String decodedValue = decodeValue(sc, regularExpressionBvs);
            if (decodedValue != null){
              sat.setValue(v, decodedValue);
            }
            vc.Destroy();
            return sat;
          }
          sc.getChoiceGenerator().reset();
          vc.Destroy();
        }
            }

      return Solution.createUNSAT();
    }finally{
      if (verbose){
        System.out.println(createTimer);
        System.out.println(distroTimer);
        System.out.println(shiftingTimer);
        //                System.out.println(shiftingTimer.getTimesHistogram().toStringSortedByKey());
        System.out.println(nativeEncodingTimer);
        System.out.println(nativeSTPObjectCreationTimer);
        System.out.println(solvingTimer);
      }
    }
  }

  //Check that the size of equality expressions are the same
  private boolean isValidEqualityLength(List<EqualsConstraint> equalsConjuncts, int varLength){
    for (EqualsConstraint ec : equalsConjuncts){
      if (ec.isEqual() && ec.getExpression1().getSize(varLength) != ec.getExpression2().getSize(varLength))
        return false;
    }
    return true;
  }

  private boolean makeBitVectorsForEqualsExpressions(List<EqualsConstraint> equalsConjuncts, int varlength, List<STPExpr> expressions, BVExpr[] equalsBvs, int[] equalsBvLens,
      int numOfPreviouslyGeneratedVectors){
    int count = 0;
    for (EqualsConstraint ec : equalsConjuncts){
      int bv1Length = getBVLength(varlength, ec.getExpression1());
      int bv2Length = getBVLength(varlength, ec.getExpression2());

      BVExpr bv1 = BVExpr.create(this, "bv" + (count + numOfPreviouslyGeneratedVectors), encodingSize() * bv1Length);
      equalsBvs[count] = bv1;
      equalsBvLens[count] = bv1Length;
      count++;
      BVExpr bv2 = BVExpr.create(this, "bv" + (count + numOfPreviouslyGeneratedVectors), encodingSize() * bv2Length);
      equalsBvs[count] = bv2;
      equalsBvLens[count] = bv2Length;
      count++;

      STPExpr e = createEqualsConstraint(bv1, bv1Length, bv2, bv2Length, ec, varlength);
      expressions.add(e);
      if (e.equals(falseExpr()))
        return false;
    }
    return true;
  }


  private boolean makeBitVectorsForRegularExpressions(List<RegexpConstraint> regExpConjuncts, int varlength, List<STPExpr> expressions, BVExpr[] bvs, int[] bvLens){
    int count = 0;
    for (RegexpConstraint rc : regExpConjuncts){
      int bvLength = getBVLength(varlength, rc.getExpression());

      BVExpr bv = BVExpr.create(this, "bv" + count, encodingSize() * bvLength);
      bvs[count] = bv;
      bvLens[count] = bvLength;
      count++;

      STPExpr e = createRegexpConstraint(bv, rc, bvLength, varlength);
      expressions.add(e);
      if (e.equals(falseExpr()))
        return false;
    }
    return true;
  }

  /**
   * Adding a constraint that the variable is in the sigma^star. This ensures
   * that there is always a constraint on the original variable (and not only on
   * subsequences of the var) and allows the comparison of subsequences to the
   * bit vector created by this constraint. The code is duplicated since the
   * Hampi object is not available here.
   */

  private Constraint addVarInSigmaStarConstraint(Constraint constraint, VariableExpression v){
    Regexp sigma = HampiConstraints.rangeRegexp(ASCIITable.lowestChar, ASCIITable.highestChar);
    Regexp sigmaStar = HampiConstraints.starRegexp(sigma);
    Constraint varInSigma = HampiConstraints.regexpConstraint(v, true, sigmaStar);
    return HampiConstraints.andConstraint(varInSigma, constraint);
  }

  /**
   * Returns the size of bitvector (in chars) given the size of var (in chars)
   */
  private int getBVLength(int varlength, Expression e){
    Set<VariableExpression> vars = e.getVariables();
    if (vars.isEmpty())
      return e.getSize(0);
    Solution s = Solution.createSAT();
    String val = Utils.repeat(varlength, 'a');
    s.setValue(vars.iterator().next(), val);
    return e.getValue(s).length();
  }

  /**
   * Returns the solved value for the variable.
   */
  private String decodeValue(SolvingContext sc, BVExpr[] bvs){
    //The first constraint asserts that the variable is in sigma*
    //and thus it can be used to decode the result
    return encoding.decodeValue(sc.getVC(), bvs[0].getExpr(sc, 0));
  }

  /**
   * Creates an expression that means: the parts of bitvectors that denote the
   * variable are all equal.
   */
  private STPExpr linkVars(List<RegexpConstraint> regExpConjuncts, BVExpr[] regularExpressionBvs, List<EqualsConstraint> equalsConjuncts, BVExpr[] equalsBvs, int varlength){
    if (regularExpressionBvs.length + equalsBvs.length == 0)
      return trueExpr();
    List<STPExpr> expressions = extractVariableFromRegExp(regExpConjuncts, regularExpressionBvs, varlength);
    expressions.addAll(extractVariableFromEqualConstraint(equalsConjuncts, equalsBvs, varlength));
    return allEqual(expressions);
  }

  /**
   * Creates an expression that means: the parts of bitvectors that denote each
   * subsequence is equal to the appropriate part of the original variable
   */
  private STPExpr linkSubsequenceVals(List<RegexpConstraint> regExpConjuncts, BVExpr[] regularExpressionBvs, List<EqualsConstraint> equalsConjuncts, BVExpr[] equalsBvs, int varlength){
    if (regularExpressionBvs.length + equalsBvs.length == 0)
      return trueExpr();
    Set<SubsequenceExpression> subsequences = getSubsequences(regExpConjuncts, equalsConjuncts);
    List<STPExpr> valEqualExpressions = new ArrayList<STPExpr>();
    for (SubsequenceExpression val : subsequences){
      valEqualExpressions.add(linkSubsequenceVal(regExpConjuncts, regularExpressionBvs, equalsConjuncts, equalsBvs, val, varlength));
    }
    return and(valEqualExpressions);
  }


  /**
   * Creates an expression that means: the parts of bitvectors that denote the
   * variable are all equal.
   */
  private STPExpr linkSubsequenceVal(List<RegexpConstraint> regExpConjuncts, BVExpr[] regularExpressionBvs, List<EqualsConstraint> equalsConjuncts, BVExpr[] equalsBvs, SubsequenceExpression val,
      int varLength){
    if (regularExpressionBvs.length + equalsBvs.length == 0)
      return trueExpr();
    List<STPExpr> expressions = extractValFromRegExp(regExpConjuncts, regularExpressionBvs, val, varLength);
    expressions.addAll(extractValFromEqualConstraint(equalsConjuncts, equalsBvs, val, varLength));
    int enc = encodingSize();
    //adding the position of the subsequence in the bit vector for the variable
    expressions.add(regularExpressionBvs[0].extract(enc * (val.getStartIndex() + val.getLength()) - 1, enc * val.getStartIndex(), enc));
    return allEqual(expressions);
  }

  private List<STPExpr> extractVariableFromEqualConstraint(List<EqualsConstraint> equalsConjuncts, BVExpr[] equalsBvs, int varlength){
    List<STPExpr> expressions = new ArrayList<STPExpr>(2*equalsConjuncts.size());
    for (int i = 0; i < equalsConjuncts.size(); i++){
      Expression e1 = equalsConjuncts.get(i).getExpression1();
      List<Integer> offsets = e1.getVarOffSets(varlength);
      for (int offset : offsets){
        int enc = encodingSize();
        STPExpr encoded = equalsBvs[2 * i].extract(enc * (offset + varlength) - 1, enc * offset, enc);
        expressions.add(encoded);
      }
      Expression e2 = equalsConjuncts.get(i).getExpression2();
      offsets = e2.getVarOffSets(varlength);
      for (int offset : offsets){
        int enc = encodingSize();
        STPExpr encoded = equalsBvs[2 * i + 1].extract(enc * (offset + varlength) - 1, enc * offset, enc);
        expressions.add(encoded);
      }
    }
    return expressions;
  }

  private List<STPExpr> extractValFromEqualConstraint(List<EqualsConstraint> equalsConjuncts, BVExpr[] equalsBvs, SubsequenceExpression val, int varlength){
    List<STPExpr> expressions = new ArrayList<STPExpr>();
    for (int i = 0; i < equalsConjuncts.size(); i++){
      Expression e1 = equalsConjuncts.get(i).getExpression1();
      List<Integer> offsets = e1.getSubsequenceOffSets(val, varlength);
      for (int offset : offsets){
        int enc = encodingSize();
        STPExpr encoded = equalsBvs[2 * i].extract(enc * (offset + val.getLength()) - 1, enc * offset, enc);
        expressions.add(encoded);
      }
      Expression e2 = equalsConjuncts.get(i).getExpression2();
      offsets = e2.getSubsequenceOffSets(val, varlength);
      for (int offset : offsets){
        int enc = encodingSize();
        STPExpr encoded = equalsBvs[2 * i + 1].extract(enc * (offset + val.getLength()) - 1, enc * offset, enc);
        expressions.add(encoded);
      }
    }
    return expressions;
  }

  private List<STPExpr> extractVariableFromRegExp(List<RegexpConstraint> regExpConjuncts, BVExpr[] regularExpressionBvs, int varlength){
    List<STPExpr> expressions = new ArrayList<STPExpr>(regExpConjuncts.size());
    for (int i = 0; i < regExpConjuncts.size(); i++){
      Expression e = regExpConjuncts.get(i).getExpression();

      List<Integer> offSets = e.getVarOffSets(varlength);
      for (int offset : offSets){
        int enc = encodingSize();
        STPExpr encoded = regularExpressionBvs[i].extract(enc * (offset + varlength) - 1, enc * offset, enc);
        expressions.add(encoded);
      }
    }
    return expressions;
  }

  private List<STPExpr> extractValFromRegExp(List<RegexpConstraint> regExpConjuncts, BVExpr[] regularExpressionBvs, SubsequenceExpression val, int varlength){
    List<STPExpr> expressions = new ArrayList<STPExpr>(regExpConjuncts.size());
    for (int i = 0; i < regExpConjuncts.size(); i++){
      Expression e = regExpConjuncts.get(i).getExpression();

      List<Integer> offsets = e.getSubsequenceOffSets(val, varlength);
      for (int offset : offsets){
        int enc = encodingSize();
        STPExpr encoded = regularExpressionBvs[i].extract(enc * (offset + val.getLength()) - 1, enc * offset, enc);
        expressions.add(encoded);
      }
    }
    return expressions;
  }


  private Set<SubsequenceExpression> getSubsequences(List<RegexpConstraint> regExpConjuncts, List<EqualsConstraint> equalsConjuncts){
    Set<SubsequenceExpression> result = new LinkedHashSet<SubsequenceExpression>();
    for(Expression e:getExpressions(regExpConjuncts, equalsConjuncts)) {
      if (e instanceof SubsequenceExpression){
        result.add((SubsequenceExpression)e);
      }
    }
    return result;
  }


  private Set<Expression> getExpressions(List<RegexpConstraint> regExpConjuncts, List<EqualsConstraint> equalsConjuncts){
    Set<Expression> result = new LinkedHashSet<Expression>();
    for (RegexpConstraint rc : regExpConjuncts){
      result.add(rc.getExpression());
    }
    for (EqualsConstraint ec : equalsConjuncts){
      result.add(ec.getExpression1());
      result.add(ec.getExpression2());
    }
    return result;
  }

  private STPExpr and(List<STPExpr> expressions){
    if (expressions.size() < 1)
      return trueExpr();
    STPExpr result = trueExpr();
    for (STPExpr e : expressions){
        result = AndExpr.create(this, result, e);
    }
    return result;
  }

  /**
   * Returns the number of bits per character in the encoding.
   */
  private int encodingSize(){
    return encoding.size();
  }

  /**
   * Create and expression that equates all subexpressions.
   */
  private STPExpr allEqual(List<STPExpr> expressions){
    if (expressions.size() < 2)
      return trueExpr();
    STPExpr result = trueExpr();
    STPExpr first = expressions.get(0);
    for (STPExpr e : expressions){
      if (e != first){//skip comparing first to self
        STPExpr prevEqCurr = first.binOp(BinOpKind.EQ_OP, e);
        result = AndExpr.create(this, result, prevEqCurr);
      }
    }
    return result;
  }

  private STPExpr createEqualsConstraint(BVExpr bv1, int bv1Length, BVExpr bv2, int bv2Length, EqualsConstraint ec, int varlength){
    Expression expr1 = ec.getExpression1();
    Expression expr2 = ec.getExpression2();
    int enc = encodingSize();
    //adding the position of the subsequence in the bit vector for the variable
    ;
    STPExpr equalityExpr = bv1.extract(enc * bv1Length - 1, enc * 0, enc).binOp(BinOpKind.EQ_OP, bv2.extract(enc * bv2Length - 1, enc * 0, enc));
    equalityExpr = ec.isEqual() ? equalityExpr : NotExpr.create(equalityExpr, this);
    equalityExpr = AndExpr.create(this, equalityExpr, getExpressionSTP(bv1, expr1, varlength));
    equalityExpr = AndExpr.create(this, equalityExpr, getExpressionSTP(bv2, expr2, varlength));

    return equalityExpr;
  }

  private STPExpr getExpressionSTP(BVExpr bv, Expression expr, int varLen){
    if (expr.getKind() == ElementKind.VAR_EXPRESSION || expr.getKind() == ElementKind.SUBSEQUENCE_EXPRESSION)
      return trueExpr();
    if (expr.getKind() == ElementKind.CONST_EXPRESSION){
      STPExpr result = trueExpr();
      ConstantExpression constExpr = (ConstantExpression) expr;
      String str = constExpr.getString();
      //TODO encode as a single equals not a conjunction char-by-char
      for (int i = 0; i < str.length(); i++){
        int num = encoding.encodedValue(str.charAt(i));
        STPExpr ch = encoding.extractedChar(i, bv);
        result = AndExpr.create(this, result, ch.binOp(BinOpKind.EQ_OP, ConstExpr.create(this, num)));
      }
      return result;
    }
    if (expr.getKind() == ElementKind.CONCAT_EXPRESSION){
      ConcatExpression ce = (ConcatExpression) expr;
      List<Expression> subs = ce.getSubexpressions();
      STPExpr result = trueExpr();
      int offsetSoFar = 0;
      for (Expression sub : subs){
        if (sub.getKind() == ElementKind.CONST_EXPRESSION){
          ConstantExpression constExpr = (ConstantExpression) sub;
          String str = constExpr.getString();
          //TODO encode as a single equals not a conjunction char-by-char
          for (int i = 0; i < str.length(); i++){
            int num = encoding.encodedValue(str.charAt(i));
            STPExpr ch = encoding.extractedChar(i + offsetSoFar, bv);
            result = AndExpr.create(this, result, ch.binOp(BinOpKind.EQ_OP, ConstExpr.create(this, num)));
          }
          offsetSoFar += str.length();
        }
        if (sub.getKind() == ElementKind.VAR_EXPRESSION){
          offsetSoFar += varLen;
        }
        if (sub.getKind() == ElementKind.SUBSEQUENCE_EXPRESSION){
          offsetSoFar += ((SubsequenceExpression) sub).getLength();
        }
        if (sub.getKind() == ElementKind.CONCAT_EXPRESSION)
          throw new IllegalArgumentException("should not have nested concats: " + expr);
      }
      return result;
    }
    throw new UnsupportedOperationException("not implemented yet " + expr);
  }

  //bvlen is in in chars (not bits)
  //varlen is in in chars (not bits)
  private STPExpr createRegexpConstraint(BVExpr bv, RegexpConstraint rc, int bvLen, int varLen){
    Regexp regexp = rc.getRegexp();

    //    System.out.println("regexp:" + regexp);
    StopWatch stpAcceptTimer = new StopWatch("STP accept ");
    stpAcceptTimer.start();
    STPExpr tryLength = stpAccept(0, bvLen, regexp, bv);
    stpAcceptTimer.stop();

    //fixing the constant prefix and suffix
    Expression expr = rc.getExpression();
    if (expr.getKind() == ElementKind.VAR_EXPRESSION || expr.getKind() == ElementKind.SUBSEQUENCE_EXPRESSION)
      return rc.isMembership() ? tryLength : NotExpr.create(tryLength, this);
    if (expr.getKind() == ElementKind.CONCAT_EXPRESSION){
      if (tryLength.equals(falseExpr()) && rc.isMembership())
        return falseExpr();

      ConcatExpression ce = (ConcatExpression) expr;
      List<Expression> subs = ce.getSubexpressions();
      STPExpr result = tryLength;
      int offsetSoFar = 0;
      for (Expression sub : subs){
        if (sub.getKind() == ElementKind.CONST_EXPRESSION){
          ConstantExpression constExpr = (ConstantExpression) sub;
          String str = constExpr.getString();
          //TODO encode as a single equals not a conjunction char-by-char
          for (int i = 0; i < str.length(); i++){
            int num = encoding.encodedValue(str.charAt(i));
            STPExpr ch = encoding.extractedChar(i + offsetSoFar, bv);
            result = AndExpr.create(this, result, ch.binOp(BinOpKind.EQ_OP, ConstExpr.create(this, num)));
          }
          offsetSoFar += str.length();
        }
        if (sub.getKind() == ElementKind.VAR_EXPRESSION){
          offsetSoFar += varLen;
        }
        if (sub.getKind() == ElementKind.SUBSEQUENCE_EXPRESSION){
          offsetSoFar +=((SubsequenceExpression)sub).getLength();
        }
        if (sub.getKind() == ElementKind.CONCAT_EXPRESSION)
          throw new IllegalArgumentException("should not have nested concats: " + rc);
      }
      return rc.isMembership() ? result : NotExpr.create(result, this);
    }
    throw new UnsupportedOperationException("not implemented yet " + rc);
  }



  /**
   * Create expression that says: suffix of bv starting at startIdx is in
   * L(regexp).
   */
  private STPExpr stpAccept(int startIdx, int varLen, Regexp regexp, BVExpr bv){
    //    System.out.println("stpAccept:" + regexp + " " + startIdx + " " + varLen);
    if (regexp.getKind() == ElementKind.CONST_REGEXP)
      return constant(startIdx, varLen, (ConstRegexp) regexp, bv);
    else if (regexp.getKind() == ElementKind.CONCAT_REGEXP)
      return concat(startIdx, varLen, (ConcatRegexp) regexp, bv);
    else if (regexp.getKind() == ElementKind.OR_REGEXP)
      return or(startIdx, varLen, (OrRegexp) regexp, bv);
    else if (regexp.getKind() == ElementKind.STAR_REGEXP)
      return star(startIdx, varLen, (StarRegexp) regexp, bv);
    else
      throw new UnsupportedOperationException("invalid regexp:" + regexp);
  }

  /**
   * Create a STP expression for constant regexp.
   */
  private STPExpr constant(int startIdx, int varLen, ConstRegexp regexp, BVExpr bv){
    //can't be a string of a different size than defined
    String string = regexp.getString();
    if (varLen != string.length())
      return falseExpr();
    if (varLen == 0 && string.isEmpty())
      return trueExpr();
    //TODO can we encode the whole thing as a single equals?
    STPExpr[] letters = new STPExpr[varLen];
    char[] chars = string.toCharArray();
    for (int i = 0; i < varLen; i++){
      STPExpr ch = encoding.extractedChar(i + startIdx, bv);
      int num = encoding.encodedValue(chars[i]);
      STPExpr oneLetter = ch.binOp(BinOpKind.EQ_OP, ConstExpr.create(this, num));
      letters[i] = oneLetter;
    }
    if (letters.length == 1)
      return letters[0];
    else
      return AndExpr.create(this, letters);//call directly, because there will be no shortcuts here for sure
  }

  /**
   * STP expression for Or regexp.
   */
  private STPExpr or(int startIdx, int varLen, OrRegexp regexp, BVExpr bv){
    List<Pair<Character, Character>> ranges = regexp.getCharacterRanges();
    if (ranges != null){
      STPExpr[] rangeExprs = new STPExpr[ranges.size()];
      for (int i = 0; i < ranges.size(); i++){
        Pair<Character, Character> range = ranges.get(i);
        STPExpr ch = encoding.extractedChar(startIdx, bv);
        int low = encoding.encodedValue(range.first);
        int high = encoding.encodedValue(range.second);
        assert (low <= high) : low + " " + high + " " + range.first + " " + range.second;
        if (low == high){
          rangeExprs[i] = ch.binOp(BinOpKind.EQ_OP, ConstExpr.create(this, low));
        }else{
          STPExpr lowBound = ch.binOp(BinOpKind.GE_OP, ConstExpr.create(this, low));
          STPExpr highBound = ch.binOp(BinOpKind.LE_OP, ConstExpr.create(this, high));
          rangeExprs[i] = AndExpr.create(this, lowBound, highBound);
        }
      }
      return OrExpr.create(this, rangeExprs);
    }else{
      List<STPExpr> subexpr = new ArrayList<STPExpr>(regexp.getExpressions().length);
      for (Regexp expr : regexp.getExpressions()){
        STPExpr sub = stpAccept(startIdx, varLen, expr, bv);
        if (sub.equals(trueExpr()))
          return trueExpr();
        subexpr.add(sub);
      }
      return OrExpr.create(this, subexpr);
    }
  }

  /**
   * STP expression for concat regexp.
   */
  private STPExpr concat(int startIdx, int varLen, ConcatRegexp regexp, BVExpr bv){
    STPExpr cached = checkConcatCache(startIdx, varLen, regexp, bv);
    if (cached != null)
      return cached;

    Regexp[] subexpresions = regexp.getExpressions();
    List<Integer> uppers = getUpperBounds(subexpresions);
    List<Integer> lowers = getLowerBounds(subexpresions);

    int holes = subexpresions.length;
    int pigeons = varLen;
    distroTimer.start();
    Set<List<Integer>> distros = distributor.distribute2(holes, pigeons, lowers, uppers);
    distroTimer.stop();

    List<STPExpr> subexpr = new ArrayList<STPExpr>(distros.size());
    for (List<Integer> distro : distros){
      List<STPExpr> parts = new ArrayList<STPExpr>(distro.size());
      int sum = 0;
      for (int i = 0, n = distro.size(); i < n; i++){
        int partSize = distro.get(i);
        STPExpr partExpr = stpAccept(startIdx + sum, partSize, subexpresions[i], bv);
        parts.add(partExpr);
        if (partExpr.equals(falseExpr())){//the whole AND will be a false
          break;
        }
        sum += partSize;
      }
      STPExpr and = AndExpr.create(this, parts);
      if (and.equals(trueExpr()))//the whole OR is a true
        return trueExpr();
      subexpr.add(and);
    }
    STPExpr res = OrExpr.create(this, subexpr);
    addToConcatCache(startIdx, varLen, regexp, res, bv);
    return res;
  }

  private STPExpr checkConcatCache(int startIdx, int varLen, ConcatRegexp regexp, BVExpr bv){
    Pair<Integer, STPExpr> cached = cache.getConcat(varLen, regexp);
    if (cached == null)
      return null;

    //need to shift the expression (we have it cached but for a different start index, so we need to shift)
    int cachedStartIdx = cached.first;
    int diff = startIdx - cachedStartIdx;

    if (diff == 0)
      return cached.second;

    STPExpr shifted = ShiftedSTPExpr.shift(cached.second, diff);
    addToConcatCache(startIdx, varLen, regexp, shifted, bv);
    return shifted;
  }

  private void addToConcatCache(int startIdx, int varLen, ConcatRegexp regexp, STPExpr res, BVExpr bv){
    cache.putConcat(varLen, regexp, Pair.create(startIdx, res));
  }

  /**
   * Returns the list of lower bounds for the expressions.
   */
  private static List<Integer> getLowerBounds(Regexp[] subexpresions){
    List<Integer> result = new ArrayList<Integer>(subexpresions.length);
    for (Regexp subexpresion : subexpresions){
      result.add(subexpresion.getSizeLowerBound());
    }
    return result;
  }

  /**
   * Returns the list of upper bounds for the expressions.
   */
  private static List<Integer> getUpperBounds(Regexp[] subexpresions){
    List<Integer> result = new ArrayList<Integer>(subexpresions.length);
    for (Regexp subexpresion : subexpresions){
      result.add(subexpresion.getSizeUpperBound());
    }
    return result;
  }

  /**
   * STP expression for star regexp.
   */
  private STPExpr star(int startIdx, int varLen, StarRegexp regexp, BVExpr bv){
    if (varLen == 0)
      return trueExpr();
    Regexp expr = regexp.getExpression();
    int exprLowerBound = max(1, expr.getSizeLowerBound());
    int exprUpperBound = min(varLen, expr.getSizeUpperBound());
    int maxNumberOfRepeats = (varLen / exprLowerBound);
    if (maxNumberOfRepeats == 0)
      return falseExpr();
    int minNumberOfRepeats = (varLen / exprUpperBound);
    if (minNumberOfRepeats == 0)
      return trueExpr();
    int pigeons = varLen;
    List<STPExpr> subexpr = new ArrayList<STPExpr>();
    for (int repeats = minNumberOfRepeats; repeats <= maxNumberOfRepeats; repeats++){
      int holes = repeats;

      List<Integer> lowers = repeat(exprLowerBound, repeats);
      List<Integer> uppers = repeat(exprUpperBound, repeats);
      distroTimer.start();
      Set<List<Integer>> distros = distributor.distribute2(holes, pigeons, lowers, uppers);
      distroTimer.stop();
      for (List<Integer> distro : distros){
        List<STPExpr> parts = new ArrayList<STPExpr>(distro.size());
        int sum = 0;
        for (int i = 0; i < distro.size(); i++){
          int partSize = distro.get(i);
          STPExpr partExpr = stpAccept(startIdx + sum, partSize, expr, bv);
          parts.add(partExpr);
          if (partExpr.equals(falseExpr())){
            break;
          }
          sum += partSize;
        }
        STPExpr and = AndExpr.create(this, parts);
        if (and.equals(trueExpr()))//the whole OR is a true
          return trueExpr();
        subexpr.add(and);
      }
    }
    return OrExpr.create(this, subexpr);
  }

  /**
   * List of n repeats of number k.
   */
  private static List<Integer> repeat(int k, int n){
    Integer kInt = k;//box once to save some time
    List<Integer> res = new ArrayList<Integer>(n);
    for (int i = 0; i < n; i++){
      res.add(kInt);
    }
    return res;
  }

  public STPExpr trueExpr(){
    return TRUE;
  }

  public STPExpr falseExpr(){
    return FALSE;
  }

  STPSolverCache getCache(){
    return cache;
  }
}
