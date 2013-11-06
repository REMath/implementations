/*******************************************************************************
 * The MIT License
 *
 * Copyright (c) 2008 Adam Kiezun
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 ******************************************************************************/
package hampi.constraints;

import java.util.*;

/**
 * Describes a constraint that may involve string variables.<br>
 * NOTE: Constructors of all constraints are package visible to force usage of
 * HampiConstraint facade
 */
public abstract class Constraint{

  private final ElementKind kind;

  Constraint(ElementKind kind){
    this.kind = kind;
  }

  /**
   * Returns the kind of the expression. Useful for implementing enum switches.
   */
  public final ElementKind getKind(){
    return kind;
  }

  @Override
  public abstract String toString();

  @Override
  public abstract int hashCode();

  @Override
  public abstract boolean equals(Object obj);

  /**
   * Returns all conjuncts in this expression. If this expression is a
   * conjuction, then it returns all sub-expressions, otherwise it returns a
   * singleton set.
   */
  public abstract List<Constraint> getConjuncts();

  /**
   * Returns all regular expression conjuncts in this expression. If this expression is a
   * conjuction, then it returns all sub-regular expressions, otherwise it returns a
   * singleton set.
   */
  public List<RegexpConstraint> getRegExpConjuncts(){
    List<RegexpConstraint> result = new ArrayList<RegexpConstraint>();
    for (Constraint c : getConjuncts()){
      if (c instanceof RegexpConstraint){
        result.add((RegexpConstraint) c);
      }
    }
    return result;
  }

  /**
   * Returns all equals expression conjuncts in this expression. If this
   * expression is a conjuction, then it returns all sub-equal expressions,
   * otherwise it returns a singleton set.
   */
  public List<EqualsConstraint> getEqualsConjuncts(){
    List<EqualsConstraint> result = new ArrayList<EqualsConstraint>();
    for (Constraint c : getConjuncts()){
      if (c instanceof EqualsConstraint){
        result.add((EqualsConstraint) c);
      }
    }
    return result;
  }


  /**
   * Returns the set of all free variables mentioned in this constraint.
   */
  public abstract Set<VariableExpression> getVariables();

  /**
   * Returns the set of all subsequence values mentioned in this constraint.
   */
  public abstract Set<SubsequenceExpression> getSubsequenceVals();

  /**
   * Implements the visitor pattern.
   */
  public abstract void accept(ConstraintGrammarVisitor visitor);

  /**
   * Returns the Java code that creates this constraint.
   */
  public abstract String toJavaCode(String hampiVar);

  /**
   * Returns the set of characters used in this constraint.
   */
  public final Set<Character> charsUsed(){
    final Set<Character> result = new LinkedHashSet<Character>();
    ConstraintGrammarVisitor v = new ConstraintGrammarVisitor(){
      @Override
      public void visitConst(ConstRegexp c){
        result.addAll(asCharacterList(c.getString()));
      }

      @Override
      public void visitConstantExpression(ConstantExpression c){
        result.addAll(asCharacterList(c.getString()));
      }

      private List<Character> asCharacterList(String s){
        List<Character> list = new ArrayList<Character>(s.length());
        for (char d : s.toCharArray()){
          list.add(d);
        }
        return list;
      }
    };
    this.accept(v);
    return result;
  }

  /**
   * Returns the set of characters that must appear in every string that
   * satisfies the constraint.
   */
  public abstract Set<Character> alphabetLowerbound();

  public abstract boolean isLegal(int varSize);

  /**
   * Remove all equality constraints that are of different length as they are
   * satisfied by default
   *
   */
  public abstract void removeUnequalSizeEqualities(int varLength);

}
