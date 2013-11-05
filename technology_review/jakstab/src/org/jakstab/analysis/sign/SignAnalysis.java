/*
 * SignAnalysis.java - This file is part of the Jakstab project.
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, see <http://www.gnu.org/licenses/>.
 */
package org.jakstab.analysis.sign;

import java.util.Collections;
import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.*;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.solver.Solver;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

/**
 * Demo analysis for classroom use.
 * 
 * @author Johannes Kinder
 */
public class SignAnalysis implements ConfigurableProgramAnalysis {

	public static void register(AnalysisProperties p) {
		p.setShortHand('g');
		p.setName("Sign analysis");
		p.setDescription("For each variable, compute its sign (-, 0, or +).");
	}

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(SignAnalysis.class);

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#initPrecision()
	 */
	@Override
	public Precision initPrecision(Location location, StateTransformer transformer) {
		return null;
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#initStartState(org.jakstab.cfa.Location)
	 */
	@Override
	public AbstractState initStartState(Location label) {
		return SignState.TOP;
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#merge(org.jakstab.analysis.AbstractState, org.jakstab.analysis.AbstractState, org.jakstab.analysis.Precision)
	 */
	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2,
			Precision precision) {
		if (s2.lessOrEqual(s1)) return s1;
		else return s2;
		//return CPAOperators.mergeSep(s1, s2, precision);
	}

	@Override
	public Set<AbstractState> post(final AbstractState state, CFAEdge edge, Precision precision) {
		final RTLStatement statement = (RTLStatement)edge.getTransformer();
		final SignState s = (SignState)state;
		
		return statement.accept(new DefaultStatementVisitor<Set<AbstractState>>() {

			protected final Set<AbstractState> visitDefault(RTLStatement stmt) {
				return Collections.singleton(state);
			}
			
			@Override
			public Set<AbstractState> visit(RTLVariableAssignment stmt) {
				SignState post = new SignState(s);
				SignElement evaledRhs = s.abstractEval(stmt.getRightHandSide());
				post.setValue(stmt.getLeftHandSide(), evaledRhs);
				if (post.equals(s)) return Collections.singleton(state);
				return Collections.singleton((AbstractState)post);
			}

			@Override
			public Set<AbstractState> visit(RTLAssume stmt) {

				RTLExpression assumption = stmt.getAssumption();

				// First analysis to use yices, demo implementation
				
				Solver solver = Solver.createSolver();
				solver.addAssertion(s.getStateFormula());
				solver.addAssertion(assumption);

				if (!solver.isSatisfiable()) {
					logger.info("Infeasible CFA edge: " + stmt);
					return Collections.emptySet();
				}
				
				SignState post = new SignState(s);
				for (RTLVariable v : assumption.getUsedVariables()) {
					// Check if we can restrict this variable
					if (s.getValue(v).isTop()) {

						solver.push();
						RTLExpression f = ExpressionFactory.createLessOrEqual(v, ExpressionFactory.createNumber(0, v.getBitWidth()));
						solver.addAssertion(f);
						if (!solver.isSatisfiable()) {
							post.setValue(v, SignElement.POSITIVE);
							logger.debug("Restricting state from " + s + " through " + assumption + " to " + post);
						} else {
							solver.pop();
							solver.push();
							f = ExpressionFactory.createNot(ExpressionFactory.createEqual(v, ExpressionFactory.createNumber(0, v.getBitWidth())));
							solver.addAssertion(f);
							if (!solver.isSatisfiable()) {
								post.setValue(v, SignElement.ZERO);
								logger.debug("Restricting state from " + s + " through " + assumption + " to " + post);
							} else {
								solver.pop();
								solver.push();
								f = ExpressionFactory.createLessOrEqual(ExpressionFactory.createNumber(0, v.getBitWidth()), v);
								solver.addAssertion(f);
								if (!solver.isSatisfiable()) {
									post.setValue(v, SignElement.NEGATIVE);
									logger.debug("Restricting state from " + s + " through " + assumption + " to " + post);
								}
							}
						}
						solver.pop();
					}
				}
				return Collections.singleton((AbstractState)post);
				
				/*
				// Modify state so that it respects the assumption
				// We should really enumerate all solutions and create the corresponding states (requires different return type)
				// Currently works only for simple assumptions 
				// Correct handling would be:
				// build state formula
				// add assumption formula
				// abstract all satisfying assignments of this formula into new state(s)
				//   or
				// get new state that most closely overapproximates the combined formula
				// (i) generate DNF from combined formula (ii) 1 state per clause
				// (iii) overapproximate each literal
				//   or
				// (i) abstract assumption into sign-logic, (ii) build new state from intersection
				
				if (assumption instanceof RTLOperation) {
					RTLOperation operation = (RTLOperation)assumption;
					
					switch (operation.getOperator()) {

					// assume(var = value)
					case EQUAL:
						if (operation.getOperands()[0] instanceof RTLVariable) {
							RTLVariable var = (RTLVariable)operation.getOperands()[0];

							if (operation.getOperands()[1] instanceof RTLNumber) {
								SignElement value = ((SignState)state).abstractEval(operation.getOperands()[1]);
								if (value.lessOrEqual(s.getValue(var))) {
									logger.debug("Restricting state to " + var + " = " + value);
									SignState post = new SignState((SignState)state);
									post.setValue(var, value);
									return Collections.singleton((AbstractState)post);
								} else {
									logger.debug("Assume " + assumption + " infeasible at " + stmt.getLabel());
									return Collections.emptySet();
								}
							}
						}
						break;

					// assume(var < value)
					case LESS:
						if (operation.getOperands()[0] instanceof RTLVariable) {
							RTLVariable var = (RTLVariable)operation.getOperands()[0];

							if (operation.getOperands()[1] instanceof RTLNumber) {
								SignElement value = ((SignState)state).abstractEval(operation.getOperands()[1]);
								if (value.equals(SignElement.NEGATIVE) || value.equals(SignElement.ZERO)) {
									if (s.getValue(var).isTop() || s.getValue(var).equals(SignElement.NEGATIVE)) {
										logger.debug("Restricting state to " + var + " = " + value);
										SignState post = new SignState(s);
										post.setValue(var, SignElement.NEGATIVE);
										return Collections.singleton((AbstractState)post);
									} else {
										logger.debug("Assume " + assumption + " infeasible at " + stmt.getLabel());
										logger.debug("State is " + s);
										return Collections.emptySet();
									}
								}
							}
						}
						break;

					// assume (!something)
					case NOT:
						if (operation.getOperands()[0] instanceof RTLOperation) {
							operation = (RTLOperation)operation.getOperands()[0];
							
							switch (operation.getOperator()) {
							case LESS:
								if (operation.getOperands()[0] instanceof RTLVariable) {
									RTLVariable var = (RTLVariable)operation.getOperands()[0];

									if (operation.getOperands()[1] instanceof RTLNumber) {
										SignElement value = ((SignState)state).abstractEval(operation.getOperands()[1]);
										if (value.equals(SignElement.NEGATIVE) || value.equals(SignElement.ZERO)) {
											if (s.getValue(var).isTop() || s.getValue(var).equals(SignElement.NEGATIVE)) {
												logger.debug("Restricting state to " + var + " != " + value);
												Set<AbstractState> posts = new FastSet<AbstractState>();
												SignState post = new SignState(s);
												post.setValue(var, SignElement.ZERO);
												posts.add(post);
												post = new SignState(s);
												post.setValue(var, SignElement.POSITIVE);
												posts.add(post);
												return posts;
											} else {
												logger.debug("Assume " + assumption + " infeasible at " + stmt.getLabel());
												return Collections.emptySet();
											}
										}
									}
								}
								break;
							}
							
						}
						break;
					}

				}
				return fallThroughState();*/
			}

			@Override
			public Set<AbstractState> visit(RTLUnknownProcedureCall stmt) {
				// Remove all information				
				return Collections.singleton((AbstractState)SignState.TOP);
			}
		});
	}

	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
			CFAEdge cfaEdge, Precision precision) {
		return s;
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#prec(org.jakstab.analysis.AbstractState, org.jakstab.analysis.Precision, org.jakstab.analysis.ReachedSet)
	 */
	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s,
			Precision precision, ReachedSet reached) {
		return Pair.create(s, precision);
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#stop(org.jakstab.analysis.AbstractState, org.jakstab.analysis.ReachedSet, org.jakstab.analysis.Precision)
	 */
	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return CPAOperators.stopSep(s, reached, precision);
	}

}
