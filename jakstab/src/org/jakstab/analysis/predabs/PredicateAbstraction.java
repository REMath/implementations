/*
 * PredicateAbstraction.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.predabs;

import java.util.Collections;
import java.util.Set;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.*;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.solver.Solver;
import org.jakstab.util.Characters;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;


/**
 * @author Johannes Kinder
 */
public class PredicateAbstraction implements ConfigurableProgramAnalysis {

	public static void register(AnalysisProperties p) {
		p.setShortHand('p');
		p.setName("Predicate abstraction");
		p.setDescription("Experimental, partial implementation of predicate abstraction.");
		p.setExplicit(true);
	}

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(PredicateAbstraction.class);
	
	private BDDFactory bddFactory;
	
	public PredicateAbstraction() {
		bddFactory = BDDFactory.init("java", 1000, 100);
		bddFactory.setVarNum(6);
	}
	
	@Override
	public Precision initPrecision(Location location, StateTransformer transformer) {
		return new PredicatePrecision();
	}

	@Override
	public AbstractState initStartState(Location label) {
		return new PredicateAbstractionState(bddFactory);
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2,
			Precision precision) {
		return CPAOperators.mergeJoin(s1, s2, precision);
	}

	@Override
	public Set<AbstractState> post(final AbstractState state, CFAEdge edge,
			final Precision precision) {
		final RTLStatement statement = (RTLStatement)edge.getTransformer();
		final PredicateAbstractionState s = (PredicateAbstractionState)state;
		final PredicatePrecision prec = (PredicatePrecision)precision;
		Set<AbstractState> post = statement.accept(new DefaultStatementVisitor<Set<AbstractState>>() {

			private final Set<AbstractState> fallThroughState() {
				return Collections.singleton(state);
			}

			@Override
			public Set<AbstractState> visit(RTLAlloc stmt) {
				return fallThroughState();
			}

			@Override
			public Set<AbstractState> visit(RTLAssert stmt) {
				if (Solver.isSatisfiable(ExpressionFactory.createAnd(s.getStateFormula(prec), 
						ExpressionFactory.createNot(stmt.getAssertion())))) {
					logger.error("Found possible assertion violation at " + stmt.getLabel() + "! " + stmt + " evaluated to " + Characters.TOP + " in state:");
					logger.error(s);
				}
				return fallThroughState();
			}

			@Override
			public Set<AbstractState> visit(RTLVariableAssignment stmt) {
				BDD postPreds = s.predicates.id();
				Writable lhs = stmt.getLeftHandSide();

				RTLExpression xprime = ExpressionFactory.createVariable("xprime" + lhs.getBitWidth(), lhs.getBitWidth()); 

				Context subCtx = new Context();
				subCtx.substitute(lhs, xprime);

				Solver solver = Solver.createSolver();
				RTLExpression stateFormula = s.getStateFormula(prec);
				solver.addAssertion(stateFormula);
				solver.addAssertion(ExpressionFactory.createEqual(xprime, 
						stmt.getRightHandSide()));
				
				for (int predIdx = 0; predIdx <= PredicateMap.getMaxIndex(); predIdx++) { 
					RTLExpression p = PredicateMap.getPredicate(predIdx);
					if (!p.getUsedVariables().contains(lhs)) 
						continue;
					// substitute x by xprime
					p = p.evaluate(subCtx);
					
					// Clear variable from predicate BDD
					setVariableDontCare(postPreds, predIdx);
					
					// check if the predicate holds or not
					solver.push();
					solver.addAssertion(ExpressionFactory.createNot(p));

					if (solver.isUnsatisfiable()) {
						postPreds.andWith(bddFactory.ithVar(predIdx));
					} else {
						// Now check whether the negative of the predicate holds
						solver.pop();
						solver.push();
						solver.addAssertion(p);
						if (solver.isUnsatisfiable()) {
							postPreds.andWith(bddFactory.nithVar(predIdx));
						}
					}
					// nothing for don't know, the predicate is already cleared from the BDD

					solver.pop();
				}

				return Collections.singleton((AbstractState)new PredicateAbstractionState(postPreds));
			}
			
			@Override
			public Set<AbstractState> visit(RTLMemoryAssignment stmt) {
				// Memory assignments not supported
				return fallThroughState();
			}

			@Override
			public Set<AbstractState> visit(RTLAssume stmt) {
				Solver solver = Solver.createSolver();
				solver.addAssertion(s.getStateFormula(prec));
				solver.addAssertion(stmt.getAssumption()); 
				if (solver.isUnsatisfiable())
					return Collections.emptySet();

				// OK? was empty in old impl
				BDD postPreds = s.predicates.id();

				for (int predIdx = 0; predIdx <= PredicateMap.getMaxIndex(); predIdx++) { 
					RTLExpression p = PredicateMap.getPredicate(predIdx);
					// check if the predicate holds or not
					solver.push();
					solver.addAssertion(ExpressionFactory.createNot(p));
					if (solver.isUnsatisfiable()) {
						setVariableDontCare(postPreds, predIdx);
						postPreds.andWith(bddFactory.ithVar(predIdx));
					} else {
						// Now check whether the negative of the predicate holds
						solver.pop();
						solver.push();
						solver.addAssertion(p);
						if (solver.isUnsatisfiable()) {
							setVariableDontCare(postPreds, predIdx);
							postPreds.andWith(bddFactory.nithVar(predIdx));
						}
					}
					solver.pop();
				}
				
				return Collections.singleton((AbstractState)new PredicateAbstractionState(postPreds));
			}

			@Override
			public Set<AbstractState> visit(RTLDealloc stmt) {
				return fallThroughState();
			}

			@Override
			public Set<AbstractState> visit(RTLSkip stmt) {
				return fallThroughState();
			}
			
			
		});
		
		//logger.info(edge);
		//logger.info(post);
		
		return post;
	}
	
	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
			CFAEdge cfaEdge, Precision precision) {
		return s;
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s,
			Precision precision, ReachedSet reached) {
		return Pair.create(s, precision);
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return CPAOperators.stopSep(s, reached, precision);
	}

	private BDD setVariableDontCare(BDD bdd, int i) {
		BDD pos = bdd.restrict(bddFactory.ithVar(i));
		bdd.restrictWith(bddFactory.nithVar(i));
		bdd.orWith(pos);
		return bdd;
	}

	
}
