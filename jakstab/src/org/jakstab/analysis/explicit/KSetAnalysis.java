/*
 * KSetAnalysis.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.explicit;

import java.util.Collections;
import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.*;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

/**
 * A K-Set analysis as used for the example in the VMCAI'09 paper. It 
 * represents values as sets of a constant size, merging them to TOP if
 * the bound is exceeded. Supports memory values and register aliasing
 * through the generic VariableValuation class.
 * 
 * For programs with procedure calls, it should be used together with a 
 * call-stack analysis for context sensitivity. Otherwise, it will merge
 * the stack contents from different calling contexts, which leads to
 * illegal addresses used as jump targets on return. 
 */
public class KSetAnalysis implements ConfigurableProgramAnalysis {

	public static void register(AnalysisProperties p) {
		p.setShortHand('k');
		p.setName("K-Set analysis");
		p.setDescription("For each variable, collect up to k values per location (non-relational).");
		p.setExplicit(true);
	}
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(KSetAnalysis.class);
	
	private AbstractValueFactory<KSet> valueFactory;
	private int bound;

	public KSetAnalysis() {
		bound = BoundedAddressTracking.varThreshold.getValue();;
		valueFactory = new KSetFactory(bound);
	}

	@Override
	public Precision initPrecision(Location location,
			StateTransformer transformer) {
		return null;
	}

	@Override
	public AbstractState initStartState(Location label) {
		return new ValuationState(valueFactory);
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2,
			Precision precision) {
		return CPAOperators.mergeJoin(s1, s2, precision);
	}

	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge,
			Precision precision) {

		final RTLStatement statement = (RTLStatement)cfaEdge.getTransformer();
		final ValuationState iState = (ValuationState)state;
		return Collections.singleton(statement.accept(new DefaultStatementVisitor<AbstractState>() {

			@Override
			public AbstractState visit(RTLAlloc stmt) {
				ValuationState post = new ValuationState(iState);
				Writable lhs = stmt.getPointer();

				MemoryRegion newRegion;
				if (stmt.getAllocationName() != null) {
					newRegion = MemoryRegion.create(stmt.getAllocationName());
				} else {
					// TODO: Detect whether this allocation is unique to allow strong updates
					newRegion = MemoryRegion.createAsSummary("alloc" + stmt.getLabel());
				}
				
				KSet basePointer = new KSet(bound, new BasedNumberElement(newRegion, 
						ExpressionFactory.createNumber(0, 32)));
				
				if (lhs instanceof RTLVariable) {
					post.setVariableValue((RTLVariable)lhs, basePointer); 
				} else {
					RTLMemoryLocation m = (RTLMemoryLocation)lhs;
					AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
					post.setMemoryValue(evaledAddress, m.getBitWidth(), basePointer);
				}

				return post;
			}

			@Override
			public AbstractState visit(RTLVariableAssignment stmt) {
				ValuationState post = new ValuationState(iState);
				AbstractDomainElement evaledRhs = iState.abstractEval(stmt.getRightHandSide());
				post.setVariableValue(stmt.getLeftHandSide(), evaledRhs);
				return post;
			}
			
			@Override
			public AbstractState visit(RTLMemoryAssignment stmt) {
				ValuationState post = new ValuationState(iState);
				AbstractDomainElement evaledRhs = iState.abstractEval(stmt.getRightHandSide());
				RTLMemoryLocation m = stmt.getLeftHandSide();
				AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
				post.setMemoryValue(evaledAddress, m.getBitWidth(), evaledRhs);
				return post;
			}

			@Override
			public AbstractState visit(RTLAssume stmt) {
				if (stmt.getAssumption() instanceof RTLOperation) {
					RTLOperation operation = (RTLOperation)stmt.getAssumption(); 
					if (operation.getOperator() == Operator.EQUAL) {					
						RTLExpression lhs = operation.getOperands()[0];
						RTLExpression rhs = operation.getOperands()[1];
						AbstractDomainElement evaledRhs = iState.abstractEval(rhs);
						if (lhs instanceof RTLVariable) {
							ValuationState post = new ValuationState(iState);
							post.setVariableValue((RTLVariable)lhs, evaledRhs);
							return post;
						} else if (lhs instanceof RTLMemoryLocation) {
							ValuationState post = new ValuationState(iState);
							RTLMemoryLocation m = (RTLMemoryLocation)lhs;
							AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
							post.setMemoryValue(evaledAddress, m.getBitWidth(), evaledRhs);
							return post;
						}
					}
				}
				return iState;
			}

			@Override
			protected AbstractState visitDefault(RTLStatement stmt) {
				return iState;
			}

		}));

	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s,
			Precision precision, ReachedSet reached) {
		return Pair.create(s, precision);
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return CPAOperators.stopJoin(s, reached, precision);
	}

	@Override
	public AbstractState strengthen(AbstractState s,
			Iterable<AbstractState> otherStates, CFAEdge cfaEdge,
			Precision precision) {
		return s;
	}

}
