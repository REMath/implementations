/*
 * IntervalAnalysis.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.intervals;

import java.util.*;

import org.jakstab.AnalysisProperties;
import org.jakstab.Program;
import org.jakstab.analysis.*;
import org.jakstab.analysis.explicit.BasedNumberElement;
import org.jakstab.analysis.explicit.BasedNumberValuation;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.*;
import org.jakstab.util.MapMap.EntryIterator;

/**
 * A reduced interval congruence analysis with regioned memory. Inspired by
 * Codesurfer's VSA domain. 
 * 
 * @author Johannes Kinder
 */
public class IntervalAnalysis implements ConfigurableProgramAnalysis {

	public static void register(AnalysisProperties p) {
		p.setShortHand('i');
		p.setName("Interval analysis");
		p.setDescription("Compute strided intervals with region information.");
		p.setExplicit(true);
	}

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(IntervalAnalysis.class);
	private AbstractValueFactory<IntervalElement> valueFactory;

	public IntervalAnalysis() {
		valueFactory = new IntervalElementFactory();
	}

	@Override
	public Precision initPrecision(Location location, StateTransformer transformer) {
		return new IntervalPrecision();
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#initStartState(org.jakstab.cfa.Location)
	 */
	@Override
	public AbstractState initStartState(Location label) {
		//IntervalState init = new IntervalState();
		/*init.setValue(Program.getProgram().getArchitecture().stackPointer(), 
				new IntervalElement(MemoryRegion.STACK, 0, 0, 0, 32));*/
		//return init;
		return new ValuationState(valueFactory);
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#merge(org.jakstab.analysis.AbstractState, org.jakstab.analysis.AbstractState)
	 */
	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2, Precision precision) {
		
		// Widen s2 towards s1.
		//return ((IntervalState)s2).widen((IntervalState)s1);
		
		if (s2.isTop() || s1.isBot()) return s2;
		if (s1.isTop()) return s1;
		
		ValuationState current = (ValuationState)s2;
		ValuationState towards = (ValuationState)s1;

		ValuationState widenedState = new ValuationState(valueFactory);
		// Widen variable valuations
		for (Iterator<Map.Entry<RTLVariable,AbstractDomainElement>> entryIt = current.variableIterator(); entryIt.hasNext();) {
			Map.Entry<RTLVariable,AbstractDomainElement> entry = entryIt.next();
			RTLVariable var = entry.getKey();
			IntervalElement v = (IntervalElement)entry.getValue();
			widenedState.setVariableValue(var, v.widen((IntervalElement)towards.getVariableValue(var)));
		}
		
		// Widen memory
		for (EntryIterator<MemoryRegion, Long, AbstractDomainElement> entryIt = current.storeIterator(); entryIt.hasEntry(); entryIt.next()) {
			MemoryRegion region = entryIt.getLeftKey();
			Long offset = entryIt.getRightKey();
			IntervalElement v = (IntervalElement)entryIt.getValue();
			int bitWidth = v.getBitWidth();
			widenedState.setMemoryValue(region, offset, bitWidth, 
					v.widen((IntervalElement)towards.getMemoryValue(region, offset, bitWidth)));
		}
		
		return widenedState;

	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#post(org.jakstab.analysis.AbstractState, org.jakstab.analysis.StateTransformer, org.jakstab.analysis.Precision)
	 */
	@Override
	public Set<AbstractState> post(final AbstractState state, CFAEdge cfaEdge, Precision precision) {

		final RTLStatement statement = (RTLStatement)cfaEdge.getTransformer();
		final ValuationState iState = (ValuationState)state;

		return Collections.singleton(statement.accept(new DefaultStatementVisitor<AbstractState>() {
			
			@Override
			protected AbstractState visitDefault(RTLStatement stmt) {
				return state;
			}

			@Override
			public AbstractState visit(RTLVariableAssignment stmt) {
				ValuationState post = new ValuationState(iState);
				Writable lhs = stmt.getLeftHandSide();
				RTLExpression rhs = stmt.getRightHandSide();
				AbstractDomainElement evaledRhs = iState.abstractEval(rhs);
				post.setVariableValue((RTLVariable)lhs, evaledRhs);
				return post;
			}
			
			@Override
			public AbstractState visit(RTLMemoryAssignment stmt) {
				ValuationState post = new ValuationState(iState);
				RTLMemoryLocation m = stmt.getLeftHandSide();
				RTLExpression rhs = stmt.getRightHandSide();
				AbstractDomainElement evaledRhs = iState.abstractEval(rhs);
				AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
				post.setMemoryValue(evaledAddress, m.getBitWidth(), evaledRhs);
				return post;
			}

			@Override
			public AbstractState visit(RTLAssume stmt) {
				
				ValuationState post = new ValuationState(iState);
				
				RTLExpression assumption = stmt.getAssumption();
				
				// TODO: implement assume
				
				if (assumption instanceof RTLOperation) {
					RTLOperation op = (RTLOperation)assumption;
					switch (op.getOperator()) {
					case UNSIGNED_LESS_OR_EQUAL:
						RTLExpression lhs = op.getOperands()[0];
						RTLExpression rhs = op.getOperands()[1];
						IntervalElement evaledLhs = (IntervalElement)iState.abstractEval(lhs);
						IntervalElement evaledRhs = (IntervalElement)iState.abstractEval(rhs);

						if (evaledRhs.getLeft() >= 0) {
							IntervalElement uLessInt = new IntervalElement(
									evaledRhs.getRegion(), 0, 
									evaledRhs.getRight(), 1, evaledLhs.getBitWidth()
							);
							// TODO: Implement meet for interval elements for optimal result
							// uLessInt = uLessInt.meet(evaledLhs);
							// if uLessInt.isBot() return Collections.emptySet();
							// cheap but sound solution for now: only use new interval if it has less elements
							if (uLessInt.size() < evaledLhs.size()) {
								if (lhs instanceof RTLVariable) {
									post.setVariableValue((RTLVariable)lhs, uLessInt);
								} else if (lhs instanceof RTLMemoryLocation) {
									RTLMemoryLocation m = (RTLMemoryLocation)lhs;
									AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
									post.setMemoryValue(evaledAddress, m.getBitWidth(), uLessInt);
								}
							}
						}
						break;
					}
				}

				return post;
			}

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
				
				IntervalElement basePointer = new IntervalElement(newRegion, 
						ExpressionFactory.createNumber(0, 32));
				
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
			public AbstractState visit(RTLHavoc stmt) {
				ValuationState post = new ValuationState(iState);
				
				// Only create a single state with the havoc range, since this analysis
				// is not path sensitive
				post.setVariableValue(stmt.getVariable(), 
						//new IntervalElement(ExpressionFactory.getInstance().createNumber(0, stmt.getVariable().getBitWidth()), 
								//(RTLNumber)stmt.getMaximum()));
						new IntervalElement(MemoryRegion.GLOBAL, 0, ((RTLNumber)stmt.getMaximum()).longValue(), 1, 
								stmt.getVariable().getBitWidth())
						);
				
				return post;
			}

			@Override
			public AbstractState visit(RTLUnknownProcedureCall stmt) {
				ValuationState post = new ValuationState(iState);
				for (RTLVariable var : stmt.getDefinedVariables()) {
					post.setVariableValue(var, IntervalElement.getTop(var.getBitWidth()));
				}
				post.setMemoryValue(IntervalElement.getTop(Program.getProgram().getArchitecture().getAddressBitWidth()), 
						32, IntervalElement.getTop(32));
				return post;
			}
			
		}));
	}

	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
			CFAEdge cfaEdge, Precision precision) {

		ValuationState state = (ValuationState)s;
		ValuationState strengthenedState = null;

		for (AbstractState t : otherStates) {
			// TODO: Does not work correctly if BoundedAddressTracking returns more than
			// 		 one successor state.
			if (t instanceof BasedNumberValuation) {
				BasedNumberValuation exState = (BasedNumberValuation)t;
				for (Map.Entry<RTLVariable, BasedNumberElement> entry : 
					exState.getVariableValuation()) {
					RTLVariable var = entry.getKey();
					BasedNumberElement exVal = entry.getValue();
					if (exVal.isTop() || exVal.isNumberTop())
						continue;
					if (state.getVariableValue(var).isTop()) {
						if (strengthenedState == null) {
							strengthenedState = new ValuationState(state);
						}
						strengthenedState.setVariableValue(var, 
								new IntervalElement(exVal.getRegion(),
								exVal.getNumber()));
						//logger.debug("Strengthened state " + state.getIdentifier() + 
						//		" by setting " + var + " to " + state.getValue(var));
					}
				}
			}
		}
		
		return strengthenedState == null ? state : strengthenedState;
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

	
	private RTLExpression addClause(RTLExpression formula, RTLExpression clause) {
		if (formula != null) {
			return ExpressionFactory.createAnd(formula, clause);
		} else {
			return clause;
		}
	}
	
	public RTLExpression getStateFormula(ValuationState state) {
		RTLExpression result = null;
		
		for (Iterator<Map.Entry<RTLVariable,AbstractDomainElement>> entryIt = state.variableIterator(); entryIt.hasNext();) {
			Map.Entry<RTLVariable,AbstractDomainElement> entry = entryIt.next();
			RTLVariable var = entry.getKey();
			IntervalElement interval = (IntervalElement)entry.getValue();
			
			if (interval.size() == 1) {
				result = addClause(result, ExpressionFactory.createEqual(
						var, ExpressionFactory.createNumber(interval.getLeft(), var.getBitWidth())));
			} else {
				if (!interval.leftOpen()) {
					result = addClause(result, ExpressionFactory.createLessOrEqual(
							ExpressionFactory.createNumber(interval.getLeft(), var.getBitWidth()), var));
				}

				if (!interval.rightOpen()) {
					result = addClause(result, ExpressionFactory.createLessOrEqual(
							var, ExpressionFactory.createNumber(interval.getRight(), var.getBitWidth())));
				}
			}
		}
		
		if (result == null) {
			result = ExpressionFactory.TRUE;
		}

		return result;
	}

}
