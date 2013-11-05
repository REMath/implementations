/*
 * CompositeProgramAnalysis.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.composite;

import java.util.Collections;
import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.JOption;
import org.jakstab.analysis.*;
import org.jakstab.analysis.callstack.CallStackAnalysis;
import org.jakstab.analysis.location.BackwardLocationAnalysis;
import org.jakstab.analysis.location.LocationAnalysis;
import org.jakstab.analysis.substitution.ExpressionSubstitutionAnalysis;
import org.jakstab.analysis.substitution.SubstitutionState;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.statements.*;
import org.jakstab.transformation.ExpressionSubstitution;
import org.jakstab.util.*;

/**
 * @author Johannes Kinder
 */
public class CompositeProgramAnalysis implements ConfigurableProgramAnalysis {

	public static void register(AnalysisProperties p) {
		p.setName("Composite Program Analysis");
		p.setDescription("Default composition of multiple CPAs.");
	}
	
	public static JOption<Boolean> ignoreCallingContext = JOption.create("ignore-context", "Allow merging of different calling contexts even with call stack analysis enabled.");
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(CompositeProgramAnalysis.class);
	
	protected final ConfigurableProgramAnalysis[] cpas;
	
	protected int expressionSubstitutionIndex;
	protected int callStackAnalysisIndex;
	
	public CompositeProgramAnalysis(BackwardLocationAnalysis locationAnalysis) {
		cpas = new ConfigurableProgramAnalysis[1];
		cpas[0] = locationAnalysis;
	}

	public CompositeProgramAnalysis(LocationAnalysis locationAnalysis, 
			ConfigurableProgramAnalysis... otherCPAs) {
		cpas = new ConfigurableProgramAnalysis[otherCPAs.length + 1];
		cpas[0] = locationAnalysis;
		System.arraycopy(otherCPAs, 0, cpas, 1, otherCPAs.length);
		expressionSubstitutionIndex = -1;
		callStackAnalysisIndex = -1;
		for (int i = 1; i < cpas.length; i++)
			if (cpas[i] instanceof ExpressionSubstitutionAnalysis) {
				expressionSubstitutionIndex = i;
			} else if (cpas[i] instanceof CallStackAnalysis) {
				callStackAnalysisIndex = i;
			}
	}

	@Override
	public AbstractState initStartState(Location label) {
		AbstractState[] components = new AbstractState[cpas.length];
		for (int i=0; i<cpas.length; i++)
			components[i] = cpas[i].initStartState(label);
		return createCompositeState(components);
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2, Precision precision) {
		// Cartesian merge
		CompositeState cs1 = (CompositeState)s1;
		CompositeState cs2 = (CompositeState)s2;
		AbstractState[] mergedComponents = new AbstractState[cpas.length];
		
		// If analysis is context sensitive, never merge different calling contexts
		if (callStackAnalysisIndex >= 0 && !ignoreCallingContext.getValue().booleanValue()) {
			if (!cs1.getComponent(callStackAnalysisIndex).equals(cs2.getComponent(callStackAnalysisIndex))) {
				return CPAOperators.mergeSep(cs1, cs2, precision);
			}
		}
		
		for (int i=0; i<cpas.length; i++) {
			mergedComponents[i] = cpas[i].merge(
					cs1.getComponent(i), 
					cs2.getComponent(i), 
					((CompositePrecision)precision).getComponent(i)
					);
		}
		return createCompositeState(mergedComponents);
	}

	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge, Precision precision) {

		// Handle single statement transformers
		if (cfaEdge.getTransformer() instanceof RTLStatement) {
			return postSingleStatement(state, cfaEdge, precision);
		} 
		// Basic Block transformers
		else if (cfaEdge.getTransformer() instanceof BasicBlock) {
			
			// Set of states we got from the last invocation of post
			Set<AbstractState> lastSuccs = new FastSet<AbstractState>();
			lastSuccs.add(state);
			// Iterate over all statements in the basic block
			for (RTLStatement stmt : (BasicBlock)cfaEdge.getTransformer()) {
				// Set of new states for this statement. 
				Set<AbstractState> newSuccs = new FastSet<AbstractState>();
				// Grow set of new states through post over each of the old states
				for (AbstractState lastState : lastSuccs) {
					try {
						newSuccs.addAll(postSingleStatement(
								lastState, 
								new CFAEdge(stmt.getLabel(), stmt.getNextLabel(), stmt), 
								precision));
					} catch (UnknownPointerAccessException e) {
						e.setState(lastState);
						throw e;
					}
				}
				lastSuccs = newSuccs;
			}
			
			return lastSuccs;
			
		} else throw new UnsupportedOperationException("Transformers of class " + cfaEdge.getTransformer().getClass().getName() + " not supported!");
	}
	
	protected Set<AbstractState> postSingleStatement(AbstractState state, CFAEdge cfaEdge, Precision precision) {
		CompositeState c = (CompositeState)state;
		
		// If expression substitution is active, substitute expression in CFA edge passed to post methods
		CFAEdge origCFAEdge = cfaEdge;
		if (expressionSubstitutionIndex >= 0) {
			cfaEdge = new CFAEdge(cfaEdge.getSource(), cfaEdge.getTarget(), ExpressionSubstitution.substituteStatement(
					((RTLStatement)cfaEdge.getTransformer()), (SubstitutionState)c.getComponent(expressionSubstitutionIndex)));
		}
		
		// Check for requests for debug messages. Currently only used for dumping
		// registered driver callbacks. 
		RTLStatement stmt = (RTLStatement)cfaEdge.getTransformer();
		if (stmt instanceof RTLDebugPrint) {
			RTLDebugPrint debug = (RTLDebugPrint)stmt;
			Set<Tuple<RTLNumber>> values = c.projectionFromConcretization(debug.getExpression());
			boolean generatedOutput = false;
			for (Tuple<RTLNumber> tuple : values) {
				// Only print DebugMsg if there is a concrete value other than 0
				if (tuple.get(0) != null && tuple.get(0).intValue() != 0) {
					logger.info("DEBUG: " + debug.getMessage() + " " + tuple);
					logger.debug("State is: " + c);
					generatedOutput = true;
				}
			}
			
			// Print informational message in any case (can be used for signaling)
			if (!generatedOutput)
				logger.info("DEBUG: Reached statement at " + cfaEdge.getSource());
			
		}
		// Check assertions in the concretization of the composite state
		else if (stmt instanceof RTLAssert) {
			Set<Tuple<RTLNumber>> cAssertionResult = state.projectionFromConcretization(((RTLAssert)stmt).getAssertion());
			if (cAssertionResult.size() > 1) {
				logger.error("Found possible assertion violation at " + state.getLocation() + "! " + stmt + " evaluated to " + Characters.TOP + " in state:");
				logger.error(state);
				//if (Options.errorTrace)
				throw new AssertionViolationException(state, "Assertion " + stmt + " might have failed!");
			} else if (cAssertionResult.iterator().next().get(0).equals(ExpressionFactory.FALSE)) {
				logger.error("Found assertion violation at " + state.getLocation() + "! " + stmt + " failed in state:");
				logger.error(state);
				//if (Options.errorTrace)
				throw new AssertionViolationException(state, "Assertion " + stmt + " failed!");
			}
		}

		// Now pass transformer down to individual CPAs		
		Tuple<Set<AbstractState>> sComponents = new Tuple<Set<AbstractState>>(cpas.length);
		for (int i=0; i<cpas.length; i++) {
			// For forward expression substitution, use the original cfa edge, 
			// it takes care of substitutions itself. Also for CallStackAnalysis.
			Set<AbstractState> succs;
			if (i == expressionSubstitutionIndex || i == callStackAnalysisIndex) {
				succs = cpas[i].post(c.getComponent(i), origCFAEdge, 
					((CompositePrecision)precision).getComponent(i));
			} else {
				succs = cpas[i].post(c.getComponent(i), cfaEdge, 
						((CompositePrecision)precision).getComponent(i));
			}
			// If one analysis reports no successors, there is no composite successor
			if (succs.isEmpty()) return Collections.emptySet();
			sComponents.set(i, succs);
		}
		//return createCompositeState(sComponents);
		Set<Tuple<AbstractState>> crossp = Sets.crossProduct(sComponents);
		Set<AbstractState> succ = new FastSet<AbstractState>();
		
		for (Tuple<AbstractState> tuple : crossp) {
			// Perform strengthening
			for (int i=0; i<cpas.length; i++) {
				AbstractState s1 = tuple.get(i);
				s1 = cpas[i].strengthen(s1, tuple, cfaEdge, precision);
				if (s1 == null || s1.isBot())
					continue;
				tuple.set(i, s1);
			}
			
			succ.add(createCompositeState(tuple));
		}
		return succ;
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s, Precision precision, ReachedSet reached) {
		CompositeState cs = (CompositeState)s;
		AbstractState[] newComponents = new AbstractState[cpas.length];
		Precision[] newPrecComponents = new Precision[cpas.length];
		
		for (int i=0; i<cpas.length; i++) {
			 Pair<AbstractState, Precision> pair = cpas[i].prec(cs.getComponent(i), 
					((CompositePrecision)precision).getComponent(i),
					reached.select(i).where(0, cs.getComponent(0)));
			 newComponents[i] = pair.getLeft();
			 newPrecComponents[i] = pair.getRight();
		}
		
		return Pair.create((AbstractState)(createCompositeState(newComponents)),
				(Precision)(new CompositePrecision(newPrecComponents)));
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {

		CompositeState cs = (CompositeState)s;

		// cartesian stop
		for (int i=0; i<cpas.length; i++) {
			if (!cpas[i].stop(
					cs.getComponent(i), 
					reached.select(i).where(0, cs.getComponent(0)), 
					((CompositePrecision)precision).getComponent(i)
			)) {
				//logger.error(cs.getComponent(i).getClass().getSimpleName() + " says continue");
				return false;
			}
		}
		return true;

		/*			
			// stop-sep
			for (AbstractState a : reached.where(0, cs.getComponent(0))) {
				if (s.lessOrEqual(a)) {
					return true;
				}
			}
			return false;
		}
		 */
	}

	@Override
	public Precision initPrecision(Location location, StateTransformer transformer) {
		Precision[] precisions = new Precision[cpas.length];
		for (int i=0; i<cpas.length; i++) {
			precisions[i] = cpas[i].initPrecision(location, transformer);
		}
		return new CompositePrecision(precisions);
	}

	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
			CFAEdge cfaEdge, Precision precision) {
		throw new UnsupportedOperationException("Strengthening should never be called on composite analysis!");
	}
	
	protected CompositeState createCompositeState(Tuple<AbstractState> tuple) {
		AbstractState[] components = new AbstractState[tuple.size()];
		for (int i=0; i<components.length; i++) {
			components[i] = tuple.get(i);
		}
		return createCompositeState(components);
	}

	protected CompositeState createCompositeState(AbstractState[] components) {
		return new CompositeState(components);
	}

}
