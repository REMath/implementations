/*
 * AlternatingStateTransformerFactory.java - This file is part of the Jakstab project.
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
package org.jakstab.cfa;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.jakstab.Options;
import org.jakstab.Program;
import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.UnderApproximateState;
import org.jakstab.analysis.composite.DualCompositeState;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.cfa.CFAEdge.Kind;
import org.jakstab.rtl.Context;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;
import org.jakstab.util.Tuple;

/**
 * Provides state transformers without assumptions about procedures. Call instructions
 * are treated as push / jmp combinations and return instructions as indirect jumps. If
 * the target of a jump cannot be resolved, plug in values from an under-approximation
 * to create MUST edges.
 * 
 * For regular statements, produces MUST edges if there is an under-approximate witness.  
 * 
 * @author Johannes Kinder
 */
public class AlternatingStateTransformerFactory extends ResolvingTransformerFactory {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(AlternatingStateTransformerFactory.class);

	private Map<RTLNumber, RTLNumber> realToStub = new HashMap<RTLNumber, RTLNumber>();
	private Map<RTLNumber, RTLNumber> stubToReal = new HashMap<RTLNumber, RTLNumber>();
	private Program program = Program.getProgram();

	@Override
	public Set<CFAEdge> getTransformers(final AbstractState a) {
		RTLStatement stmt = Program.getProgram().getStatement(a.getLocation());

		Set<CFAEdge> transformers = stmt.accept(new DefaultStatementVisitor<Set<CFAEdge>>() {

			@Override
			protected Set<CFAEdge> visitDefault(RTLStatement stmt) {

				CFAEdge.Kind edgeKind = Kind.MAY;

				// If any under-approximate component is not BOT, then we have a witness
				// and this is a MUST edge.
				DualCompositeState dcs = (DualCompositeState)a;
				for (int i = 0; i < dcs.numComponents(); i++) {
					AbstractState componentState = dcs.getComponent(i);
					if (componentState instanceof UnderApproximateState &&
							!componentState.isBot()) {
						edgeKind = Kind.MUST;
						break;
					} 
				}

				return Collections.singleton(new CFAEdge(stmt.getLabel(), stmt.getNextLabel(), stmt, edgeKind));
			}

			@Override
			public Set<CFAEdge> visit(RTLGoto stmt) {
				assert stmt.getCondition() != null;
				Set<CFAEdge> results = new FastSet<CFAEdge>();


				if (Options.procedureAbstraction.getValue() == 2) {
					// Calls always get a fallthrough edge in optimistic mode
					if (stmt.getType() == RTLGoto.Type.CALL) {
						Location nextLabel = stmt.getNextLabel();

						if (Program.getProgram().getHarness().contains(stmt.getAddress())) {
							nextLabel = new Location(Program.getProgram().getHarness().getFallthroughAddress(stmt.getAddress()));
						}

						if (nextLabel != null) {
							RTLUnknownProcedureCall unknownCallEdge = new RTLUnknownProcedureCall(stmt);
							unknownCallEdge.setLabel(stmt.getLabel());
							unknownCallEdge.setNextLabel(nextLabel);
							results.add(new CFAEdge(stmt.getLabel(), nextLabel, unknownCallEdge));
							sound = false;
						}
					} 
					// Replace return with halt, since control flow passes over calls anyway
					else if (stmt.getType() == RTLGoto.Type.RETURN) {
						sound = false;
						return Collections.emptySet();
					}
				}

				DualCompositeState dcs = (DualCompositeState)a;

				// Add all edges from over-approximation
				for (Tuple<RTLNumber> pair : dcs.projectionFromConcretization(stmt.getCondition(), stmt.getTargetExpression())) {
					RTLNumber conditionValue = pair.get(0);
					RTLNumber targetValue = pair.get(1);
					Location nextLabel;
					// Start building the assume expression: assume correct condition case 
					assert conditionValue != null;
					RTLExpression assumption = 
							ExpressionFactory.createEqual(stmt.getCondition(), conditionValue);
					if (conditionValue.equals(ExpressionFactory.FALSE)) {
						// assume (condition = false), and set next statement to fallthrough
						nextLabel = stmt.getNextLabel();
					} else {
						if (targetValue == null) {
							logger.debug("No value from MAY-analysis at " + stmt.getLabel());
							sound = false;
							unresolvedBranches.add(stmt.getLabel());
							continue;
						}
						// assume (condition = true AND targetExpression = targetValue)
						assumption = ExpressionFactory.createAnd(
								assumption,
								ExpressionFactory.createEqual(
										stmt.getTargetExpression(),
										targetValue)
								);
						// set next label to jump target
						nextLabel = new Location(new AbsoluteAddress(targetValue));
					}
					assumption = assumption.evaluate(new Context());
					RTLAssume assume = new RTLAssume(assumption, stmt);
					assume.setLabel(stmt.getLabel());
					assume.setNextLabel(nextLabel);
					// Target address sanity check
					if (nextLabel.getAddress().getValue() < 10L) {
						logger.warn("Control flow from " + stmt.getLabel() + " reaches address " + nextLabel.getAddress() + "!");
					}

					results.add(new CFAEdge(assume.getLabel(), assume.getNextLabel(), assume, Kind.MAY));
				}

				// Add all edges from under-approximation

				for (Tuple<RTLNumber> pair : dcs.projection(stmt.getCondition(), stmt.getTargetExpression())) {
					RTLNumber conditionValue = pair.get(0);
					RTLNumber targetValue = pair.get(1);
					Location nextLabel;
					// Start building the assume expression: assume correct condition case 
					assert conditionValue != null;
					RTLExpression assumption = 
							ExpressionFactory.createEqual(stmt.getCondition(), conditionValue);
					if (conditionValue.equals(ExpressionFactory.FALSE)) {
						// assume (condition = false), and set next statement to fallthrough
						nextLabel = stmt.getNextLabel();
					} else {
						assert targetValue != null;

						// Translate real library addresses into stub addresses. Necessary because the static analysis component 
						// does not know about concrete import addresses, so it uses a stub system.
						if (!isProgramAddress(targetValue)) {
							logger.debug(dcs.getLocation() + ": Jumping out of module to " + targetValue.toHexString());

							// Attempt to map this out-of-module location to a stub
							if (realToStub.containsKey(targetValue)) {
								// If we saw this concrete address before, replace it by the known stub
								logger.debug("Replacing concrete target " + targetValue.toHexString() + " with stub to " + program.getSymbolFor(new AbsoluteAddress(realToStub.get(targetValue))));
								targetValue = realToStub.get(targetValue);
							} else {

								// Check the statically produced edges for one that is not yet mapped to a concrete address.
								// If the over-approximation resolved an import to a stub, it's going to be contained.
								boolean foundStub = false;
								for (CFAEdge e : results) {
									RTLNumber staticTarget = e.getTarget().getAddress().toNumericConstant();
									if (!isProgramAddress(staticTarget) && !stubToReal.containsKey(staticTarget)) {
										// Take the first one that's neither taken nor in the program
										// TODO: This could map the wrong addresses in some (hopefully) rare cases depending on analysis order
										stubToReal.put(staticTarget, targetValue);
										realToStub.put(targetValue, staticTarget);
										targetValue = staticTarget;
										foundStub = true;
										break;
									}
								}

								if (!foundStub) {
									// If we have not found anything suitable, we need to create a new stub
									// FIXME: The new stub will likely have incorrect stack height adjustment.
									//        We should extract that information from the trace.

									logger.info(dcs.getLocation() + ": Creating new stub for unknown function at " + targetValue.toHexString());
									RTLNumber stubTarget = Program.getProgram().getProcAddress("JAK_UNKNOWN", "proc" + targetValue.toHexString()).toNumericConstant();
									stubToReal.put(stubTarget, targetValue);
									realToStub.put(targetValue, stubTarget);
									targetValue = stubTarget;
								}
							}

						}

						// assume (condition = true AND targetExpression = targetValue)
						assumption = ExpressionFactory.createAnd(
								assumption,
								ExpressionFactory.createEqual(
										stmt.getTargetExpression(),
										targetValue)
								);
						// set next label to jump target
						nextLabel = new Location(new AbsoluteAddress(targetValue));
					}
					assumption = assumption.evaluate(new Context());
					RTLAssume assume = new RTLAssume(assumption, stmt);
					assume.setLabel(stmt.getLabel());
					assume.setNextLabel(nextLabel);

					results.add(new CFAEdge(assume.getLabel(), assume.getNextLabel(), assume, Kind.MUST));
				}

				return results;
			}

			@Override
			public Set<CFAEdge> visit(RTLHalt stmt) {
				return Collections.emptySet();
			}

		});		

		saveNewEdges(transformers, a.getLocation());

		return transformers;
	}

	@Override
	protected void saveNewEdges(Set<CFAEdge> transformers, Location l) {
		// Make sure we only add new edges. Edges are mutable so we cannot just implement
		// hashCode and equals and add everything into a HashSet.
		for (CFAEdge edge : transformers) {
			boolean found = false;
			// We check for this in the loop, because transformers may contain duplicate edges
			// that only differ in their kind. So we check them against each other for upgrading
			if (outEdges.containsKey(l)) {
				for (CFAEdge existingEdge : outEdges.get(l)) {
					if (existingEdge.getTarget().equals(edge.getTarget())) {

						// There is an edge with the same target
						found = true;

						// Different kinds of edges
						if (!existingEdge.getKind().equals(edge.getKind())) {

							if (existingEdge.getKind().lessOrEqual(edge.getKind())) {
								// If the new kind is greater than the existing, upgrade to new kind
								//logger.debug("Upgrading existing edge " + existingEdge + " from " + existingEdge.getKind() + " to " + edge.getKind());
								existingEdge.setKind(edge.getKind());
							} else if (edge.getKind().lessOrEqual(existingEdge.getKind())) {
								// If the existing kind is greater than the new one, upgrade new one
								//logger.debug("Upgrading new edge " + edge + " from " + edge.getKind() + " to " + existingEdge.getKind());
								edge.setKind(existingEdge.getKind());
							} else {
								// Incomparable edge kinds cannot happen with current logic
								assert false : "Incomparable edge kinds!";
							}
						}

						//break;
					}
				}
			}
			if (!found) outEdges.put(l,  edge);
		}

	}

	@Override
	protected Set<CFAEdge> resolveGoto(AbstractState a, RTLGoto stmt) {
		throw new UnsupportedOperationException("Not used");
	}

	private boolean isProgramAddress(RTLNumber n) {
		return program.getModule(new AbsoluteAddress(n.longValue())) != null;
	}

}
