/*
 * PessimisticBasicBlockFactory.java - This file is part of the Jakstab project.
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
import java.util.Set;

import org.jakstab.Options;
import org.jakstab.Program;
import org.jakstab.analysis.AbstractState;
import org.jakstab.asm.AbsoluteAddress;
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
 * @author Johannes Kinder
 */
public class PessimisticBasicBlockFactory extends ResolvingTransformerFactory implements StateTransformerFactory {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(PessimisticBasicBlockFactory.class);

	@Override
	public Set<CFAEdge> getTransformers(final AbstractState a) {
		Program program = Program.getProgram();
		// First statement
		RTLStatement firstStmt = program.getStatement(a.getLocation());

		Set<RTLStatement> blockHeads = new FastSet<RTLStatement>();
		if (firstStmt instanceof RTLGoto) {
			// Multiple blocks
			blockHeads = gotoToAssumes(a, (RTLGoto)firstStmt);
		} else if (firstStmt instanceof RTLHalt) {
			// Nothing
			blockHeads = Collections.emptySet();
		} else {
			// Single Block
			blockHeads = new FastSet<RTLStatement>(firstStmt);
		}

		Set<CFAEdge> transformers = new FastSet<CFAEdge>();

		for (RTLStatement head : blockHeads) {

			BasicBlock block = new BasicBlock();
			RTLStatement stmt = head;

			while (true) {
				if (stmt instanceof RTLGoto || stmt instanceof RTLHalt) {
					break;
				} else {
					block.add(stmt);
					stmt = program.getStatement(stmt.getNextLabel());
				}
			}
			transformers.add(new CFAEdge(head.getLabel(), stmt.getLabel(), block));
		}

		saveNewEdges(transformers, a.getLocation());

		return transformers;
	}

	public Set<RTLStatement> gotoToAssumes(final AbstractState a, final RTLGoto stmt) {
		assert stmt.getCondition() != null;

		Set<RTLStatement> results = new FastSet<RTLStatement>();

		Set<Tuple<RTLNumber>> valuePairs = a.projectionFromConcretization(
				stmt.getCondition(), stmt.getTargetExpression());
		for (Tuple<RTLNumber> pair : valuePairs) {
			RTLNumber conditionValue = pair.get(0);
			RTLNumber targetValue = pair.get(1);
			Location nextLabel;
			// assume correct condition case 
			assert conditionValue != null;
			RTLExpression assumption = 
					ExpressionFactory.createEqual(stmt.getCondition(), conditionValue);
			if (conditionValue.equals(ExpressionFactory.FALSE)) {
				// assume (condition = false), and set next statement to fallthrough
				nextLabel = stmt.getNextLabel();
			} else {
				if (targetValue == null) {
					// if target could not be resolved, just leave the edge out for now
					logger.info(stmt.getLabel() + ": Cannot resolve target expression " + 
							stmt.getTargetExpression() + ". Continuing with unsound underapproximation.");
					logger.debug("State is: " + a);
					sound = false;
					unresolvedBranches.add(stmt.getLabel());
					if (Options.debug.getValue())
						throw new ControlFlowException(a, "Unresolvable control flow from " + stmt.getLabel());
					continue;
				} else {
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
			}
			assumption = assumption.evaluate(new Context());
			RTLAssume assume = new RTLAssume(assumption, stmt);
			assume.setLabel(stmt.getLabel());
			assume.setNextLabel(nextLabel);
			// Target address sanity check
			if (nextLabel.getAddress().getValue() < 10L) {
				logger.warn("Control flow from " + a.getLocation() + " reaches address " + nextLabel.getAddress() + "!");
			}

			results.add(assume);
		}
		return results;
	}

	@Override
	protected Set<CFAEdge> resolveGoto(AbstractState a, RTLGoto stmt) {
		throw new UnsupportedOperationException();
	}
}
