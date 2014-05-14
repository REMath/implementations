/*
 * SemiOptimisticStateTransformerFactory.java - This file is part of the Jakstab project.
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

import java.util.Set;

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
 * Provides CFAEdges using a medium level of assumptions. If the target of a 
 * call instruction cannot be resolved, assumes that the call returns to the
 * instruction following the callsite. 
 * 
 * @author Johannes Kinder
 */
public class SemiOptimisticStateTransformerFactory extends ResolvingTransformerFactory {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(SemiOptimisticStateTransformerFactory.class);
	
	@Override
	public Set<CFAEdge> resolveGoto(final AbstractState a, final RTLGoto stmt) {

		assert stmt.getCondition() != null;

		Set<CFAEdge> results = new FastSet<CFAEdge>();

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

					if (stmt.getType() == RTLGoto.Type.CALL) {
						// if it's a call TOP, add an unknown call edge if we're allowing unsound analysis
						RTLUnknownProcedureCall unknownCallEdge = new RTLUnknownProcedureCall(stmt);
						unknownCallEdge.setLabel(stmt.getLabel());
						unknownCallEdge.setNextLabel(stmt.getNextLabel());
						results.add(new CFAEdge(stmt.getLabel(), stmt.getNextLabel(), unknownCallEdge));
						logger.info(stmt.getLabel() + ": Cannot resolve target expression " + 
								stmt.getTargetExpression() + " of call. Adding unknown call edge.");
						logger.debug("State is: " + a);
					} else {
						// if target could not be resolved, just leave the edge out for now
						logger.info(stmt.getLabel() + ": Cannot resolve target expression " + 
								stmt.getTargetExpression() + ". Continuing with unsound underapproximation.");
						logger.debug("State is: " + a);
						unresolvedBranches.add(stmt.getLabel());
					}
					sound = false;

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
			results.add(new CFAEdge(stmt.getLabel(), nextLabel, assume));
		}
		return results;
	}

}
