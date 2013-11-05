/*
 * ExpressionSubstitution.java - This file is part of the Jakstab project.
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
package org.jakstab.transformation;

import org.jakstab.Program;
import org.jakstab.analysis.*;
import org.jakstab.analysis.substitution.ExpressionSubstitutionAnalysis;
import org.jakstab.analysis.substitution.SubstitutionElement;
import org.jakstab.analysis.substitution.SubstitutionState;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.rtl.statements.RTLSkip;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class ExpressionSubstitution implements CFATransformation {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger
			.getLogger(ExpressionSubstitution.class);
	
	private Program program;
	private CPAAlgorithm cpaAlgo;
	
	public ExpressionSubstitution(Program program) {
		this.program = program;
		cpaAlgo = CPAAlgorithm.createForwardAlgorithm(program, new ExpressionSubstitutionAnalysis());
	}
	
	public static void substituteCFAEdge(CFAEdge edge, SubstitutionState s) {
		RTLStatement stmt = (RTLStatement)edge.getTransformer();
		RTLStatement newStmt = substituteStatement(stmt, s);
		if (newStmt != stmt)
			edge.setTransformer(newStmt);
	}
	
	public static RTLStatement substituteStatement(RTLStatement stmt, SubstitutionState s) {
		Context substCtx = new Context();
		for (RTLVariable v : stmt.getUsedVariables()) {
			SubstitutionElement el = s.getValue(v);
			if (!el.isTop()) {
				substCtx.addAssignment(v, el.getExpression());
			}
		}
		if (!substCtx.getAssignments().isEmpty()) {
			//logger.info("Old stmt: " + stmt);
			RTLStatement newStmt = stmt.copy().evaluate(substCtx);
			//logger.info("New stmt: " + newStmt);
			if (newStmt != null) {
				return newStmt.evaluate(new Context());
			} else {
				RTLSkip skip = new RTLSkip();
				skip.setLabel(stmt.getLabel());
				skip.setNextLabel(stmt.getNextLabel());
				return skip;
			}
		}
		return stmt;
	}

	@Override
	public void run() {
		
		logger.info("Starting expression substitution.");
		long startTime = System.currentTimeMillis();
		
		cpaAlgo.run();
		ReachedSet exprSubstStates = cpaAlgo.getReachedStates().select(1);
		
		for (CFAEdge edge : program.getCFA()) {
			assert exprSubstStates.where(edge.getSource()).size() == 1;
			SubstitutionState s = (SubstitutionState)exprSubstStates.where(edge.getSource()).iterator().next();
			substituteCFAEdge(edge, s);
		}
		
		long endTime = System.currentTimeMillis();
		logger.verbose("Finished after " + (endTime - startTime) + "ms.");
	}
	
	public void stop() {
		cpaAlgo.stop();
	}
}
