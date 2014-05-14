/*
 * YicesSolver.java - This file is part of the Jakstab project.
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
package org.jakstab.solver.yices;

import java.util.*;

import org.jakstab.rtl.expressions.*;
import org.jakstab.solver.Solver;
import org.jakstab.util.*;

public class YicesSolver extends Solver {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(YicesSolver.class);
	
	static final String yTrue = YicesWrapper.makeBVConstant(1, 1);
	static final String yFalse = YicesWrapper.makeBVConstant(1, 0);
	
	private YicesContext ctx;
	private YicesConversionVisitor yicesConversionVisitor;
	private Set<String> declaredVars;
	private Deque<Set<String>> declarationStack;
	
	public YicesSolver() {
		super();
		ctx = new YicesContext();
		yicesConversionVisitor = new YicesConversionVisitor();
		declaredVars = new HashSet<String>();
		declarationStack = new LinkedList<Set<String>>();
	}
	
	@Override
	public void addAssertion(RTLExpression f) {
		logger.debug(ctx + ": Adding " + f); 
		String formulaString = f.accept(yicesConversionVisitor);
		
		for (RTLVariable v : yicesConversionVisitor.getVariables()) {
			if (!declaredVars.contains(v.getName())) {
				declaredVars.add(v.getName());
				ctx.declareVariable(v);
			}
		}
		
		for (Pair<String, Integer> nondet : yicesConversionVisitor.getNondets()) {
			String v = nondet.getLeft();
			if (!declaredVars.contains(v)) {
				declaredVars.add(v);
				ctx.declareVariable(v, YicesWrapper.makeBVType(nondet.getRight()));
			}
		}
		
		for (int i=0; i <= yicesConversionVisitor.usedMemoryStates(); i++) {
			String memState = "m" + i;
			if (!declaredVars.contains(memState)  ) {
				ctx.readCommand("(define " + memState + "::(-> (bitvector 32) (bitvector 8)))");
				declaredVars.add(memState);
			}
		}
		
		// assert formula = 1  (use bitvector 1 as TRUE)
		//ctx.putAssertion(YicesWrapper.makeEquality(formulaString, yTrue));
		
		// Never generates inconsistent contexts this way?
		ctx.putRetractableAssertion(YicesWrapper.makeEquality(formulaString, yTrue));
	}

	@Override
	public boolean isSatisfiable() {
		boolean result = ctx.check();
		logger.debug(ctx + ": Check " + result); 
		return result;
	}

	@Override
	public void pop() {
		logger.debug(ctx + ": Pop"); 
		ctx.pop();
		declaredVars = declarationStack.pop();
	}

	@Override
	public void push() {
		logger.debug(ctx + ": Push"); 
		ctx.push();
		declarationStack.push(declaredVars);
		declaredVars = new HashSet<String>(declaredVars);
	}

}
