/*
 * ExpressionSimplifier.java - This file is part of the Jakstab project.
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
package org.jakstab.rtl.expressions;

import java.io.File;
import java.io.FileInputStream;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import org.jakstab.Options;
import org.jakstab.rtl.Context;
import org.jakstab.ssl.parser.SSLFunction;
import org.jakstab.ssl.parser.SSLLexer;
import org.jakstab.ssl.parser.SSLParser;
import org.jakstab.ssl.parser.SSLPreprocessor;
import org.jakstab.util.Logger;

/**
 * Template based expression simplifier. Reads a set of simplification rules from 
 * an SSL file when initialized.
 * 
 * @author Johannes Kinder
 */
public class ExpressionSimplifier {
	
	private final static Logger logger = Logger.getLogger(ExpressionSimplifier.class);
	private static ExpressionSimplifier instance;
	
	public final static ExpressionSimplifier getInstance() {
		if (instance == null) {
			try {
				instance = new ExpressionSimplifier();
			} catch (Exception e) {
				logger.fatal("Could not parse simplification rules!");
				e.printStackTrace();
				throw new RuntimeException(e);
			}
		}
		return instance;
	}
	
	private final RTLExpression[] patterns;
	private final RTLExpression[] results;
	
	private ExpressionSimplifier() throws Exception {
		// (x < y) | (x = y)   <->   x <= y
		File specFile = new File(Options.jakstabHome + "/ssl/simplifications.ssl");
		logger.info("Reading simplifications from " + specFile.getName() + ".");

		SSLLexer lex = new SSLLexer(new FileInputStream(specFile));
		SSLParser parser = new SSLParser(lex);
		SSLPreprocessor prep = new SSLPreprocessor();

		parser.start();
		prep.start(parser.getAST());

		Map<String,SSLFunction> instrPrototypes = prep.getInstructions();
		//registers = prep.getRegisters();
		//registers.removeAll(statusFlags);

		logger.debug("-- Got " + instrPrototypes.size() + " simplification groups.");
		
		Map<RTLExpression, RTLExpression> wholeMapping = new LinkedHashMap<RTLExpression, RTLExpression>();

		for (Map.Entry<String, SSLFunction> entry : instrPrototypes.entrySet()) {
			Map<RTLExpression, RTLExpression> mapping = prep.convertSimplificationTemplates(entry.getValue().getAST());
			wholeMapping.putAll(mapping);
		}
		
		patterns = wholeMapping.keySet().toArray(new RTLExpression[0]);
		results = wholeMapping.values().toArray(new RTLExpression[0]);
		
		logger.debug("Substitution rules:");
		for (int i=0; i<patterns.length; i++)
			logger.debug("  " + patterns[i] + " ----> " + results[i]);
	}
	
	/**
	 * Recursively tries to simplify the given expression and all its subexpressions,
	 * until no further simplifications can be made. 
	 * 
	 * @param e the expression to simplify
	 * @return a simplified version of the expression or the expression itself, if it could
	 *         not be simplified at all
	 */
	public RTLExpression simplify(RTLExpression e) {
		
		ExpressionVisitor<RTLExpression> simplificationVisitor = new ExpressionVisitor<RTLExpression>() {

			@Override
			public RTLExpression visit(RTLBitRange e) {
				RTLExpression result = applyTemplates(e);
				if (e != result)
					return result;
				RTLExpression eFirst = e.getFirstBitIndex().accept(this);
				RTLExpression eLast = e.getLastBitIndex().accept(this);
				RTLExpression eOp = e.getOperand().accept(this);
				if (eFirst != e.getFirstBitIndex() || eLast != e.getLastBitIndex() || eOp != e.getOperand())
					return ExpressionFactory.createBitRange(eOp, eFirst, eLast);
				else 
					return e;
			}

			@Override
			public RTLExpression visit(RTLConditionalExpression e) {
				RTLExpression result = applyTemplates(e);
				if (e != result)
					return result;
				RTLExpression eCond = e.getCondition().accept(this);
				RTLExpression eTrue = e.getTrueExpression().accept(this);
				RTLExpression eFalse = e.getFalseExpression().accept(this);
				if (eTrue != e.getTrueExpression() || eFalse != e.getFalseExpression())
					return ExpressionFactory.createConditionalExpression(eCond, eTrue, eFalse);
				else
					return e;
			}

			@Override
			public RTLExpression visit(RTLOperation e) {
				RTLExpression result = applyTemplates(e);
				if (e != result)
					return result;
				
				int count = e.getOperandCount();
				RTLExpression[] eOperands = new RTLExpression[count];
				boolean changed = false;
				for (int i = 0; i < count; i++) {
					eOperands[i] = e.getOperands()[i].accept(this);
					changed |= eOperands[i] != e.getOperands()[i];
				}
				if (changed)
					return ExpressionFactory.createOperation(e.getOperator(), eOperands);
				else
					return e;
			}

			@Override
			public RTLExpression visit(RTLSpecialExpression e) {
				RTLExpression result = applyTemplates(e);
				if (e != result)
					return result;
				
				int count = e.getOperandCount();
				RTLExpression[] eOperands = new RTLExpression[count];
				boolean changed = false;
				for (int i = 0; i < count; i++) {
					eOperands[i] = e.getOperands()[i].accept(this);
					changed |= eOperands[i] != e.getOperands()[i];
				}
				if (changed)
					return ExpressionFactory.createSpecialExpression(e.getOperator(), eOperands);
				else
					return e;
			}

			@Override
			public RTLExpression visit(RTLMemoryLocation e) {
				return e;
			}

			@Override
			public RTLExpression visit(RTLNondet e) {
				return e;
			}

			@Override
			public RTLExpression visit(RTLNumber e) {
				return e;
			}

			@Override
			public RTLExpression visit(RTLVariable e) {
				return e;
			}
			
		};
		
		int rounds = 0;
		RTLExpression old;
		do {
			old = e;
			e = e.accept(simplificationVisitor);
			// A cycle in the substitution rules could cause an infinite loop here!
			if (rounds++ > 50) {
				throw new RuntimeException("Over 50 iterations in substitution rules! Infinite loop?");
			}
			// Repeat while it's still changing
		} while (old != e);
		return e;
	}
	
	/**
	 * Substitute a single expression by trying all templates once. 
	 */
	private RTLExpression applyTemplates(RTLExpression e) {
		
		Map<RTLVariable, RTLExpression> bindings = new HashMap<RTLVariable, RTLExpression>(); 

		// Just go through all patterns and check for a match
		for (int i=0; i<patterns.length; i++) {
			if (match(e, patterns[i], bindings)) {
				// Success
				Context context = new Context();
				for (Map.Entry<RTLVariable, RTLExpression> binding : bindings.entrySet())
					context.substitute(binding.getKey(), binding.getValue());
				RTLExpression result = results[i].evaluate(context);
				//logger.debug("Simplified " + e + " to " + result);
				e = result;
			}
			bindings.clear();
		}

		return e;
	}

	/**
	 * Check whether an expression matches a pattern, and if so, under which binding of template variables to subexpressions. 
	 */
	private static boolean match(final RTLExpression expr, final RTLExpression pattern, final Map<RTLVariable, RTLExpression> bindings) {

		ExpressionVisitor<Boolean> matcher = new ExpressionVisitor<Boolean>() {
			
			// Needs to be set before calling accept. Holds the second parameter.
			private RTLExpression subExpr = expr;
			
			@Override
			public Boolean visit(RTLVariable e) {
				RTLExpression priorBinding = bindings.get(e);
				if (priorBinding == null) {
					bindings.put(e, subExpr);
					return true;
				} else {
					return priorBinding.equals(subExpr);				
				}
			}
			
			@Override
			public Boolean visit(RTLSpecialExpression e) {
				if (!(subExpr instanceof RTLSpecialExpression)) 
					return false;
				RTLSpecialExpression spSubExpr = (RTLSpecialExpression)subExpr;
				
				if (!spSubExpr.getOperator().equals(e.getOperator()))
					return false;
				
				if (spSubExpr.getOperandCount() != e.getOperandCount())
					return false;

				for (int i=0; i<e.getOperandCount(); i++) {
					subExpr = spSubExpr.getOperands()[i];
					if (!e.getOperands()[i].accept(this))
						return false;
				}
				return true;
			}
			
			@Override
			public Boolean visit(RTLOperation e) {
				
				// Negated variables can match constants 
				if (subExpr instanceof RTLNumber && e.getOperator() == Operator.NEG) {
					// Negate the number
					subExpr = ExpressionFactory.createNeg(subExpr);
					subExpr = subExpr.evaluate(new Context());
					assert (subExpr instanceof RTLNumber);
					// Match the expression within the negation to the negated number 
					return e.getOperands()[0].accept(this);
				}
				
				if (!(subExpr instanceof RTLOperation)) 
					return false;
				RTLOperation opSubExpr = (RTLOperation)subExpr;
				
				if (!opSubExpr.getOperator().equals(e.getOperator()))
					return false;
				
				int count = opSubExpr.getOperandCount();
				
				if (count != e.getOperandCount())
					return false;

				for (int i=0; i<count; i++) {
					subExpr = opSubExpr.getOperands()[i];
					if (!e.getOperands()[i].accept(this))
						return false;
				}
				return true;
			}
			
			@Override
			public Boolean visit(RTLNumber e) {
				if (!(subExpr instanceof RTLNumber))
					return false;
				RTLNumber other = (RTLNumber)subExpr;
				return other.longValue() == e.longValue();
			}
			
			@Override
			public Boolean visit(RTLNondet e) {
				throw new IllegalArgumentException("RTLNondet in simplification pattern!");
			}
			
			@Override
			public Boolean visit(RTLMemoryLocation e) {
				throw new IllegalArgumentException("RTLMemoryLocation in simplification pattern!");
			}
			
			@Override
			public Boolean visit(RTLConditionalExpression e) {
				if (!(subExpr instanceof RTLConditionalExpression)) 
					return false;
				RTLConditionalExpression cSubExpr = (RTLConditionalExpression)subExpr;

				subExpr = cSubExpr.getCondition();
				if (!e.getCondition().accept(this))
					return false;
				subExpr = cSubExpr.getTrueExpression();
				if (!e.getTrueExpression().accept(this))
					return false;
				subExpr = cSubExpr.getFalseExpression();
				if (!e.getFalseExpression().accept(this))
					return false;

				return true;
			}
			
			@Override
			public Boolean visit(RTLBitRange e) {
				if (!(subExpr instanceof RTLBitRange)) 
					return false;
				RTLBitRange bSubExpr = (RTLBitRange)subExpr;

				subExpr = bSubExpr.getFirstBitIndex();
				if (!e.getFirstBitIndex().accept(this))
					return false;
				subExpr = bSubExpr.getLastBitIndex();
				if (!e.getLastBitIndex().accept(this))
					return false;
				subExpr = bSubExpr.getOperand();
				if (!e.getOperand().accept(this))
					return false;

				return true;
			}
		};
		
		return pattern.accept(matcher);
	
	}
	
}
