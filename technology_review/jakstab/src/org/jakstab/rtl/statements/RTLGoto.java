/*
 * RTLGoto.java - This file is part of the Jakstab project.
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

package org.jakstab.rtl.statements;

import java.util.Collections;
import java.util.Set;

import org.jakstab.Program;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.loader.ExecutableImage;
import org.jakstab.rtl.*;
import org.jakstab.rtl.expressions.*;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.Logger;
import org.jakstab.util.FastSet;

/**
 * Guarded goto statements, only appear during disassembly, not in CFAs, and do not need to 
 * be handled during analyses. These are translated into assumes by StateTransformerFactories.
 * 
 * @author Johannes Kinder
 */
public class RTLGoto extends AbstractRTLStatement implements RTLStatement {

	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(RTLGoto.class);
	
	private RTLExpression condition;
	private RTLExpression targetExpression;
	public enum Type {CALL, RETURN, JUMP, STRING_LENGTH_CHECK, REPEAT}
	private Type type;
	
	public RTLGoto(RTLExpression targetExpr, Type type) {
		this(targetExpr, ExpressionFactory.TRUE, type);
	}
	
	public RTLGoto(RTLExpression targetExpr, RTLExpression condition, Type type) {
		this.condition = condition;
		this.targetExpression = targetExpr;
		this.type = type;
	}
	
	/**
	 * @return the targetExpression
	 */
	public RTLExpression getTargetExpression() {
		return targetExpression;
	}

	@Override
	public RTLStatement evaluate(Context context) {
		invalidateCache();
		condition = condition.evaluate(context);
		if (targetExpression != null)
			targetExpression = targetExpression.evaluate(context);
		return this;
	}
	
	@Override
	protected SetOfVariables initDefinedVariables() {
		return SetOfVariables.EMPTY_SET;
	}
	
	@Override
	protected SetOfVariables initUsedVariables() {
		if (targetExpression == null) return SetOfVariables.EMPTY_SET;
		else {
			SetOfVariables usedVars = new SetOfVariables(targetExpression.getUsedVariables());
			usedVars.addAll(condition.getUsedVariables());
			return usedVars;
		}
	}
	
	@Override
	protected Set<RTLMemoryLocation> initUsedMemoryLocations() {
		if (targetExpression == null) return Collections.emptySet();
		else {
			Set<RTLMemoryLocation> usedMemory = new FastSet<RTLMemoryLocation>();
			usedMemory.addAll(targetExpression.getUsedMemoryLocations());
			usedMemory.addAll(condition.getUsedMemoryLocations());
			return usedMemory;
		}
	}

	@Override
	public String toString() {
		StringBuilder res = new StringBuilder();
		if (!condition.equals(ExpressionFactory.TRUE)) { 
			res.append("if ");
			res.append(condition);
			res.append(" ");
		}
		res.append("GOTO ");
		if (targetExpression != null) {
			res.append(targetExpression.toHexString());

			// Add import symbol (hackish)
			if (targetExpression instanceof RTLMemoryLocation) {
				RTLMemoryLocation m = (RTLMemoryLocation)targetExpression;
				if (m.getAddress() instanceof RTLNumber) {
					long v = ((RTLNumber)m.getAddress()).longValue();
					AbsoluteAddress va = new AbsoluteAddress(v);
					ExecutableImage module = Program.getProgram().getModule(va);
					if (module != null) {
						String symbol = module.getSymbolFinder().getSymbolFor(va);
						if (!symbol.equals("")) res.append("(" + symbol + ")");
					} else {
						res.append(va);
					}
				}
			}
			
		}
		else res.append("null");
		return res.toString();
	}

	public RTLExpression getCondition() {
		return condition;
	}

	@Override
	public void inferTypes(Architecture arch) throws TypeInferenceException {
		condition = condition.inferBitWidth(arch, 1);
		targetExpression = targetExpression.inferBitWidth(
				arch, arch.getAddressBitWidth());
	}

	@Override
	public void setLabel(AbsoluteAddress addr, int rtlId) {
		super.setLabel(addr, rtlId);
		if (targetExpression == null)
			targetExpression = ExpressionFactory.createNumber(addr.getValue(), addr.getBitWidth());
	}
	
	@Override
	public <T> T accept(StatementVisitor<T> visitor) {
		return visitor.visit(this);
	}
	
	public Type getType() {
		return type;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result
				+ ((condition == null) ? 0 : condition.hashCode());
		result = prime
				* result
				+ ((targetExpression == null) ? 0 : targetExpression.hashCode());
		result = prime * result + ((type == null) ? 0 : type.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		RTLGoto other = (RTLGoto) obj;
		if (condition == null) {
			if (other.condition != null)
				return false;
		} else if (!condition.equals(other.condition))
			return false;
		if (targetExpression == null) {
			if (other.targetExpression != null)
				return false;
		} else if (!targetExpression.equals(other.targetExpression))
			return false;
		if (type == null) {
			if (other.type != null)
				return false;
		} else if (!type.equals(other.type))
			return false;
		return true;
	}
}
