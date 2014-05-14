/*
 * SSLInstruction.java - This file is part of the Jakstab project.
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

package org.jakstab.ssl;

import java.io.Serializable;

import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.rtl.statements.StatementSequence;


/**
 * @author Johannes Kinder
 */
public final class SSLInstruction implements Serializable {

	private static final long serialVersionUID = -8965196059524975177L;

	private final RTLVariable[] parameters;
	private final String stringRep;
	private final int parameterCount;
	private final StatementSequence body;
	private final String name;

	public SSLInstruction(String name, String[] parameters, StatementSequence body) {
		super();
		this.name = name;
		this.body = body;
		if (parameters == null || parameters.length == 0 || parameters[0] == null ) {
			this.parameters = null;
			this.parameterCount = 0;
		} else {
			int parameterCount = parameters.length;
			this.parameters = new RTLVariable[parameters.length]; 
			for (int i=0; i < parameters.length; i++)
				if (parameters[i] == null) {
					parameterCount = i;
					break;
				} else {
					this.parameters[i] = ExpressionFactory.createVariable(parameters[i]);
				}
			this.parameterCount = parameterCount; 
		}
		
		StringBuilder sb = new StringBuilder();
		sb.append(this.name);
		sb.append('(');
		for (int i = 0; i < parameterCount; i++) {
			if (i > 0) sb.append(',');
			sb.append(parameters[i]);
		}
		sb.append(')');
		stringRep = sb.toString();
	}
	
	public RTLVariable getParameter(int i) {
		if (parameters == null || i >= parameterCount) return null;
		else return parameters[i];
	}
	
	public int getParameterCount() {
		return parameterCount;
	}
	
	public StatementSequence getBody() {
		return body;
	}
	
	public String getName() {
		return name;
	}

	@Override
	public String toString() {
		return stringRep;
	}
	
}
