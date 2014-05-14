/*
 * SSLFunction.java - This file is part of the Jakstab project.
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

package org.jakstab.ssl.parser;

import java.util.List;
import antlr.collections.AST;

/**
 * @author Johannes Kinder
 */
public class SSLFunction {

	private String[] parameters;
	private String stringRep;
	private int parameterCount;
	private AST body;
	private String name;

	public SSLFunction(String name, List<String> parameters, AST body) {
		super();
		this.name = name;
		this.body = body;
		if (parameters != null && parameters.size() > 0) {
			this.parameters = parameters.toArray(new String[3]);
			this.parameterCount = parameters.size();
		}
		else {
			this.parameters = new String[3];
			this.parameterCount = 0;
		}
		stringRep = null;
	}

	public String[] getParameters() {
		return parameters;
	}
	
	public String getParameter(int i) {
		assert (0 <= i && i < parameters.length) : "Invalid parameter number";
		return parameters[i];
	}
	
	public int getParameterCount() {
		return parameterCount;
	}
	
	public AST getAST() {
		return body;
	}
	
	public String getName() {
		return name;
	}

	@Override
	public String toString() {
		if (stringRep == null) {
			StringBuilder sb = new StringBuilder();
			sb.append(this.name);
			sb.append('(');
			for (int i = 0; i < getParameterCount(); i++) {
				if (i > 0) sb.append(',');
				sb.append(parameters[i]);
			}
			sb.append(')');
			stringRep = sb.toString();
		}
		return stringRep;
	}
	
}
