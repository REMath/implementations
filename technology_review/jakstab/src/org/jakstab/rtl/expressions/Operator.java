/*
 * Operator.java - This file is part of the Jakstab project.
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

/**
 * Supported operators in our RTL. GT and GE are replaced by LT and LE,
 * MINUS by PLUS(NEG) and NEQ by NOT(EQ).
 * 
 * @author Johannes Kinder
 */
public enum Operator {

	UNKNOWN,
	
	// Operators for changing bitwidth
	CAST, 
	SIGN_EXTEND("sign_extend"),
	ZERO_FILL("zero_fill"),
	FSIZE,

	// Comparison
	EQUAL("=="), 
	LESS("<"), // Signed
	LESS_OR_EQUAL("<="), // Signed
	UNSIGNED_LESS("u<"), 
	UNSIGNED_LESS_OR_EQUAL("u<="),

	// Unary operators
	NOT("!"),
	NEG("-"),
	
	// Associative commutative bitwise arithmetic operators
	AND("&"), 
	OR("|"), 
	XOR("^"),
	PLUS("+"),
	MUL("*"),
	FMUL,
	FDIV,

	// Other bitwise arithmetic operators
	DIV, 
	MOD, 
	POWER_OF,

	// Bitwise shift operations
	SHR(">>>"), 
	SAR(">>"), /* Shift right with sign extension */
	SHL("<<"), 
	ROL, 
	ROR, 
	ROLC, 
	RORC /* Rotate with carry */
	;
	
	private String stringRep;
	
	private Operator() {
		this.stringRep = this.name();
	}
	
	private Operator(String stringRep) {
		this.stringRep = stringRep;
	}
	
	public String toString() { 
		return stringRep; 
	}

}
