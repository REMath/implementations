/*
 * StatementSequence.java - This file is part of the Jakstab project.
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

import java.io.Serializable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.*;
import org.jakstab.ssl.CanonizationVisitor;
import org.jakstab.util.Logger;

/**
 * A sequence of RTL statements, only used during SSL instantiation and in stub generation. 
 * 
 * @author Johannes Kinder
 */
public class StatementSequence implements Iterable<RTLStatement>, Serializable {

	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(StatementSequence.class);
	private static final long serialVersionUID = -3750283603929931899L;


	private LinkedList<RTLStatement> sequence;

	/**
	 * Creates a new empty statement sequence.
	 */
	public StatementSequence() {
		sequence = new LinkedList<RTLStatement>();
	}

	/**
	 * Inserts a statement before the start of this sequence when it is not null, 
	 * otherwise does nothing.
	 * 
	 * @param statement the statement to be added.
	 */
	public void addFirst(RTLStatement statement) {
		if (statement != null) {
			sequence.addFirst(statement);
		}
	}

	/**
	 * Inserts a sequence of statements before the start of this sequence when the 
	 * sequence object is not null, otherwise does nothing.
	 * 
	 * @param statements the statement sequence to be added
	 */
	public void addFirst(StatementSequence statements) {
		if (statements != null) {
			sequence.addAll(0, statements.sequence);
		}
	}

	/**
	 * Adds a statement to the end of this sequence when it is not null, 
	 * otherwise does nothing.
	 * 
	 * @param statement the statement to be added.
	 */
	public void addLast(RTLStatement statement) {
		if (statement != null) {
			sequence.addLast(statement);
		}
	}

	/**
	 * Adds a sequence of statements to the end of this sequence when the sequence 
	 * object is not null, otherwise does nothing.
	 * 
	 * @param statements the statement sequence to be added
	 */
	public void addLast(StatementSequence statements) {
		if (statements != null) {
			sequence.addAll(statements.sequence);
		}
	}

	public Iterator<RTLStatement> iterator() {
		return sequence.iterator();
	}

	public void removeLast() {
		sequence.removeLast();
	}


	public RTLStatement getFirst() {
		return sequence.getFirst();
	}

	public RTLStatement getLast() {
		return sequence.getLast();
	}

	/**
	 * Returns a canonical copy of this sequence. Canonization is required only
	 * once, after parsing a SSL specification. Canonical statements do not contain
	 * assignments of the special %RPT and %SKIP registers.
	 * 
	 * NOTE: Unchanged elements are not copied but the originals are returned. 
	 * 
	 * @return this statement sequence converted to canonical form. 
	 */
	public StatementSequence canonize() {
		CanonizationVisitor visitor = new CanonizationVisitor();
		
		RTLExpression skipCondition = null;
		RTLExpression repeatCondition = null;
		
		LinkedList<RTLStatement> oldSequence = sequence;
		sequence = new LinkedList<RTLStatement>();

		/* Evaluate substatements */
		for (RTLStatement statement : oldSequence) {
			RTLStatement evaldStatement;
			
			if (statement instanceof AssignmentTemplate) {
				AssignmentTemplate a = (AssignmentTemplate)statement;
				
				RTLExpression genericEvaldLHS = a.getLeftHandSide().accept(visitor);
				RTLExpression evaldRHS = a.getRightHandSide().accept(visitor);

				if (!(genericEvaldLHS instanceof Writable))
					throw new RuntimeException("Error: LHS of assignment no longer writable after canonization: " + 
							a.getLeftHandSide().toString() + " = " + genericEvaldLHS.toString());

				Writable evaldLHS = (Writable)genericEvaldLHS;

				/* Convert %SKIP assignments to conditionals */
				if (evaldLHS.equals(ExpressionFactory.SKIP)) {
					skipCondition = evaldRHS;
					continue;
				}

				/* Convert %RPT assignments to conditionals */
				if (evaldLHS.equals(ExpressionFactory.REPEAT)) {
					repeatCondition = evaldRHS;
					continue;
				}

				// if both sides are equal, remove this statement
				if (evaldLHS.equals(evaldRHS)) 
					continue;
				
				evaldStatement = new AssignmentTemplate(a.getBitWidth(), evaldLHS, evaldRHS);
				
			} else /* non AssignmentTemplate */ {
				evaldStatement = statement.evaluate(new Context());
			}

			addLast(evaldStatement);
		}
		if (sequence.size() < 1) 
			return null;

		if (skipCondition != null) {
			RTLGoto skipGoto = new RTLGoto(ExpressionFactory.pc, skipCondition, RTLGoto.Type.STRING_LENGTH_CHECK);
			addFirst(skipGoto);
		}

		if (repeatCondition != null) {
			// Create a dummy goto statement, this will point to the instruction's address after instantiation
			if (!repeatCondition.equals(ExpressionFactory.FALSE)) {
				RTLStatement condGoto = new RTLGoto(null, repeatCondition, RTLGoto.Type.REPEAT);
				addLast(condGoto);
			}
		}

		return this; 
	}
	
	/**
	 * Move all bitrange expressions from the LHS of assignments to the RHS, 
	 * and convert all assignment templates to variable or memory assignments.
	 * @return
	 */
	public StatementSequence normalizeAssignments() {
		LinkedList<RTLStatement> oldSequence = sequence;
		sequence = new LinkedList<RTLStatement>();

		for (RTLStatement statement : oldSequence) {
			if (statement instanceof AssignmentTemplate)
				sequence.addLast(((AssignmentTemplate)statement).convertToSpecificAssignmentType());
			else
				sequence.addLast(statement);
			
		}
		return this; 
	}


	public StatementSequence evaluate(Context context) {
		LinkedList<RTLStatement> oldSequence = sequence;
		sequence = new LinkedList<RTLStatement>();

		for (RTLStatement statement : oldSequence) {
			RTLStatement evaldStatement = statement.evaluate(context);
			if (evaldStatement != null) addLast(evaldStatement);
		}
		if (sequence.size() < 1) 
			return null;

		return this; 
	}

	public int getLength() {
		return sequence.size();
	}

	/**
	 * @return the statement sequence
	 */
	protected List<RTLStatement> getSequence() {
		return sequence;
	}

	public StatementSequence replace(RTLStatement statement, RTLStatement replacement) {
		LinkedList<RTLStatement> oldSequence = sequence;
		sequence = new LinkedList<RTLStatement>();
		for (RTLStatement stmt : oldSequence) {
			if (stmt.equals(statement)) {
				if (replacement != null) {
					addLast(replacement);
				}
			} else addLast(stmt);
		}
		if (sequence.size() < 1) {
			return null;
		}

		return this; 
	}

	@Override
	public String toString() {
		StringBuilder res = new StringBuilder();
		res.append("{ ");
		for (RTLStatement statement : sequence) {
			res.append(statement.toString());
			res.append("; ");
		}
		res.append(" }");
		return res.toString();
	}

	public StatementSequence copy() {
		StatementSequence res = new StatementSequence();
		for (RTLStatement statement : sequence) {
			res.addLast(statement.copy());
		}
		return res;
	}

	public SetOfVariables getDefinedVariables() {
		SetOfVariables res = new SetOfVariables();
		for (RTLStatement s : sequence)
			res.addAll(s.getDefinedVariables());
		return res;
	}
	
}
