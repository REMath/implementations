/*
 * CallStackState.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.callstack;

import java.util.*;

import org.jakstab.Program;
import org.jakstab.analysis.*;
import org.jakstab.asm.*;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.Logger;
import org.jakstab.util.Tuple;

/**
 * @author Johannes Kinder
 */
public class CallStackState implements AbstractState {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(CallStackState.class);
	
	public static CallStackState TOP = new CallStackState(null);
	public static CallStackState BOT = new CallStackState(null);
	
	private final Deque<Location> callStack;
	
	public CallStackState() {
		this(new LinkedList<Location>());
	}
	
	public CallStackState(Deque<Location> callStack) {
		this.callStack = callStack;
	}

	public AbstractState abstractPost(StateTransformer transformer,
			Precision precision) {
		if (isBot()) return BOT;
		if (isTop()) return TOP;
		
		final RTLStatement statement = (RTLStatement)transformer;
		return statement.accept(new DefaultStatementVisitor<CallStackState>() {

			
			@Override
			protected CallStackState visitDefault(RTLStatement stmt) {
				return CallStackState.this;
			}

			@Override
			public CallStackState visit(RTLAssume stmt) {

				Instruction instr = Program.getProgram().getAssemblyMap().get(stmt.getAddress());
				Deque<Location> postStack;
				RTLGoto gotoStmt = stmt.getSource();

				long addressValue = stmt.getAddress().getValue(); 

				// in the stub area there are only returns (but no real asm instructions)
				// in the prologue there is only a single call
				// Return
				if (gotoStmt.getType() == RTLGoto.Type.RETURN) {
					postStack = new LinkedList<Location>(callStack);
					if (postStack.isEmpty()) {
						logger.warn("Return instruction on empty call stack!");
					} else {
						Location target = postStack.pop();
						logger.debug("Call stack: Return to " + target + ". Remaining stack " + postStack);
					}
				} 
				// Prologue Call
				else if (Program.getProgram().getHarness().contains(stmt.getAddress())) {
					postStack = new LinkedList<Location>(callStack);
					postStack.push(new Location(Program.getProgram().getHarness().getFallthroughAddress(stmt.getAddress())));
				}
				// Call
				else if (gotoStmt.getType() == RTLGoto.Type.CALL) {
					Location returnLabel; 
					if (instr == null) {
						// Happens in import stubs containing a call
						logger.info("No instruction at address " + stmt.getLabel());
						returnLabel = gotoStmt.getNextLabel();
					} else {
						returnLabel = new Location(new AbsoluteAddress(addressValue + instr.getSize()));
					}

					postStack = new LinkedList<Location>();
					for (Iterator<Location> iter = callStack.descendingIterator(); iter.hasNext();) {
						Location exRetLoc = iter.next();
						if (exRetLoc.equals(returnLabel)) {
							logger.verbose("Recursion detected in call at " + stmt.getAddress());
							break;
						} else {
							postStack.push(exRetLoc);
						}
					}

					logger.debug("Call stack: Pushing " + returnLabel);
					postStack.push(returnLabel);
				} 
				// Something else
				else {
					return CallStackState.this;
				}
				return new CallStackState(postStack);
			}

		});		
	}

	@Override
	public String getIdentifier() {
		return Integer.toString(hashCode());
	}

	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(this.getClass().getSimpleName() + " does not contain location information.");
	}

	@Override
	public AbstractState join(LatticeElement l) {
		CallStackState other = (CallStackState)l;
		if (this.isBot()) return other;
		if (other.isBot() || this.equals(other)) return this;
		return TOP;
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {
		if (!isBot() && !isTop() && expressions.length == 2 && 
 				expressions[0].equals(ExpressionFactory.TRUE) && 
				expressions[1].equals(Program.getProgram().getArchitecture().returnAddressVariable())) {
			
			if (callStack.isEmpty()) {
				logger.error("Trying to read return target from empty callstack!");
				return null;
			}
			
			logger.debug("Concretizing callstack element: " + callStack.peek());
			return Collections.singleton(Tuple.create(
					ExpressionFactory.TRUE,
					ExpressionFactory.createNumber(callStack.peek().getAddress().getValue(), 32))
					); 
		} else {
			Tuple<RTLNumber> result = new Tuple<RTLNumber>(expressions.length);
			for (int i=0; i<expressions.length; i++) {
				result.set(i, null);
			}
			return Collections.singleton(result);
		}
	}

	@Override
	public boolean isBot() {
		return this == BOT;
	}

	@Override
	public boolean isTop() {
		return this == TOP;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		CallStackState other = (CallStackState)l;
		if (this.isBot() || other.isTop()) return true;
		if (other.equals(this)) return true;
		else return false;
	}
	
	@Override
	public String toString() {
		return "Call stack: " + callStack;
	}

	@Override
	public int hashCode() {
		if (isTop()) return 842192;
		if (isBot()) return 189487;
		return callStack.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) return true;
		CallStackState other = (CallStackState)obj;
		if (callStack == null) {
			// callStack is only null for singletons TOP and BOT  
			assert isTop() || isBot();
			return false;
		} 
		return callStack.equals(other.callStack);
	}

}
