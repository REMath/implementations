/*
 * BasedNumberValuation.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.explicit;

import java.util.*;

import org.jakstab.Program;
import org.jakstab.analysis.*;
import org.jakstab.asm.x86.X86Instruction;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.*;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.*;

/**
 * The abstract state for constant propagation. There are two explicit states 
 * TOP and BOT, all other states use two collections of BasedCPValue elements to
 * assign values to variables and memory. Elements not present in the 
 * collections are implicitly set to a TOP value. BOT elements cannot be
 * present, since a single BOT element makes the whole state turn to BOT.
 * 
 * @author Johannes Kinder
 */
public final class BasedNumberValuation implements AbstractState {

	public static BasedNumberValuation createInitialState() {
		BasedNumberValuation initial = new BasedNumberValuation();
		return initial;
	}
	
	public static long OverAppPrintfArgs = 0;
	public static long ExplicitPrintfArgs = 0;	
	
	/**
	 * Counts allocs at allocation sites 
	 */
	private static final class AllocationCounter {

		public static AllocationCounter create() {
			return new AllocationCounter();
		}
		
		public static AllocationCounter create(AllocationCounter proto) {
			return new AllocationCounter(proto.leaf);
		}
		
		private static final class AllocationTreeNode {
			private final Location location;
			private final AllocationTreeNode parent;
			public AllocationTreeNode(Location location, AllocationTreeNode parent) {
				this.location = location; this.parent = parent;
			}
		}
		
		private AllocationTreeNode leaf;
		
		private AllocationCounter(AllocationTreeNode leaf) {
			this.leaf = leaf;
		}
		
		private AllocationCounter() {
			this(null);
		}
		
		public int countAllocation(Location loc) {
			int count = 0;
			for (AllocationTreeNode iter = leaf; iter != null; iter = iter.parent)
				if (iter.location.equals(loc))
					count++;
			leaf = new AllocationTreeNode(loc, leaf);
			return count;
		}
		
		public AllocationCounter join(AllocationCounter other) {
			// TODO: Implement some kind of joining
			//throw new UnsupportedOperationException("Missing join implementation!");
			// This is invoked only for based constant propagation... don't know if this quick fix is correct?
			return this;
		}
		
	}

	/*	
	private static class AllocationCounter {

		public static AllocationCounter create() {
			return new AllocationCounter();
		}
		
		public static AllocationCounter create(AllocationCounter proto) {
			return new AllocationCounter(proto.allocCounters);
		}
		
		private HashMap<Location, Integer> allocCounters;
		
		private AllocationCounter(HashMap<Location, Integer> allocCounters) {
			this.allocCounters = allocCounters;
		}
		
		private AllocationCounter() {
			this(new HashMap<Location, Integer>());
		}
		
		private AllocationCounter(AllocationCounter proto) {
			this(proto.allocCounters);
		}
		
		public int countAllocation(Location loc) {
			allocCounters = new HashMap<Location, Integer>(allocCounters);
			Integer countObj = allocCounters.get(loc);
			int count = (countObj != null) ? countObj.intValue() : 0;
			count++;
			allocCounters.put(loc, count);
			return count;
		}
		
		public AllocationCounter join(AllocationCounter other) {
			AllocationCounter res = new AllocationCounter(new HashMap<Location, Integer>(other.allocCounters));
			for (Map.Entry<Location, Integer> entry : allocCounters.entrySet()) {
				Integer curInt = res.allocCounters.get(entry.getKey());
				int val = curInt != null ? curInt.intValue() : 0;
				res.allocCounters.put(entry.getKey(), Math.max(val, entry.getValue()));
			}
			return res;
		}
		
	}
	*/
		
	private static final Logger logger = Logger.getLogger(BasedNumberValuation.class);
	
	private final VariableValuation<BasedNumberElement> aVarVal;
	private final PartitionedMemory<BasedNumberElement> aStore;
	private final AllocationCounter allocCounters;
	
	private BasedNumberValuation(VariableValuation<BasedNumberElement> aVarVal, 
			PartitionedMemory<BasedNumberElement> aStore,
			AllocationCounter allocCounters) {
		this.aVarVal = aVarVal;
		this.aStore = aStore;
		this.allocCounters = allocCounters;
	}
	
	private BasedNumberValuation() {
		this(new VariableValuation<BasedNumberElement>(new BasedNumberElementFactory()), 
				new PartitionedMemory<BasedNumberElement>(new BasedNumberElementFactory()),
				AllocationCounter.create());
	}
	
	/**
	 * Copy constructor
	 * 
	 * @param proto
	 */
	protected BasedNumberValuation(BasedNumberValuation proto) {
		this(new VariableValuation<BasedNumberElement>(proto.aVarVal), 
				new PartitionedMemory<BasedNumberElement>(proto.aStore),
				AllocationCounter.create(proto.allocCounters));
	}
	
	private BasedNumberElement abstractEvalAddress(RTLMemoryLocation m) {
		BasedNumberElement abstractAddress = abstractEval(m.getAddress());
		if (m.getSegmentRegister() != null) {
			if (abstractAddress.getRegion() != MemoryRegion.GLOBAL)
				return BasedNumberElement.getTop(m.getBitWidth());
			BasedNumberElement segmentValue = abstractEval(m.getSegmentRegister());
			assert segmentValue.getNumber().intValue() == 0 : "Segment " + m.getSegmentRegister() + " has been assigned a value!";
			abstractAddress = new BasedNumberElement(segmentValue.getRegion(), abstractAddress.getNumber());
		}
		return abstractAddress;
	}
	
	/**
	 * Evaluates an expression in the context of this abstract state to
	 * an abstract value.
	 * 
	 * @param e the expression to be evaluated.
	 * @return the abstract value of the expression in the abstract state.
	 */
	protected BasedNumberElement abstractEval(RTLExpression e) {
		ExpressionVisitor<BasedNumberElement> visitor = new ExpressionVisitor<BasedNumberElement>() {
			
			@Override
			public BasedNumberElement visit(RTLBitRange e) {
				BasedNumberElement aFirstBit = e.getFirstBitIndex().accept(this);
				BasedNumberElement aLastBit = e.getLastBitIndex().accept(this);
				BasedNumberElement aOperand = e.getOperand().accept(this);

				if (!(aFirstBit.hasUniqueConcretization() && 
						aLastBit.hasUniqueConcretization() && 
						aOperand.hasUniqueConcretization())) { 
					return BasedNumberElement.getTop(e.getBitWidth());
				}
				
				return new BasedNumberElement(RTLBitRange.calculate(aFirstBit.getNumber(), aLastBit.getNumber(), aOperand.getNumber()));
			}

			@Override
			public BasedNumberElement visit(RTLConditionalExpression e) {
				BasedNumberElement aCondition = e.getCondition().accept(this);
				BasedNumberElement result = null;
				// If aCondition is TOP, the both branches are joined
				if (BasedNumberElement.TRUE.lessOrEqual(aCondition)) 
					result = e.getTrueExpression().accept(this);
				if (BasedNumberElement.FALSE.lessOrEqual(aCondition)) {
					BasedNumberElement falseVal = e.getFalseExpression().accept(this); 
					result = result == null ? falseVal : result.join(falseVal);
				}
				//logger.info("Cond result: " + result);
				return result;
			}

			@Override
			public BasedNumberElement visit(RTLMemoryLocation m) {
				return getMemoryValue(abstractEvalAddress(m), m.getBitWidth());
			}

			@Override
			public BasedNumberElement visit(RTLNondet e) {
				return BasedNumberElement.getTop(e.getBitWidth());
			}

			@Override
			public BasedNumberElement visit(RTLNumber e) {
				return new BasedNumberElement(e);
			}

			@Override
			public BasedNumberElement visit(RTLOperation e) {
				BasedNumberElement[] aOperands = new BasedNumberElement[e.getOperandCount()];

				for (int i=0; i<e.getOperandCount(); i++) {
					aOperands[i] = e.getOperands()[i].accept(this);
				}
				
				// Handle Boolean (1-bit) operations
				switch (e.getOperator()) {
				case EQUAL:
					// v == 0: If v is a valid pointer, return false.
					if (!aOperands[0].isTop() && !aOperands[0].isUnbased() && aOperands[1].hasUniqueConcretization() &&
							aOperands[1].getNumber().intValue() == 0)
						return BasedNumberElement.FALSE;
					// Same for 0 == v
					if (!aOperands[1].isTop() && !aOperands[1].isUnbased() && aOperands[0].hasUniqueConcretization() &&
							aOperands[0].getNumber().intValue() == 0)
						return BasedNumberElement.FALSE;

					// Fall through if no definitive result

				case UNSIGNED_LESS:
				case UNSIGNED_LESS_OR_EQUAL:
				case LESS:
				case LESS_OR_EQUAL:
					// Check whether both operands have same region
					if (!aOperands[0].isTop() && aOperands[0].getRegion() == aOperands[1].getRegion() && 
							!aOperands[0].isNumberTop() && !aOperands[1].isNumberTop()) {
						// Same region, now compare offsets
						RTLExpression result = ExpressionFactory.createOperation(e.getOperator(), aOperands[0].getNumber(), 
								aOperands[1].getNumber()).evaluate(new Context());

						if (result.equals(ExpressionFactory.TRUE)) return BasedNumberElement.TRUE; 
						if (result.equals(ExpressionFactory.FALSE)) return BasedNumberElement.FALSE; 
					}
					// Regions not equal or evaluate() did not return a definitive result
					return BasedNumberElement.getTop(1);

				}
				
				RTLExpression[] cOperands = new RTLExpression[e.getOperandCount()];
				MemoryRegion region = MemoryRegion.GLOBAL;
				
				// Handle arithmetic operations
				for (int i=0; i<aOperands.length; i++) {
					
					assert region != MemoryRegion.TOP : "Temporary region cannot become TOP during arithmetic evaluation.";
					
					BasedNumberElement aOperand = aOperands[i];
					// Handle top operands
					if (aOperand.isTop()) {
						return BasedNumberElement.getTop(e.getBitWidth());
					} 
					// Handle operands with a base value (a memory region)
					else if (aOperand.getRegion() != MemoryRegion.GLOBAL) {
						// only handle based operands for simple additions at the moment, should
						// suffice for most cases (stack, structs)
						if (e.getOperator().equals(Operator.PLUS)) {
							// no base yet?
							if (region == MemoryRegion.GLOBAL) {
								region = aOperand.getRegion();
								if (aOperand.isNumberTop())
									cOperands[i] = ExpressionFactory.nondet(e.getOperands()[i].getBitWidth());
								else 
									cOperands[i] = aOperand.getNumber();
							} else {
								// we already have a region
								return BasedNumberElement.getTop(e.getBitWidth());
							}
						} else {
							// No addition, just return nondet
							cOperands[i] = ExpressionFactory.nondet(e.getOperands()[i].getBitWidth());
						}
					} else /* operand has no base */ {
						if (!aOperand.isNumberTop()) {
							cOperands[i] = aOperand.getNumber();
						} else {
							// Check if this was a negation, to support subtraction of two pointers of same base
							RTLExpression eOperand = e.getOperands()[i];
							if (e.getOperator() == Operator.PLUS && eOperand instanceof RTLOperation && ((RTLOperation)eOperand).getOperator() == Operator.NEG) {
								RTLExpression negOp = ((RTLOperation)eOperand).getOperands()[0];
								BasedNumberElement aNegOp = negOp.accept(this);
								if (aNegOp.getRegion() == region) {
									logger.debug("Subtracting pointer from another one to the same region (" + region + ").");
									// We are subtracting the same region, so reset region to global 
									// since just the offset difference remains										
									region = MemoryRegion.GLOBAL;
									// If the operand being negated is (region + TOP), we still treat the region as annihilated 
									// and the result is most likely (global + TOP) unless there are more terms in the addition 
									if (aNegOp.isNumberTop())
										cOperands[i] = ExpressionFactory.nondet(e.getOperands()[i].getBitWidth());
									else 
										cOperands[i] = aNegOp.getNumber();
								} else {
									// This will also trigger when the negation is processed before the other term (e.g., (-x) + y)
									cOperands[i] = ExpressionFactory.nondet(e.getOperands()[i].getBitWidth());
								}
							} else {
								cOperands[i] = ExpressionFactory.nondet(e.getOperands()[i].getBitWidth());
							}
						} 

					}
				}
				RTLExpression result = ExpressionFactory.createOperation(e.getOperator(), cOperands).evaluate(new Context());
				if (result instanceof RTLNumber) {
					return new BasedNumberElement(region, new NumberElement((RTLNumber)result));
				}
				else return new BasedNumberElement(region, NumberElement.getTop(e.getBitWidth()));
			}

			@Override
			public BasedNumberElement visit(RTLSpecialExpression e) {
				if (e.getOperator().equals(RTLSpecialExpression.GETPROCADDRESS)) {
					BasedNumberElement aLibNameAddr = e.getOperands()[0].accept(this);
					BasedNumberElement aProcNameAddr = e.getOperands()[1].accept(this);
					if (aLibNameAddr.hasUniqueConcretization() && aProcNameAddr.hasUniqueConcretization()) {
						long libNameAddr = aLibNameAddr.getNumber().longValue();
						long procNameAddr = aProcNameAddr.getNumber().longValue();
						String libName = getCString(MemoryRegion.GLOBAL, libNameAddr);
						// If it's length 1, it's most probably a unicode string:
						if (libName.length() <= 1) {
							libName = getWString(MemoryRegion.GLOBAL, libNameAddr);
						}
						String procName = getCString(MemoryRegion.GLOBAL, procNameAddr);
						logger.info("GetProcAddress for " + procName + " from module " + libName);
						long procAddress = Program.getProgram().getProcAddress(libName, procName).getValue();
						return new BasedNumberElement(ExpressionFactory.createNumber(procAddress, 32));
						
					} else {
						logger.info("Could not determine parameters of GetProcAddress!");
					}
				} else if (e.getOperator().equals(RTLSpecialExpression.DBG_PRINTF)) {
					BasedNumberElement firstArg = e.getOperands()[0].accept(this);
					// Dereference
					BasedNumberElement stringAddress = getMemoryValue(firstArg, 32);
					if (!stringAddress.getRegion().equals(MemoryRegion.TOP) && !stringAddress.isNumberTop()) {
						String formatString = getCString(stringAddress.getRegion(), stringAddress.getNumber().longValue());
						logger.debug("printf called with format string " + formatString.trim());
						StringBuilder sb = new StringBuilder();
						int varArgCount = 0;
						int lastMatch = 0;
						for (int i = formatString.indexOf('%'); i >= 0; i = formatString.indexOf('%', i + 1)) {
							sb.append(formatString.substring(lastMatch, i));
							lastMatch = i + 2; // skip %i (works only for simple %i, %s...)
							varArgCount++;
							BasedNumberElement curVarArg = getMemoryValue(
									new BasedNumberElement(firstArg.getRegion(), 
											ExpressionFactory.createNumber(firstArg.getNumber().intValue() + varArgCount * 4, 32)), 
											32);
							
							// Very basic support for printf
							switch (formatString.charAt(i + 1)) {
							case 'i':
								logger.debug("  Integer argument: " + curVarArg);
								if (curVarArg.hasUniqueConcretization()) {
									sb.append(curVarArg.getNumber().intValue());
									ExplicitPrintfArgs++;
								} else {
									sb.append(curVarArg);
									OverAppPrintfArgs++;
								}
								break;
							case 's':
								BasedNumberElement argStrAddr = getMemoryValue(curVarArg, 32);
								logger.debug("  String argument: " + argStrAddr);
								sb.append(getCString(argStrAddr.getRegion(), argStrAddr.getNumber().longValue()));
							}
						}
						sb.append(formatString.substring(lastMatch));
						logger.info("DEBUG: printf output: " + sb.toString());
						return new BasedNumberElement(firstArg.getNumber());
					}
				}
				
				return BasedNumberElement.getTop(e.getBitWidth());
			}

			@Override
			public BasedNumberElement visit(RTLVariable e) {
				return getValue(e);
			}
			
		};
		
		BasedNumberElement result = e.accept(visitor);
		
		assert result.getBitWidth() == e.getBitWidth() : "Bitwidth changed during evaluation of " + e + " to " + result;
		
		return result;
	}

	public Set<AbstractState> abstractPost(final RTLStatement statement, final Precision precision) {
		final ExplicitPrecision eprec = (ExplicitPrecision)precision;
		
		return statement.accept(new DefaultStatementVisitor<Set<AbstractState>>() {
			
			private final Set<AbstractState> thisState() {
				if (statement.getLabel() == null) logger.warn("No label: " + statement);
				if (!statement.getLabel().getAddress().equals(statement.getNextLabel().getAddress())) {
					BasedNumberValuation post = new BasedNumberValuation(BasedNumberValuation.this);
					post.clearTemporaryVariables();
					return Collections.singleton((AbstractState)post);
				} else {
					return Collections.singleton((AbstractState)BasedNumberValuation.this);
				}
			}
			
			private final BasedNumberValuation copyThisState() {
				BasedNumberValuation post = new BasedNumberValuation(BasedNumberValuation.this);
				if (statement.getNextLabel() == null || 
						!statement.getAddress().equals(
								statement.getNextLabel().getAddress())) {
					// New instruction
					post.clearTemporaryVariables();
				}
				return post;
			}
			
			@Override
			public Set<AbstractState> visit(RTLVariableAssignment stmt) {
				BasedNumberValuation post = copyThisState();

				RTLVariable lhs = stmt.getLeftHandSide();
				RTLExpression rhs = stmt.getRightHandSide();
				BasedNumberElement evaledRhs = abstractEval(rhs);

				// Check for stackpointer alignment assignments (workaround for gcc compiled files)
				RTLVariable sp = Program.getProgram().getArchitecture().stackPointer();
				if (lhs.equals(sp) && rhs instanceof RTLOperation) {
					RTLOperation op = (RTLOperation)rhs;
					if (op.getOperator().equals(Operator.AND) && 
							op.getOperands()[0].equals(sp) &&
							op.getOperands()[1] instanceof RTLNumber) {
						evaledRhs = getValue(sp);
						logger.warn("Ignoring stackpointer alignment at " + stmt.getAddress());
					}
				}

				post.setValue(lhs, evaledRhs, eprec);
				
				if (!BoundedAddressTracking.keepDeadStack.getValue()) {
					// If the stack pointer was increased, forget stack below to save state space
					if (lhs.equals(Program.getProgram().getArchitecture().stackPointer())) {
						if (!evaledRhs.isTop() && !evaledRhs.isNumberTop()) {
							post.aStore.forgetStackBelow(evaledRhs.getNumber().longValue());
						}
					}
				}

				return Collections.singleton((AbstractState)post);
			}
			
			@Override
			public Set<AbstractState> visit(RTLMemoryAssignment stmt) {
				BasedNumberValuation post = copyThisState();
				BasedNumberElement evaledRhs = abstractEval(stmt.getRightHandSide());

				RTLMemoryLocation m = stmt.getLeftHandSide();
				BasedNumberElement abstractAddress = abstractEvalAddress(m);
				
				// if the address cannot be determined, set all store memory to TOP
				if (!post.setMemoryValue(abstractAddress, m.getBitWidth(), evaledRhs, eprec)) {
					logger.verbose(stmt.getLabel() + ": Cannot resolve memory write to " + m + ".");
					logger.debug("State: " + BasedNumberValuation.this);
				}

				return Collections.singleton((AbstractState)post);
			}
			
			@Override
			public Set<AbstractState> visit(RTLAssume stmt) {

				Architecture arch = Program.getProgram().getArchitecture();
				/////////
				// Special case for non-exit edges of x86 REP/REPNZ prefixes (for loops using ecx)
				if (stmt.getSource().getType() == RTLGoto.Type.STRING_LENGTH_CHECK) { 
					BasedNumberElement loopCounter = getValue(arch.loopCounter());
					if (loopCounter.isTop() || loopCounter.isNumberTop()) {
						X86Instruction instr = (X86Instruction)Program.getProgram().getInstruction(stmt.getAddress());
						BasedNumberValuation post = copyThisState();
						if (instr.hasEsiBasedMemorySource()) {
							logger.debug(stmt.getLabel() + ": ecx is unknown in REP/REPNZ, widening esi");
							post.setValue(arch.stringSource(), new BasedNumberElement(
									getValue(arch.stringSource()).getRegion(), 
									NumberElement.getTop(arch.getAddressBitWidth())));
						} 
						if (instr.hasEdiBasedMemoryTarget()) {
							logger.debug(stmt.getLabel() + ": ecx is unknown in REP/REPNZ, widening edi");
							post.setValue(arch.stringTarget(), new BasedNumberElement(
									getValue(arch.stringTarget()).getRegion(), 
									NumberElement.getTop(arch.getAddressBitWidth())));
						}
						// STRING_LENGTH_CHECK assumptions are ecx == 0 or !(ecx == 0)
						RTLOperation operation = (RTLOperation)stmt.getAssumption();
						if (operation.getOperator() == Operator.EQUAL) {
							assert operation.getOperands()[0] == arch.loopCounter();
							assert ((RTLNumber)operation.getOperands()[1]).longValue() == 0;
							post.setValue(arch.loopCounter(), abstractEval(operation.getOperands()[1]));
						}
						
						return Collections.singleton((AbstractState)post);
					}
				}
				//// End special case for REP/REPNZ
				
				
				AbstractValue truthValue = abstractEval(stmt.getAssumption());

				if (truthValue.equals(BasedNumberElement.FALSE)) {
					logger.info(stmt.getLabel() + ", state ID " + getIdentifier() + ": Transformer " + stmt + " is infeasible.");
					return Collections.emptySet();
				} else if (truthValue.equals(BasedNumberElement.TRUE)){
					return thisState();
				} else {
					// first evaluate the assumption, maybe we can simplify it due to assignments in this state
					RTLExpression assumption = stmt.getAssumption();
					assumption = assumption.evaluate(getContext());
					
					// Modify state so that it respects the assumption
					// We should really enumerate all solutions and create the corresponding states (requires different return type)
					// Currently works only for simple assumptions 

					if (assumption instanceof RTLOperation) {
						RTLOperation operation = (RTLOperation)assumption;
						switch(operation.getOperator()) {
						case EQUAL:
							// assume(var = value)
							if (operation.getOperands()[0] instanceof RTLVariable) {
								RTLVariable var = (RTLVariable)operation.getOperands()[0];

								if (operation.getOperands()[1] instanceof RTLNumber) {
									RTLNumber value = (RTLNumber)operation.getOperands()[1];
									//logger.debug("Restricting state to " + var + " = " + value);
									BasedNumberValuation post = copyThisState();
									post.setValue(var, new BasedNumberElement(value), eprec);
									return Collections.singleton((AbstractState)post);
								}
							}
							break;
						case NOT:
							// assume(!x)
							if (operation.getOperands()[0] instanceof RTLVariable) {
								RTLVariable var = (RTLVariable)operation.getOperands()[0];
								//logger.debug("Restricting state to " + var + " = false");
								BasedNumberValuation post = copyThisState();
								post.setValue(var, BasedNumberElement.FALSE, eprec);
								return Collections.singleton((AbstractState)post);
							}
							break;
						case UNSIGNED_LESS_OR_EQUAL:
							// assume (x u<= n)
							/* Currently commented out - we do not really know when
							 * we want to do this - in jumptables yes (first default-check
							 * generates all possible cases), but in simple input u<= n
							 * checks, we do not.
							if (operation.getOperands()[0] instanceof Writable && 
									operation.getOperands()[1] instanceof RTLNumber) {
								
								long max = ((RTLNumber)operation.getOperands()[1]).longValue();
								if (max <= Options.explicitThreshold) {
									Writable lhs = (Writable)operation.getOperands()[0];
									Set<AbstractState> postSet = new FastSet<AbstractState>();
									ExpressionFactory factory = ExpressionFactory.getInstance();
									
									BasedNumberElement aAddr = null;
									if (lhs instanceof RTLMemoryLocation)
										aAddr = abstractEvalAddress((RTLMemoryLocation)lhs);
									
									for (int val = 0; val <= max; val++) {
										BasedNumberValuation post = copyThisState();
										BasedNumberElement value = new BasedNumberElement(factory.createNumber(val, lhs.getBitWidth()));
										if (lhs instanceof RTLMemoryLocation)
											post.setMemoryValue(aAddr, lhs.getBitWidth(), value, eprec);
										else
											post.setValue((RTLVariable)lhs, value);
										if (postSet.contains(post)) {
											logger.debug("Post states already contain enumerated state - reduced precision for " + lhs + "?");
											break;
										}
										postSet.add((AbstractState)post);
									}
									logger.debug(stmt.getLabel() + ": Assume created " + postSet.size() + " new states!");
									return postSet;
								} else {
									logger.debug(stmt + " enumeration would exceed threshold!");
								}
							}
							*/
						}
						
					}
					else if (assumption instanceof RTLVariable) {
						// assume(x)
						RTLVariable var = (RTLVariable)assumption;
						//logger.debug("Restricting state to " + var + " = true");
						BasedNumberValuation post = copyThisState();
						post.setValue(var, BasedNumberElement.TRUE, eprec);
						return Collections.singleton((AbstractState)post);
					}
					return thisState();
				}
			}
			
			@Override
			public Set<AbstractState> visit(RTLAlloc stmt) {
				BasedNumberValuation post = copyThisState();
				Writable lhs = stmt.getPointer();
				// Note: We never need to create heap regions as summary regions. Either the threshold
				// is high enough to precisely track all executions of an allocation explicitly,
				// or the number of different pointers/regions also exceeds the threshold and
				// will be widened to T.
				// TODO: How can we create regions to allow exchange of information between analyses?
				//MemoryRegion newRegion = MemoryRegion.create("alloc" + stmt.getLabel() + "_" + getIdentifier());
				
				MemoryRegion newRegion;
				
				// Check for hardcoded allocation names (i.e., stack or FS)
				if (stmt.getAllocationName() != null) {
					newRegion = MemoryRegion.create(stmt.getAllocationName());
				} else {
					newRegion = MemoryRegion.create("alloc" + stmt.getLabel() + 
							"#" + post.allocCounters.countAllocation(stmt.getLabel()));
				}
				
				// We also allow pointers of less than the actual address size, to emulate the 16 bit segment registers FS/GS
				// FS gets a value of (FS, 0) in the prologue. 
				
				if (lhs instanceof RTLVariable) {
					post.setValue((RTLVariable)lhs, new BasedNumberElement(newRegion, 
							ExpressionFactory.createNumber(0, lhs.getBitWidth())), eprec);
				} else {
					RTLMemoryLocation m = (RTLMemoryLocation)lhs;
					BasedNumberElement abstractAddress = abstractEvalAddress(m);
					if (!post.setMemoryValue(abstractAddress, m.getBitWidth(), 
							new BasedNumberElement(newRegion, 
									ExpressionFactory.createNumber(0, lhs.getBitWidth())), eprec))
						logger.verbose(stmt.getLabel() + ": Cannot resolve memory write from alloc to " + m + ".");
				}

				return Collections.singleton((AbstractState)post);
			}

			@Override
			public Set<AbstractState> visit(RTLDealloc stmt) {
				BasedNumberValuation post = copyThisState();
				BasedNumberElement abstractAddress = abstractEval(stmt.getPointer());
				// if the address cannot be determined, set all store memory to TOP
				if (abstractAddress.isTop()) {
					logger.info(getIdentifier() + ": Cannot resolve location of deallocated memory pointer " + stmt.getPointer() + ". Might miss use after free bugs!");
					//logger.info(getIdentifier() + ": Cannot resolve location of deallocated memory pointer " + stmt.getPointer() + ". Defaulting ALL memory to " + Characters.TOP);
					//logger.info(BasedNumberValuation.this);
					//post.aStore.setTop();
				} else {
					if (abstractAddress.getRegion() == MemoryRegion.GLOBAL || abstractAddress.getRegion() == MemoryRegion.STACK) 
						throw new UnknownPointerAccessException("Cannot deallocate " + abstractAddress.getRegion() + "!");
					logger.debug(stmt.getLabel() + ": Dealloc on " + abstractAddress.getRegion()); 
					post.aStore.setTop(abstractAddress.getRegion());
				}
				return Collections.singleton((AbstractState)post);
			}

			@Override
			public Set<AbstractState> visit(RTLUnknownProcedureCall stmt) {
				BasedNumberValuation post = copyThisState();
				for (RTLVariable var : stmt.getDefinedVariables()) {
					post.setValue(var, BasedNumberElement.getTop(var.getBitWidth()), eprec);
				}
				post.aStore.setTop();
				return Collections.singleton((AbstractState)post);
			}

			@Override
			public Set<AbstractState> visit(RTLHavoc stmt) {
				assert (stmt.getMaximum() instanceof RTLNumber);

				long max = ((RTLNumber)stmt.getMaximum()).longValue();
				// Convert max from unsigned to signed
				if (max < 0) {
					max = (1 << stmt.getMaximum().getBitWidth()) + max;
				}
				RTLVariable var = stmt.getVariable();
				if (max > eprec.getThreshold(var)) {
					logger.debug(stmt.getLabel() + ": Havoc bound exceeds variable precision! Setting " + var + " to $" + Characters.TOP);
					BasedNumberValuation post = copyThisState();
					post.setValue(var, new BasedNumberElement(MemoryRegion.GLOBAL, 
							NumberElement.getTop(var.getBitWidth())), eprec);
					return Collections.singleton((AbstractState)post);
				} else {
					Set<AbstractState> postSet = new FastSet<AbstractState>();
					for (int val = 0; val <= max; val++) {
						BasedNumberValuation post = copyThisState();
						post.setValue(var, new BasedNumberElement(ExpressionFactory.createNumber(val, var.getBitWidth())), eprec);
						postSet.add(post);
					}
					logger.debug(stmt.getLabel() + ": Havoc created " + postSet.size() + " new states!");
					//logger.debug("State was: " + BasedNumberValuation.this);
					return postSet;
				}
			}

			@Override
			public Set<AbstractState> visit(RTLMemset stmt) {

				BasedNumberValuation post = copyThisState();

				BasedNumberElement aDest = abstractEval(stmt.getDestination());
				BasedNumberElement aVal = abstractEval(stmt.getValue());
				BasedNumberElement aCount = abstractEval(stmt.getCount());
				
				logger.debug(stmt.getLabel() + ": memset( " + aDest + ", " + aVal + ", " + aCount + ")");
				
				if (aCount.hasUniqueConcretization() && !aDest.isTop() && !aDest.isNumberTop()) {
					long count = aCount.getNumber().longValue();
					int step = aVal.getBitWidth() / 8;
					long base = aDest.getNumber().longValue();
					for (long i=base; i<base + (count * step); i += step) {
						BasedNumberElement pointer = new BasedNumberElement(
								aDest.getRegion(), 
								new NumberElement(ExpressionFactory.createNumber(i, aDest.getBitWidth()))
								);
						post.setMemoryValue(pointer, aVal.getBitWidth(), aVal, eprec);
					}
					
				} else {
					logger.debug(stmt.getLabel() + ": Overapproximating memset( " + aDest + ", " + aVal + ", " + aCount + ")");
					post.aStore.setTop(aDest.getRegion());
				}
				
				return Collections.singleton((AbstractState)post);
			}

			@Override
			public Set<AbstractState> visit(RTLMemcpy stmt) {
				BasedNumberValuation post = copyThisState();

				BasedNumberElement aSrc = abstractEval(stmt.getSource());
				BasedNumberElement aDest = abstractEval(stmt.getDestination());
				BasedNumberElement aSize = abstractEval(stmt.getSize());
				
				logger.debug(stmt.getLabel() + ": memcpy( " + aSrc + ", " + aDest + ", " + aSize + ")");
				
				
				if (aSize.hasUniqueConcretization() && 
						!aDest.isTop() && !aDest.isNumberTop()) {

					long size = aSize.getNumber().longValue();
					
					// Source is unknown
					if (aSrc.isTop() || aSrc.isNumberTop()) {

						logger.debug(stmt.getLabel() + ": memcpy( " + aSrc + ", " + aDest + ", " + aSize + ") with unknown source.");
						long base = aDest.getNumber().longValue();
						for (long i=base; i<base + size; i++) {
							BasedNumberElement pointer = new BasedNumberElement(
									aDest.getRegion(), 
									new NumberElement(ExpressionFactory.createNumber(i, aDest.getBitWidth()))
									);
							post.setMemoryValue(pointer, 8, BasedNumberElement.getTop(8), eprec);
						}

					} else {
						post.aStore.memcpy(aSrc.getRegion(), aSrc.getNumber().longValue(), 
								aDest.getRegion(), aDest.getNumber().longValue(),
								size);
					}
				} else {
					logger.debug(stmt.getLabel() + ": Overapproximating memcpy( " + aSrc + ", " + aDest + ", " + aSize + ")");
					post.aStore.setTop(aDest.getRegion());
				}
				
				return Collections.singleton((AbstractState)post);
			}
			
			@Override
			public Set<AbstractState> visitDefault(RTLStatement stmt) {
				return thisState();
			}

		});
	}

	public BasedNumberElement getValue(RTLVariable var) {
		return aVarVal.get(var);
	}

	void setValue(RTLVariable var, BasedNumberElement value) {
		aVarVal.set(var, value);
	}
	
	void setValue(RTLVariable var, BasedNumberElement value, ExplicitPrecision precision) {
		BasedNumberElement valueToSet;
		switch (precision.getTrackingLevel(var)) {
		case NONE:
			logger.debug("Precision prevents value " + value + " to be set for " + var);
			valueToSet = BasedNumberElement.getTop(var.getBitWidth());
			break;
		case REGION:
			valueToSet = new BasedNumberElement(value.getRegion(), 
					NumberElement.getTop(var.getBitWidth()));
			break;
		default:
			valueToSet = value;
		}
		aVarVal.set(var, valueToSet);
	}

	private BasedNumberElement getMemoryValue(BasedNumberElement pointer, int bitWidth) {
		if (pointer.isTop() || pointer.isNumberTop()) return BasedNumberElement.getTop(bitWidth);
		long offset = pointer.getNumber().longValue(); 
		return aStore.get(pointer.getRegion(), offset, bitWidth);
	}

	// Returns true if set was successful, false if memory was overapproximated
	private boolean setMemoryValue(BasedNumberElement pointer, int bitWidth, BasedNumberElement value, ExplicitPrecision precision) {
		if (pointer.isTop()) {
			aStore.setTop();
			return false;
		} else if (pointer.isNumberTop()) {
			aStore.setTop(pointer.getRegion());
			return false;
		} else {
			long offset = pointer.getNumber().longValue(); 

			BasedNumberElement valueToSet;
			switch (precision.getTrackingLevel(pointer.getRegion(), offset)) {
			case NONE:
				logger.debug("Precision prevents value " + value + " to be set for " + pointer);
				valueToSet = BasedNumberElement.getTop(bitWidth);
				break;
			case REGION:
				valueToSet = new BasedNumberElement(value.getRegion(), 
						NumberElement.getTop(bitWidth));
				break;
			default:
				valueToSet = value;
			}
			
			aStore.set(pointer.getRegion(), offset, bitWidth, valueToSet);
			return true;
		}
	}
	
	private String getCString(MemoryRegion region, long offset) {
		StringBuilder res = new StringBuilder();
		int length = 0;
		while (true) {
			BasedNumberElement v = aStore.get(region, offset + length, 8);
			if (v.isBot() || v.isTop()) return null;
			int newChar = v.getNumber().intValue();
			if (newChar == 0) break;
			length++;
			res.append((char)newChar);
		}
		return res.toString();
	}
	
	/**
	 * Just a hack, not really a unicode implementation.
	 */
	private String getWString(MemoryRegion region, long offset) {
		StringBuilder res = new StringBuilder();
		int length = 0;
		boolean firstByte = true;
		while (true) {
			BasedNumberElement v = aStore.get(region, offset + length, 8);
			length++;
			if (v.isBot() || v.isTop()) return null;
			int newChar = v.getNumber().intValue();
			if (firstByte) {
				if (newChar == 0) break;
				res.append((char)newChar);
				firstByte = false;
			} else {
				firstByte = true;
			}
		}
		return res.toString();
	}

	@Override
	public boolean isTop() {
		return aVarVal.isTop() && aStore.isTop();
	}

	@Override
	public boolean isBot() {
		return false;
	}

	private void clearTemporaryVariables() {
		for (RTLVariable tmp : Program.getProgram().getArchitecture().getTemporaryVariables()) {
			aVarVal.setTop(tmp);
		}
	}
	
	/*
	 * @see org.jakstab.analysis.AbstractState#join(org.jakstab.analysis.AbstractState)
	 */
	@Override
	public BasedNumberValuation join(LatticeElement l) {
		BasedNumberValuation other = (BasedNumberValuation)l;
		
		if (isTop() || other.isBot()) return this;
		if (isBot() || other.isTop()) return other;
			
		VariableValuation<BasedNumberElement> newVarVal = 
			aVarVal.join(other.aVarVal); 
		PartitionedMemory<BasedNumberElement> newStore = 
			aStore.join(other.aStore);
		AllocationCounter newAllocCounters = 
				allocCounters.join(other.allocCounters);
		
		return new BasedNumberValuation(newVarVal, newStore, newAllocCounters);
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		BasedNumberValuation other = (BasedNumberValuation)l;
		if (this == other) return true;
		if (other.isTop() || isBot()) return true;
		if (isTop() || other.isBot()) return false;
		
		return aVarVal.lessOrEqual(other.aVarVal) &&
		aStore.lessOrEqual(other.aStore);
	}
	
	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof BasedNumberValuation)) return false;
		BasedNumberValuation other = (BasedNumberValuation)obj;
		if (other == this) return true;

		return aVarVal.equals(other.aVarVal) && aStore.equals(other.aStore);
	}
	
	@Override
	public String getIdentifier() {
		//return Long.toString(stateId);
		return Long.toString(hashCode());
	}

	@Override
	public String toString() {
		if (isTop()) return Characters.TOP;
		else if (isBot()) return Characters.BOT;
		else return "BAT: Var=" + aVarVal.toString() + "," + aStore.toString();
	}

	@Override
	public int hashCode() {
		return aVarVal.hashCode() ^ aStore.hashCode();
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {

		Tuple<Set<RTLNumber>> cValues = new Tuple<Set<RTLNumber>>(expressions.length);
		for (int i=0; i<expressions.length; i++) {
			BasedNumberElement aValue = abstractEval(expressions[i]);
			cValues.set(i, aValue.concretize());
		}
		return Sets.crossProduct(cValues);

	}
	
	public VariableValuation<BasedNumberElement> getVariableValuation() {
		return aVarVal;
	}
	
	public PartitionedMemory<BasedNumberElement> getStore() {
		return aStore;
	}
	
	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(this.getClass().getSimpleName() + " does not contain location information.");
	}
	
	private Context getContext() {
		Context context = new Context();
		for (Map.Entry<RTLVariable, BasedNumberElement> entry : aVarVal) {
			RTLVariable var = entry.getKey();
			BasedNumberElement val = entry.getValue(); 
			if (val.hasUniqueConcretization())
				context.addAssignment(var, val.getNumber());
		}
		return context;
	}
	
}
