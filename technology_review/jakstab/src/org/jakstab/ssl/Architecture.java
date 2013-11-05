/*
 * Architecture.java - This file is part of the Jakstab project.
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

import java.io.*;
import java.util.*;

import org.jakstab.Options;
import org.jakstab.util.Logger;
import org.jakstab.asm.*;
import org.jakstab.asm.x86.*;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.*;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.ssl.parser.*;

import antlr.ANTLRException;

/**
 *  This class represents the physical architecture a program runs on. It is 
 *  initialized by loading the corresponding SSL specification. It should 
 *  encapsulate all architecture specific aspects of the analyses, and
 *  also supports the conversion of disassembled instructions to RTL statements.
 *  
 *  @author Johannes Kinder
 */
public class Architecture {

	private final static Logger logger = Logger.getLogger(Architecture.class);

	// Variables that can be safely forgotten when crossing instruction boundaries
	// This should better be extracted from the SSL somehow (e.g. by making all 
	// explicitly declared registers non-temporary.
	private static final SetOfVariables temporaryVariables;
    // flags
	private static final SetOfVariables statusFlags;
	static {
		temporaryVariables = new SetOfVariables(Arrays.asList(new RTLVariable[] {
				ExpressionFactory.createVariable("tmpb", 8),
				ExpressionFactory.createVariable("tmph", 16),
				ExpressionFactory.createVariable("tmp1", 32),
				ExpressionFactory.createVariable("tmp2", 32),
				ExpressionFactory.createVariable("tmp3", 32),
				ExpressionFactory.createVariable("tmp4", 32),
				ExpressionFactory.createVariable("tmp5", 32),
				ExpressionFactory.createVariable("retaddr", 32),
				ExpressionFactory.createVariable("tmpl", 64),
				ExpressionFactory.createVariable("tmpD", 80),
				ExpressionFactory.createVariable("tmpD1", 80),
				ExpressionFactory.createVariable("tmpD2", 80),
				ExpressionFactory.createVariable("tmpb1", 8),
				ExpressionFactory.createVariable("tmpb2", 8),
				ExpressionFactory.createVariable("tmph1", 16),
				ExpressionFactory.createVariable("tmph2", 16),
				ExpressionFactory.createVariable("tmpq2", 64),
				ExpressionFactory.createVariable("tmpq3", 64),
				ExpressionFactory.createVariable("tmpq5", 64)
		}));
		statusFlags = new SetOfVariables(Arrays.asList(new RTLVariable[] {
				ExpressionFactory.createVariable("%AF", 1),
				ExpressionFactory.createVariable("%CF", 1),
				ExpressionFactory.createVariable("%C1", 1),
				ExpressionFactory.createVariable("%C2", 1),
				ExpressionFactory.createVariable("%FLF", 1),
				ExpressionFactory.createVariable("%FZF", 1),
				ExpressionFactory.createVariable("%fsw", 16),
				ExpressionFactory.createVariable("%fcw", 16),
				ExpressionFactory.createVariable("%fstp", 8),
				ExpressionFactory.createVariable("%DF", 1),
				ExpressionFactory.createVariable("%IF", 1),
				ExpressionFactory.createVariable("%OF", 1),
				ExpressionFactory.createVariable("%PF", 1),
				ExpressionFactory.createVariable("%SF", 1),
				ExpressionFactory.createVariable("%ZF", 1)
		}));
	}

	
	private File specFile;
	private Map<String, SSLInstruction> instructions;
	private Map<String, List<SSLInstruction>> instrGroups;
	private final RTLVariable stackPointer;
	private final RTLVariable framePointer;
	private final RTLVariable loopCounter;
	private final RTLVariable stringSource;
	private final RTLVariable stringTarget;
	private final RTLVariable retAddrVar;
	private final MagicInstructions magicInstructions;

	private SetOfVariables registers;

	/**
	 * Parses an SSL specification from a given filename and converts the RTL 
	 * blocks to canonical form.
	 * 
	 * @param fileName The path of the SSL file to be parsed.
	 */
	public Architecture(String fileName) throws FileNotFoundException, ANTLRException {

		parseSSL(fileName);
		magicInstructions = new MagicInstructions();
		
		stackPointer = ExpressionFactory.createVariable("%esp", 32);
		framePointer = ExpressionFactory.createVariable("%ebp", 32);
		retAddrVar = ExpressionFactory.createVariable("retaddr", 32);
		loopCounter = ExpressionFactory.createVariable("%ecx", 32);
		stringSource = ExpressionFactory.createVariable("%esi", 32);
		stringTarget = ExpressionFactory.createVariable("%edi", 32);
	}
	
	public RTLVariable stackPointer() {
		return stackPointer;
	}
	
	public RTLVariable returnAddressVariable() {
		return retAddrVar;
	}
	
	public RTLVariable framePointer() {
		return framePointer;
	}
	
	public RTLVariable programCounter() {
		return ExpressionFactory.pc;
	}
	
	public RTLVariable loopCounter() {
		return loopCounter;
	}

	public RTLVariable stringSource() {
		return stringSource;
	}

	public RTLVariable stringTarget() {
		return stringTarget;
	}

	public SetOfVariables getTemporaryVariables() {
		return temporaryVariables;
	}

	public SetOfVariables getStatusFlags() {
		return statusFlags;
	}
	
	public SetOfVariables getRegisters() {
		return registers;
	}

	/**
	 * Writes the whole instruction set to System.out.
	 */
	void dumpToConsole() {
		for (Iterator<Map.Entry<String, SSLInstruction>> iter = instructions.entrySet().iterator(); iter.hasNext();) {
			Map.Entry<String, SSLInstruction> entry = iter.next();
			SSLInstruction instr = entry.getValue();
			System.out.println(instr.toString() + ": " + instr.getBody());
		}
	}

	// Scores for ranking SSL instruction matches.
	private final int NUM_OPERANDS_SCORE = 100;			// Correct number of operands
	private final int IMPLICIT_OPERAND_MATCH_SCORE = 5;	// Parameter name matches suffix (AL, AX, EAX, CS, DS, ES)
	private final int OPERAND_TYPE_EXACT_SCORE = 4;		// Parameter type matches exactly (i, reg, modrm, mem)
	private final int OPERAND_TYPE_MATCH_SCORE = 3;		// Parameter type possibly matches (modrm to reg)

	private static final String[] repInstructions = new String[] {
		"CMPS", "LODS", "MOVS", "SCAS", "STOS", "INS", "OUTS", "NOP"
	};


	/**
	 * Returns the name of this instruction in the SSL definitions.   
	 * Used for looking up RTL descriptions.
	 * Looks for opcode name and performs parameter matching: 
	 * 
	 * @param instr The instruction to be matches with an SSL prototype
	 * @return The name of the prototype
	 */
	private SSLInstruction matchInstruction(Instruction instr) {
		String name = instr.getName();
		name = name.toUpperCase(Locale.ENGLISH);

		if (instr instanceof X86Instruction) {
			X86Instruction x86instr = (X86Instruction)instr;
			
			// This applies only to "special" instructions used by harness files 
			// for generating IR statements directly
			if (x86instr.hasPrefixLOCK() && x86instr.hasPrefixREPZ()) {
				if (name.equals("INCL")) {
					return magicInstructions.getAllocPrototype();
				} else if (name.equals("NOTL")) {
					return magicInstructions.getDeallocPrototype();
				} else if (name.equals("SUBL")) {
					return magicInstructions.getHavoc32Prototype();
				} else if (name.equals("SUBW")) {
					return magicInstructions.getHavoc16Prototype();
				} else if (name.equals("SUBB")) {
					return magicInstructions.getHavoc8Prototype();
				} else if (name.equals("MOVL")) {
					return magicInstructions.getNondet32Prototype();
				} else if (name.equals("MOVW")) {
					return magicInstructions.getNondet16Prototype();
				} else if (name.equals("MOVB")) {
					return magicInstructions.getNondet8Prototype();
				} else if (name.equals("ADDL")) {
					return magicInstructions.getAssertGTPrototype();
				} else if (name.equals("CMPL")) {
					return magicInstructions.getAssertEQPrototype();
				} else if (name.equals("ADCL")) {
					return magicInstructions.getAssertGEPrototype();
				} else {
					logger.warn("Instruction with both LOCK and REP prefixes was not recognized as Jakstab magic!");
				}
			}
			// Rename instructions with REP prefix to the SSL-format
			// but only do this where it has an effect, otherwise drop it
			else if (x86instr.hasPrefixREPZ() || x86instr.hasPrefixREPNZ()) {
				boolean legalREP = false;
				for (String repInstr : repInstructions) {
					if (name.startsWith(repInstr)) {
						if (x86instr.hasPrefixREPZ()) name = "REP" + name;
						if (x86instr.hasPrefixREPNZ()) name = "REPNE" + name;
						legalREP = true;
						break;
					}
				}
				if (!legalREP) logger.info("Ignoring REP prefix of " + name + "!");
			}
		}

		// check for a direct match and return it if there are no other possibilities
		if (instructions.containsKey(name) && 
				(!instrGroups.containsKey(name) || instrGroups.get(name).size() == 1)) {
			return instructions.get(name);
		}

		if (!(instrGroups.containsKey(name))) {
			logger.warn("SSL library has no entry for " + name + "!");
			return null;
		}

		List<SSLInstruction> instrList = instrGroups.get(name);
		// Is there only one match?
		if (instrList.size() == 1) 
			return instrList.get(0);
		// If there are more, do matching

		int maxScore = -1;
		int score = 0;
		SSLInstruction maxMatch = null;

		//StringBuilder sb = new StringBuilder();

		for (SSLInstruction proto : instrList) {
			score = 0;
			// Check parameter count
			if (instr.getOperandCount() == proto.getParameterCount()) 
				score += NUM_OPERANDS_SCORE;
			
			if (Options.summarizeRep.getValue() && proto.getName().startsWith("REP") &&
					proto.getName().endsWith("SUMMARY")) {
				score++;
			}

			// Do parameter matching
			for (int i = 0; i < instr.getOperandCount(); i++) {
				Operand oper = instr.getOperand(i);

				// Special handling for implicit operands
				if (oper instanceof Register && ( 
						(oper.equals(X86Registers.EAX) && proto.getName().endsWith("EAX")) ||
						(oper.equals(X86Registers.AX) && proto.getName().endsWith("AX")) ||
						(oper.equals(X86Registers.AL) && proto.getName().endsWith("AL")) ||
						(oper.equals(X86SegmentRegisters.CS) && proto.getName().endsWith("CS")) ||
						(oper.equals(X86SegmentRegisters.DS) && proto.getName().endsWith("DS")) ||
						(oper.equals(X86SegmentRegisters.ES) && proto.getName().endsWith("ES")) ||
						(oper.equals(X86SegmentRegisters.FS) && proto.getName().endsWith("FS")) ||
						(oper.equals(X86SegmentRegisters.GS) && proto.getName().endsWith("GS")) ||
						(oper.equals(X86SegmentRegisters.SS) && proto.getName().endsWith("SS"))
						
				)) {
					score += IMPLICIT_OPERAND_MATCH_SCORE;
					if (instr.getOperandCount() == proto.getParameterCount() + 1) {
						score += NUM_OPERANDS_SCORE;
					}
				}

				if (proto.getParameter(i) == null) continue;
				
				String param = proto.getParameter(i).getName();
				if ((oper instanceof Register && param.startsWith("reg"))
						|| (oper instanceof X86FloatRegister && param.equals("sti"))
						|| (oper instanceof Immediate && param.equals("i" + Integer.toString(((Immediate)oper).getDataType().bits())))
						|| (oper instanceof MemoryOperand && (param.equals("modrm") || param.equals("mem")))
						|| (oper instanceof PCRelativeAddress && (param.startsWith("reloc"))))
					score += OPERAND_TYPE_EXACT_SCORE;
				else if (oper instanceof Register && param.equals("modrm"))
					score += OPERAND_TYPE_MATCH_SCORE;
				
			}
			/*if (logger.isDebugEnabled())
				sb.append(proto.getName() + "=" + score + " ");*/
			if (score > maxScore) {
				maxMatch = proto;
				maxScore = score;
			}
		}
		//logger.debug(sb);
		return maxMatch;

	}

	/**
	 * Returns the RTL sequence which corresponds to the specified assembly instruction.
	 * The instruction is looked up in the library and the RTL template is instantiated
	 * with the instruction's parameters.
	 * 
	 * @param address the address of the instruction
	 * @param instr the assembly instruction to be translated to RTL
	 * @return a sequence of RTL statements that match the instruction's behavior 
	 */
	public StatementSequence getRTLEquivalent(AbsoluteAddress address, Instruction instr) {

		StatementSequence rtlTemplate = null;

		SSLInstruction sslInstr = matchInstruction(instr);
		if (sslInstr == null) {
			logger.warn(address + ": No equivalent SSL instruction found for: " + instr.getName());
		} else {
			rtlTemplate = sslInstr.getBody();
		}
		Context instrParamContext = new Context();

		boolean excessAsmOps = false;
		if (sslInstr != null && instr.getOperandCount() > sslInstr.getParameterCount()) {
			excessAsmOps = true;
			logger.debug("Different number of operands for " + instr.getName() + 
					" (" + instr.getOperandCount() + ") and " + 
					sslInstr.toString() + " (" + sslInstr.getParameterCount() + ")!");
			logger.debug("Unassigned operand: " + instr.getOperand(0));
			for (int i = sslInstr.getParameterCount() + 1; i < instr.getOperandCount(); i++)
				logger.debug("Unassigned operand: " + instr.getOperand(i).toString());
		}
		if (!(sslInstr == null || instr.getOperandCount() >= sslInstr.getParameterCount())) {
			logger.error("Instruction: " + address + ": " + instr.toString(address.getValue(), new DummySymbolFinder()));
			logger.error("Template: " + sslInstr);
			throw new RuntimeException("Too few operands in ASM instruction for SSL template");
		}

		/* Transform Parameters. If there are excessive Asm operands, skip the first.
		 * This fixes the problem with an implicit EAX operand. Might not work on other
		 * architectures than x86! */
		if (sslInstr != null) for (int i=0; i<sslInstr.getParameterCount(); i++) {
			Operand iOp = excessAsmOps ? instr.getOperand(i+1) : instr.getOperand(i);
			RTLExpression opAsExpr = ExpressionFactory.createOperand(iOp);
			instrParamContext.substitute(sslInstr.getParameter(i), opAsExpr);
		}

		/* Assign PC - the PC value in the RTL is that of the next instruction in Intel assembly */
		long pcValue = address.getValue(); 
		if (instr instanceof X86Instruction) pcValue += instr.getSize();
		instrParamContext.addAssignment(ExpressionFactory.pc, ExpressionFactory.createNumber(pcValue, ExpressionFactory.pc.getBitWidth()));

		if (rtlTemplate == null) {
			logger.debug("Null RTL body for instruction: " + instr.getName());
			StatementSequence newSeq = new StatementSequence();
			//newSeq.addFirst(new RTLDirective("ASM_" + instr.getName()));
			newSeq.addFirst(new RTLSkip());
			rtlTemplate = newSeq;
		} 

		StatementSequence instrRTL = rtlTemplate.copy();
		int rtlId = 0;
		instrRTL = instrRTL.evaluate(instrParamContext);
		if (instrRTL != null) {
			// we need to label only after evaluation, as some instructions might disappear
			for (RTLStatement stmt : instrRTL) {
				stmt.setLabel(address, rtlId++);
				stmt.setNextLabel(new Location(address, rtlId));
			}
		} else {
			logger.debug("Detected semantic nop during instantiation: " + address);
			instrRTL = new StatementSequence();
			RTLSkip nop = new RTLSkip();
			nop.setLabel(address, 0);
			instrRTL.addFirst(nop);
		}
		// set next label of the last statement to fall-through instruction 
		instrRTL.getLast().setNextLabel(new Location(new AbsoluteAddress(address.getValue() + instr.getSize()), 0));
		
		// infer missing bit widths:
		try {
			for (RTLStatement s : instrRTL)
				s.inferTypes(this);
		} catch (TypeInferenceException e) {
			e.printStackTrace();
			logger.error("Instruction: " + instr.toString(pcValue, new DummySymbolFinder()));
			logger.error("RTL: " + instrRTL);
			throw new RuntimeException();
		}
		// evaluate again, to use inferred bit widths.
		instrRTL = instrRTL.evaluate(new Context());

		// Remove bitranges on LHS and split AssignmentTemplates into memory and variables
		instrRTL = instrRTL.normalizeAssignments();
		// One more simplification step
		instrRTL = instrRTL.evaluate(new Context());
		
		return instrRTL;
	}
	
	public int getAddressBitWidth() {
		return stackPointer.getBitWidth();
	}
	
	public void parseSSL(String fileName) throws FileNotFoundException, ANTLRException {
		specFile = new File(fileName);
		logger.info("Reading machine specification from " + specFile.getName() + ".");

		SSLLexer lex = new SSLLexer(new FileInputStream(specFile));
		SSLParser parser = new SSLParser(lex);
		SSLPreprocessor prep = new SSLPreprocessor();

		parser.start();
		prep.start(parser.getAST());

		Map<String,SSLFunction> instrPrototypes = prep.getInstructions();
		registers = prep.getRegisters();
		registers.removeAll(statusFlags);

		logger.debug("-- Got " + instrPrototypes.size() + " instructions.");

		instructions = new TreeMap<String, SSLInstruction>();
		instrGroups = new TreeMap<String, List<SSLInstruction>>();
		for (Iterator<Map.Entry<String, SSLFunction>> iterator = instrPrototypes.entrySet().iterator(); iterator.hasNext();) {
			Map.Entry<String, SSLFunction> entry = iterator.next();
			String name = entry.getKey();
			SSLFunction proto = entry.getValue();

			//logger.debug("Converting " + proto.getName() + " = " + proto.getAST().toStringTree());

			StatementSequence rtlBody = prep.convertToRTL(proto.getAST());

			// Do a first evaluation step
			rtlBody = rtlBody.evaluate(new Context());

			// Check is necessary for empty instructions, such as INT3 or NOP
			if (rtlBody != null) {
				// Canonize the RTL statements
				rtlBody = rtlBody.canonize();
				
				RTLGoto.Type gotoType;
				if (proto.getName().startsWith("RET")) gotoType = RTLGoto.Type.RETURN;
				else if (proto.getName().startsWith("CALL")) gotoType = RTLGoto.Type.CALL;
				else gotoType = RTLGoto.Type.JUMP;

				// When there is a %pc assignment as last statement in a sequence, turn it to a GOTO.
				// We cannot do that if it appears earlier, b/c we might lose changes to variables 
				// coming behind the %pc assignment!
				RTLStatement exitStatement = rtlBody.getLast();
				if (exitStatement instanceof AssignmentTemplate) {
					AssignmentTemplate assignment = (AssignmentTemplate)exitStatement;
					if (assignment.getLeftHandSide().equals(ExpressionFactory.pc)) {
						RTLGoto newGoto;
						RTLExpression rhs = assignment.getRightHandSide();
						if (rhs instanceof RTLConditionalExpression) {
							RTLConditionalExpression condExpr = (RTLConditionalExpression)rhs;
							if (condExpr.getTrueExpression() == ExpressionFactory.pc) {
								// conditional goto to false expression
								newGoto = new RTLGoto(condExpr.getFalseExpression(), 
										ExpressionFactory.createNot(condExpr.getCondition()), gotoType);
							} else if (condExpr.getFalseExpression() == ExpressionFactory.pc) {
								// conditional goto to true expression
								newGoto = new RTLGoto(condExpr.getTrueExpression(), 
										condExpr.getCondition(), gotoType);
							} else {
								logger.error("Dual branch in SSL definition: " + rtlBody);
								assert false;
								newGoto = new RTLGoto(rhs, gotoType);
							}
						} else {
							// unconditional goto
							newGoto = new RTLGoto(rhs, gotoType);
						}
						rtlBody = rtlBody.replace(assignment, newGoto);
					}
				}
				
				// If there is any pc-assignment, then add a goto to the end
				if (rtlBody.getDefinedVariables().contains(ExpressionFactory.pc)) {
					rtlBody.addLast(new RTLGoto(ExpressionFactory.pc, gotoType));
				}

			} else logger.debug("Null rtl body: " + proto);
			
			SSLInstruction instr = new SSLInstruction(proto.getName(), 
					proto.getParameters(), rtlBody);

			//logger.debug("Result:\n" + instr.getBody());

			instructions.put(instr.getName(), instr);
			String[] parts = name.split("\\.");
			if (!instrGroups.containsKey(parts[0])) {
				List<SSLInstruction> instrList = new LinkedList<SSLInstruction>();
				instrList.add(instr);
				instrGroups.put(parts[0], instrList);
			} else
				instrGroups.get(parts[0]).add(instr);
		}
		logger.debug("-- Suffix map has " + instrGroups.size() + " unique instructions.");
	}

}
