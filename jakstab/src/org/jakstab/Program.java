/*
 * Program.java - This file is part of the Jakstab project.
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

package org.jakstab;

import java.io.File;
import java.io.IOException;
import java.util.*;

import org.jakstab.util.Logger;
import org.jakstab.asm.*;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.disasm.DisassemblyException;
import org.jakstab.loader.*;
import org.jakstab.loader.elf.ELFModule;
import org.jakstab.loader.pe.*;
import org.jakstab.rtl.expressions.SetOfVariables;
import org.jakstab.rtl.statements.RTLHalt;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.rtl.statements.StatementSequence;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.FastSet;


/**
 * There is one singleton Program object for all modules currently under analysis.
 * It stores all non-analysis information about the analyzed programs, including 
 * statements, the current control flow graph, and symbols.
 * 
 * @author Johannes Kinder
 */
public final class Program {
	
	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(Program.class);
	private static Program programInstance;

	/**
	 * Get the singleton Program object.
	 * 
	 * @return the singleton instance of the Program class
	 */
	public static Program getProgram() {
		return programInstance;
	}
	
	/**
	 * Initially creates the Program object.
	 *  
	 * @param arch An Architecture object with architecture specific information
	 * @return the new singleton instance of the Program class
	 */
	public static Program createProgram(Architecture arch) {
		//assert programInstance == null;
		programInstance = new Program(arch);
		return programInstance;
	}

	private final Architecture arch;
	private Location start;
	private Map<Location, RTLStatement> statementMap;
	private Map<AbsoluteAddress, Instruction> assemblyMap;
	private ExecutableImage mainModule;
	private List<ExecutableImage> modules;
	private Set<CFAEdge> cfa;
	private final Map<String, ExportedSymbol> exportedSymbols;
	private final Set<UnresolvedSymbol> unresolvedSymbols;
	private Set<Location> unresolvedBranches;
	private StubProvider stubLibrary;
	private Harness harness;
	
	public enum TargetOS {WINDOWS, LINUX, UNKNOWN};
	private TargetOS targetOS;
	
	private Program(Architecture arch) {
		this.arch = arch;
		this.targetOS = TargetOS.UNKNOWN;

		modules = new LinkedList<ExecutableImage>();
		assemblyMap = new TreeMap<AbsoluteAddress, Instruction>();
		statementMap = new HashMap<Location, RTLStatement>(2000);
		cfa = new FastSet<CFAEdge>();
		exportedSymbols = new HashMap<String, ExportedSymbol>();
		unresolvedSymbols = new FastSet<UnresolvedSymbol>();
		
		unresolvedBranches = new FastSet<Location>();
	}
	
	/**
	 * Loads the module containing the main function. This function should be called last
	 * for correct symbol resolution.
	 * 
	 * @param moduleFile the file to load
	 * @return the ExecutableImage class for the loaded module
	 * @throws IOException
	 * @throws BinaryParseException
	 */
	public ExecutableImage loadMainModule(File moduleFile) throws IOException, BinaryParseException {
		ExecutableImage module = loadModule(moduleFile);
		mainModule = module;
		setEntryAddress(module.getEntryPoint());
		installStubs();
		return module;
	}
	
	/**
	 * Loads a secondary (library or stub) module for analysis. Automatically determines 
	 * the correct file type.
	 *  
	 * @param moduleFile the file to load
	 * @return the ExecutableImage class for the loaded module
	 * @throws IOException
	 * @throws BinaryParseException
	 */
	public ExecutableImage loadModule(File moduleFile) throws IOException, BinaryParseException {
		// First try to load it as a PE file, then object file, ELF and finally raw binary code
		// The right thing to do would be some smart IDing of the file type, but 
		// this exception chaining works for now...		
		ExecutableImage module = null;
		try {
			module = new PEModule(moduleFile, getArchitecture());
			targetOS = TargetOS.WINDOWS;
		} catch (BinaryParseException e) {
			try {
				module = new ObjectFile(moduleFile, getArchitecture());
			} catch (BinaryParseException e2) {
				try {
					module = new ELFModule(moduleFile, getArchitecture());
					targetOS = TargetOS.LINUX;
				} catch (BinaryParseException e3) {
					module = new RawModule(moduleFile, getArchitecture());
				}
			}
		}
		
		for (ExecutableImage existingModule : modules) {
			if (existingModule.getMaxAddress().getValue() >= module.getMinAddress().getValue() &&
					existingModule.getMinAddress().getValue() <= module.getMaxAddress().getValue()) {
				throw new RuntimeException("Virtual addresses of modules overlap!");
			}
		}
		
		
		modules.add(module);
		unresolvedSymbols.addAll(module.getUnresolvedSymbols());
		for (ExportedSymbol symbol : module.getExportedSymbols()) {
			exportedSymbols.put(removeDecoration(symbol.getName()), symbol);
		}
		resolveSymbols();
		return module;
	}
	
	private String removeDecoration(String s) {
		if (s.charAt(0) == '@' || s.charAt(0) == '_')
			s = s.substring(1);
		int i = s.indexOf('@');
		if (i >= 0)
			s = s.substring(0, i); 
		return s;
	}
	
	/**
	 * Resolves symbols between the loaded modules. 
	 */
	private void resolveSymbols() {
		Iterator<UnresolvedSymbol> sIter = unresolvedSymbols.iterator();
		while (sIter.hasNext()) {
			UnresolvedSymbol unresolvedSymbol = sIter.next();
			ExportedSymbol symbol = exportedSymbols.get(removeDecoration(unresolvedSymbol.getName()));
			
			if (symbol != null) {
				logger.debug("Resolving symbol " + unresolvedSymbol.getName());
				unresolvedSymbol.resolve(symbol.getAddress());
				sIter.remove();
			}
		}
	}
	
	/**
	 * Returns the address of the given procedure within the given library. Procedures
	 * present within the analyzed modules are given precedence over stub functions.
	 * 
	 * @param library 
	 * @param procedure
	 * @return the virtual address of the procedure
	 */
	public AbsoluteAddress getProcAddress(String library, String procedure) {
		ExportedSymbol expSymbol = exportedSymbols.get(procedure);
		if (expSymbol != null) {
			return expSymbol.getAddress();
		} else {
			return stubLibrary.resolveSymbol(library, procedure);
		}
	}
	
	/**
	 * For all unresolved symbols, install simple stubs.
	 */
	public void installStubs() {
		if (mainModule instanceof AbstractCOFFModule) {
			stubLibrary = new Win32StubLibrary(arch);
		} else if (mainModule instanceof ELFModule){
			stubLibrary = new LinuxStubLibrary(arch);
		}
		
		Iterator<UnresolvedSymbol> sIter = unresolvedSymbols.iterator();
		while (sIter.hasNext()) {
			UnresolvedSymbol unresolvedSymbol = sIter.next();
			AbsoluteAddress address = stubLibrary.resolveSymbol(unresolvedSymbol.getFromLibrary(), unresolvedSymbol.getName());
			if (address != null) {
				//logger.debug("Installing stack height stub for " + unresolvedSymbol.getName());
				unresolvedSymbol.resolve(address);
				sIter.remove();
			}
		}
		
		if (!unresolvedSymbols.isEmpty()) 
			logger.warn("Unresolved symbols remaining: " + unresolvedSymbols);
	}
	
	/**
	 * Install a harness that sets up the symbolic environment before calling main
	 * and provides a return point with a termination statement.
	 * 
	 * @param harness the harness object to install
	 */
	public void installHarness(Harness harness) {
		this.harness = harness;
		harness.install(this);
	}
	
	/**
	 * Set the program entry point to the given label.
	 * @param label the new entry point
	 */
	public void setStart(Location label) {
		this.start = label;
	}

	/**
	 * Set the program entry point to the given address.
	 * @param entryAddress the new entry address
	 */
	public void setEntryAddress(AbsoluteAddress entryAddress) {
		setStart(new Location(entryAddress));
	}
	
	/**
	 * Get the main module.  
	 * @return the main module
	 */
	public ExecutableImage getMainModule() {
		return mainModule;
	}
	
	/**
	 * Get the module that contains the specified virtual address at runtime.
	 * @param a a virtual address
	 * @return the module to which the given virtual address belongs. 
	 */
	public ExecutableImage getModule(AbsoluteAddress a) {
		for (ExecutableImage module : modules) {
			if (module.getFilePointer(a) >= 0)
				return module;
		}
		return null;
	}
	
	public Iterator<AbsoluteAddress> codeAddressIterator() {
		return getMainModule().codeBytesIterator();
	}
	
	/**
	 * Get all statements in the Program.
	 * 
	 * @return a collection of all statements in all loaded modules.
	 */
	public Collection<RTLStatement> getStatements() {
		return statementMap.values();
	}

	/**
	 * Get the statement at a specific label. If there is no statement stored, attempts
	 * to disassemble the instruction at the label's virtual address. If the address is
	 * outside of the file area, logs an error and returns a Halt statement by default.
	 * 
	 * @param label The label for which to get the statement
	 * @return The statement object at label.
	 */
	public final RTLStatement getStatement(Location label) {
		if (!statementMap.containsKey(label)) {
			AbsoluteAddress address = label.getAddress();
			Instruction instr = getInstruction(address);
			// If we did not get an instruction, add an artificial Halt for recovery
			if (instr == null) {
				RTLHalt halt = new RTLHalt();
				halt.setLabel(label);
				putStatement(halt);
				logger.error("ERROR: Replacing unknown instruction with HALT.");
				if (Options.debug.getValue())
					throw new DisassemblyException("Disassembly failed at " + address);
			} else {
				StatementSequence seq = arch.getRTLEquivalent(address, instr);
				for (RTLStatement s : seq) {
					putStatement(s);
				}
				assert statementMap.containsKey(label) : "Disassembly did not produce label: " + label;
			}
		}
		return statementMap.get(label);
	}
	
	/**
	 * Stores a statement in the program. If a statement already exists with the same
	 * label, it is replaced.
	 * 
	 * @param stmt The statement to be stored. Has to contain a proper label.
	 */
	public final void putStatement(RTLStatement stmt) {
		RTLStatement existing = statementMap.get(stmt.getLabel());
		if (existing != null) {
			if (existing.equals(stmt)) return;
			logger.debug("Replacing statement at " + stmt.getLabel());
		}
		statementMap.put(stmt.getLabel(), stmt);
	}
	
	public boolean containsLabel(Location label) {
		return statementMap.containsKey(label);
	}

	public final int getStatementCount() {
		return statementMap.size();
	}

	public final int getInstructionCount() {
		return assemblyMap.size();
	}
	
	public Harness getHarness() {
		return harness;
	}
	
	/**
	 * Gets the assembly instruction at the specified virtual address.
	 * @param address a virtual address
	 * @return the assembly instruction at the specified address
	 */
	public final Instruction getInstruction(AbsoluteAddress address) {

		Instruction instr = assemblyMap.get(address);
		if (instr != null) {
			return instr;
		} else {
			// No real instructions in prologue/epilogue
			if (harness.contains(address) || address.getValue() >= StubProvider.STUB_BASE)
				return null;
			
			ExecutableImage module = getModule(address);

			long fp = -1;
			if (module == null) {
				logger.error("No module for address " + address + ". Cannot disassemble instruction!");
			} else {
				fp = module.getFilePointer(address);
				// Also check whether fp is out of the int range, since the X86Disassembler actually
				// performs this cast in its implementation.
				if (fp < 0 || (int)fp < 0) {
					logger.error("Requested instruction outside of file area: " + address);
				} else {
					if (!module.isCodeArea(address)) {
						logger.error("Requested instruction outside code section: " + address);
						return null;
					}
					instr = module.getDisassembler().decodeInstruction(fp);
					if (instr == null) {
						logger.error("Instruction could not be disassembled at: " + address);
					}
				}
			}

			if (instr != null)
				putInstruction(address, instr);
			return instr;
		}
	}

	/**
	 * Stores an assembly instruction at the given address, overwriting
	 * any existing instruction.
	 * @param addr the virtual address to save the instruction at
	 * @param instr the assembly instruction
	 * @return true if there was no instruction stored for that address before, false otherwise. 
	 */
	public final boolean putInstruction(AbsoluteAddress addr, Instruction instr) {
		//logger.info(addr + " " + instr.toString(addr.getValue(), new DummySymbolFinder()));
		return assemblyMap.put(addr, instr) == null;
	}
	
	/**
	 * Get the string representation of the assembly instruction at the given address.
	 * @param addr a virtual address
	 * @return a string representation of the assembly code at the given address
	 */
	public String getInstructionString(AbsoluteAddress addr) {
		Instruction instr = getInstruction(addr);
		if (instr == null) return "NON_EXISTENT";
		return instr.toString(addr.getValue(), symbolFinder(addr));
	}
	
	public String getSymbolFor(Location label) {
		SymbolFinder symFinder = symbolFinder(label.getAddress());
		if (symFinder.hasSymbolFor(label.getAddress())) {
			return symFinder.getSymbolFor(label.getAddress());
		} else {
			return label.toString();
		}
	}
	
	public String getSymbolFor(AbsoluteAddress addr) {
		return symbolFinder(addr).getSymbolFor(addr);
	}
	
	private SymbolFinder symbolFinder(AbsoluteAddress addr) {
		if (addr.getValue() >= StubProvider.STUB_BASE)
			return stubLibrary.getSymbolFinder();
		
		ExecutableImage module = getModule(addr);
		return (module == null) ? new DummySymbolFinder() : module.getSymbolFinder();
	}
	
	public Set<Location> getUnresolvedBranches() {
		return unresolvedBranches;
	}

	public void setUnresolvedBranches(Set<Location> unresolvedBranches) {
		this.unresolvedBranches = unresolvedBranches;
	}

	/**
	 * @return the assemblyMap
	 */
	public final Map<AbsoluteAddress, Instruction> getAssemblyMap() {
		return assemblyMap;
	}

	public TargetOS getTargetOS() {
		return targetOS;
	}

	/**
	 * Returns all variables used in the program. At the current state of
	 * the implementation, this includes only registers and flags.
	 * 
	 * @return A set containing all variables used in this program.
	 */
	public SetOfVariables getUsedVariables() {
		SetOfVariables result = new SetOfVariables();
		for (CFAEdge edge : cfa)
			result.addAll(((RTLStatement)edge.getTransformer()).getUsedVariables());
		return result;
	}

	
	public Architecture getArchitecture() {
		return arch;
	}
	
	public Collection<ExportedSymbol> getSymbols() {
		return exportedSymbols.values();
	}
	
	public Set<CFAEdge> getCFA() {
		return Collections.unmodifiableSet(cfa);
	}

	public void setCFA(Set<CFAEdge> cfa) {
		this.cfa = cfa;
	}

	public Location getStart() {
		return start;
	}
	
	public int countIndirectBranches() {
		int res = 0;
		for (Map.Entry<AbsoluteAddress, Instruction> entry : assemblyMap.entrySet()) {
			Instruction instr = entry.getValue();
			
			if (instr instanceof BranchInstruction) {
				BranchInstruction branch = (BranchInstruction)instr;
				if (branch.isIndirect()) {
					// if branch target is not a memory operand pointing into a static data area of the binary (imports)
					if (branch.getBranchDestination() instanceof MemoryOperand) {
						MemoryOperand memOp = (MemoryOperand)branch.getBranchDestination();
						// Import calls have only displacement
						if (memOp.getBase() == null && memOp.getIndex() == null) {
							AbsoluteAddress disp = new AbsoluteAddress(memOp.getDisplacement());
							// Check whether displacement points into import table
							ExecutableImage module = getModule(disp);
							if (module instanceof PEModule && ((PEModule)module).getImportTable().containsKey(disp))
								continue;
						}
					}
					res++;
					//logger.verbose(entry.getKey() + "\t" + getInstructionString(entry.getKey()));
				}
			}
		}
		return res;
	}
}
