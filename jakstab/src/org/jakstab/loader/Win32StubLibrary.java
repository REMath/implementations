/*
 * Win32StubLibrary.java - This file is part of the Jakstab project.
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

package org.jakstab.loader;

import java.io.*;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.jakstab.Options;
import org.jakstab.Program;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.asm.SymbolFinder;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.ssl.Architecture;

/**
 * @author Johannes Kinder
 */
public class Win32StubLibrary implements StubProvider {
	
	private enum mjFunctionCode {
		DRIVER_INIT(-3),		// Not really part of MajorFunction array, but
		DRIVER_STARTIO(-2),		// directly precedes it in DriverObject
		DRIVER_UNLOAD(-1),
		IRP_MJ_CREATE(0x00),
		IRP_MJ_CREATE_NAMED_PIPE(0x01),
		IRP_MJ_CLOSE(0x02),
		IRP_MJ_READ(0x03),
		IRP_MJ_WRITE(0x04),
		IRP_MJ_QUERY_INFORMATION(0x05),
		IRP_MJ_SET_INFORMATION(0x06),
		IRP_MJ_QUERY_EA(0x07),
		IRP_MJ_SET_EA(0x08),
		IRP_MJ_FLUSH_BUFFERS(0x09),
		IRP_MJ_QUERY_VOLUME_INFORMATION(0x0a),
		IRP_MJ_SET_VOLUME_INFORMATION(0x0b),
		IRP_MJ_DIRECTORY_CONTROL(0x0c),
		IRP_MJ_FILE_SYSTEM_CONTROL(0x0d),
		IRP_MJ_DEVICE_CONTROL(0x0e),
		IRP_MJ_INTERNAL_DEVICE_CONTROL(0x0f),
		IRP_MJ_SHUTDOWN(0x10),
		IRP_MJ_LOCK_CONTROL(0x11),
		IRP_MJ_CLEANUP(0x12),
		IRP_MJ_CREATE_MAILSLOT(0x13),
		IRP_MJ_QUERY_SECURITY(0x14),
		IRP_MJ_SET_SECURITY(0x15),
		IRP_MJ_POWER(0x16),
		IRP_MJ_SYSTEM_CONTROL(0x17),
		IRP_MJ_DEVICE_CHANGE(0x18),
		IRP_MJ_QUERY_QUOTA(0x19),
		IRP_MJ_SET_QUOTA(0x1a),
		IRP_MJ_PNP(0x1b);
		
		private final int code;

		private mjFunctionCode(int code) {
			this.code = code;
		}
		
		@SuppressWarnings("unused")
		public mjFunctionCode fromCode(int whichCode) {
			assert mjFunctionCode.values()[whichCode].code == whichCode;
			return mjFunctionCode.values()[whichCode];
		}
		
	}
	
	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(Win32StubLibrary.class);

	private static final String stubDir =  Options.jakstabHome + "/stubs/win32/";
	private static final String jakstab_internal = "jakstab.dll";
	
	static class Stub {
		public int callingConvention;
		public String name;
		public int stackIncrement;
		public boolean returns;
		public Stub(int cc, String n, int s, boolean r) {
			callingConvention = cc; name = n; stackIncrement = s; returns = r;
		}
	}

	private Architecture arch;
	private final Map<String,Map<String,Stub>> stubMap;
	private Map<String,Map<String,AbsoluteAddress>> activeStubs;
	private Map<AbsoluteAddress,String> addressMap;
	private int impId;
	private Set<String> loadedDefFiles = new FastSet<String>();
	private RTLExpression arg0;
	private RTLExpression arg1;
	private SymbolFinder symFinder;
	
	private final void registerStub(String library, int callingConvention, String name, int stackIncrement, boolean returns) {
		Map<String, Stub> exportMap = stubMap.get(library);
		if (exportMap == null) {
			exportMap = new HashMap<String, Stub>();
			stubMap.put(library, exportMap);
		}
		if (!exportMap.containsKey(name))
			exportMap.put(name, new Stub(callingConvention, name, stackIncrement, returns));
	}
	
	public Win32StubLibrary(Architecture arch) {
		this.arch = arch;
		activeStubs = new HashMap<String, Map<String, AbsoluteAddress>>();
		stubMap = new HashMap<String, Map<String,Stub>>();
		addressMap = new HashMap<AbsoluteAddress, String>();
		impId = 0;
		arg0 = ExpressionFactory.createMemoryLocation(ExpressionFactory.createPlus(arch.stackPointer(), ExpressionFactory.createNumber(4, 32)), 32);
		arg1 = ExpressionFactory.createMemoryLocation(ExpressionFactory.createPlus(arch.stackPointer(), ExpressionFactory.createNumber(8, 32)), 32);
	}
	
	private void loadDefFile(String library) {
		// Add to loaded files even if we fail to load it to avoid multiple warnings
		loadedDefFiles.add(library);
		try {
			String baseName;
			int dotIndex = library.lastIndexOf('.');
			if (dotIndex > 0) baseName = library.substring(0, dotIndex);
			else baseName = library;
			
			File defFile = new File(stubDir + baseName + ".def");
			if (defFile.canRead()) {
				
				BufferedReader in = new BufferedReader(new FileReader(defFile));
				boolean inExports = false; 
				String line;
				while ((line = in.readLine()) != null) {
					line = line.trim();

					// Skip empty lines
					if (line.length() == 0)
						continue;
					
					// ignore comments and preprocessor directives
					if (line.startsWith(";") || line.startsWith("#")) continue;
					if (line.startsWith("EXPORTS")) {
						inExports = true;
						continue;
					}
					if (!inExports) continue;
					// parse exported function:
					
					int callingConvention = STDCALL;
					boolean returns = true;
					int stackIncrement = 0;

					int i = line.length();
					if (line.length() > 4 && line.substring(i - 4, i).equals("DATA")) {
						callingConvention = EXTERNAL_VARIABLE;
						i -= 4;
						while (i >= 1 && line.charAt(i - 1) == ' ')
							i--;
					}
					int finalAt = line.lastIndexOf('@');
					if (finalAt >= 0 && finalAt < i - 1) {
						try {
							stackIncrement = Integer.parseInt(line.substring(finalAt + 1, i));
							i = finalAt;
						} catch (NumberFormatException e) {
							// Failed to parse, the last @ is still within the function name, so leave i at where it is							
						}
					}
					
					// Parse prefixes
					int start = 0;
					prefixParse: for (; start <= i; start++) {
						char c = line.charAt(start);
						switch (c) {
						case '@':
							callingConvention = FASTCALL;
							break;
						case '!':
							returns = false;
							break;
						default:
							break prefixParse; 
						}
					}
					
					String name = line.substring(start, i);
					
					//logger.debug("Registering " + name.toString() + "@" + library + " " + callingConvention + " " + stackIncrement + " " + returns);
					registerStub(library, callingConvention, name, stackIncrement, returns);
					
				} /* end file reading while */
				

			} else {
				logger.error("Cannot find definition file " + defFile.getAbsolutePath() + "!");
			}
			
		} catch (IOException e) {
			throw new RuntimeException("Error reading definition file. " + e.getMessage());
		}
		

	}

	

	private AbsoluteAddress createStubInstance(String library, String function) {
		int callingConvention = CDECL;
		int stackIncrement = 0;
		boolean returns = true;

		impId += 0x10;
		AbsoluteAddress address = new AbsoluteAddress(STUB_BASE + impId);

		StatementSequence seq = new StatementSequence();
		
		if (library.equals(jakstab_internal)) {
			
			if (function.equals("_jakstab_print_driver_object@4")) {
				logger.debug("Intercepting " + function);
				stackIncrement = 8;
				RTLVariable driverObject = ExpressionFactory.createVariable("driverObject", 32);
				int mjFunArray = 0x38;
				seq.addLast(new RTLVariableAssignment(32, driverObject, ExpressionFactory.createMemoryLocation(
						ExpressionFactory.createPlus(arch.stackPointer(), ExpressionFactory.createNumber(4)), 
						arch.stackPointer().getBitWidth())));

				for (mjFunctionCode mjFun : mjFunctionCode.values()) {
					seq.addLast(new RTLDebugPrint(
							"Driver registers " + mjFun.name() + "(DriverObject[0x" + 
							Integer.toHexString(mjFunArray + mjFun.code * 4) + "])",
							ExpressionFactory.createMemoryLocation(
									ExpressionFactory.createPlus(
											driverObject, 
											ExpressionFactory.createNumber(mjFunArray + mjFun.code * 4, 32)
									),
									32)
					));
				}
			} else {
				// Assume these are all variables
				logger.debug("Created global variable at " + address); 
				return address;
			}

		} else {



			if (!loadedDefFiles.contains(library)) {
				// search for def file
				loadDefFile(library);
			}

			if (stubMap.containsKey(library) && stubMap.get(library).containsKey(function)) {
				Stub stub = stubMap.get(library).get(function);
				callingConvention = stub.callingConvention;
				returns = stub.returns;
				stackIncrement = stub.stackIncrement;
				if (callingConvention == FASTCALL)
					stackIncrement = Math.max(0, stackIncrement - 8);
			} else {
				logger.error("Using default stub for function " + function + "@" + library + "! Bad stack height assertions likely.");
			}

			if (callingConvention == EXTERNAL_VARIABLE) {
				// no function, but a variable!
				return address;
			}

			// pop PC
			stackIncrement += arch.programCounter().getBitWidth() / 8;


			// GetProcAddress is special
			if (library.toUpperCase().startsWith("KERNEL32") && function.equals("GetProcAddress")) {
				
				if (Options.getProcAddress.getValue() == 0) {
					RTLExpression loadExpression = ExpressionFactory.createSpecialExpression(RTLSpecialExpression.GETPROCADDRESS, arg0, arg1); 
					seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%eax"), loadExpression));
				} else if (Options.getProcAddress.getValue() == 1) {
					logger.warn("Havocing GetProcAddress is not yet implemented!");
					assert false;
					seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%eax"), ExpressionFactory.nondet(32)));
				} else if (Options.getProcAddress.getValue() == 2) {
					seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%eax"), ExpressionFactory.nondet(32)));
				}
			} else if (library.toUpperCase().startsWith("KERNEL32") && function.startsWith("GetModuleHandle")) {
				// This function returns either 0 or a valid handle to the given module
				// This hack here uses the string as the handle value, not very nice
				//seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%eax"), arg0));
				seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%eax"), ExpressionFactory.nondet(32)));
			} else {
				// overwrite registers according to ABI
				seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%eax"), ExpressionFactory.nondet(32)));
			}
			seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%ecx"), ExpressionFactory.nondet(32)));
			seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%edx"), ExpressionFactory.nondet(32)));
		}

		// store return address in retaddr
		if (returns) {
			seq.addLast(new RTLVariableAssignment(32, Program.getProgram().getArchitecture().returnAddressVariable(), 
					ExpressionFactory.createMemoryLocation(arch.stackPointer(), 
							arch.stackPointer().getBitWidth())
			));
		}

		
		// adjust stack pointer
		seq.addLast(new RTLVariableAssignment(arch.stackPointer().getBitWidth(), 
				arch.stackPointer(), 
				ExpressionFactory.createPlus( 
						arch.stackPointer(), 
						ExpressionFactory.createNumber(stackIncrement, arch.stackPointer().getBitWidth())
				)
		));

		if (returns) {
			// Read return address from temporary variable
			seq.addLast(new RTLGoto(Program.getProgram().getArchitecture().returnAddressVariable(), RTLGoto.Type.RETURN));
		} else {
			// artificial termination statement
			seq.addLast(new RTLHalt());
		}
		
		int rtlId = 0;
		for (RTLStatement stmt : seq) {
			stmt.setLabel(address, rtlId++);
			stmt.setNextLabel(new Location(address, rtlId));
		}
		seq.getLast().setNextLabel(null);

		// add stub statements to program
		for (RTLStatement s : seq)
			Program.getProgram().putStatement(s);

		return address;
	}

	@Override
	public AbsoluteAddress resolveSymbol(String library, String symbol) {
		AbsoluteAddress functionAddress;
		if (library == null) {
			// no library means this symbol comes from an obj.
			
			// We currently allow a trick for objs to refer directly to external library variables
			// The format is: jakstab$link$library_ext$symbol
			//                01234567890123
			if (symbol.startsWith("jakstab$link$")) {
				symbol = symbol.substring(13);
				int underscore = symbol.indexOf("$");
				library = symbol.substring(0, underscore).replace("_", ".");
				symbol = symbol.substring(underscore + 1);
				logger.debug("Resolving pseudo-import " + symbol + "@" + library);
			} else {
				logger.debug("Resolving non-import symbol " + symbol);
				library = jakstab_internal;
			}
		} else {
			library = library.toLowerCase();
		}
		
		if (activeStubs.containsKey(library) && activeStubs.get(library).containsKey(symbol))
			functionAddress = activeStubs.get(library).get(symbol);
		else {
			// create a new stub instance
			functionAddress = createStubInstance(library, symbol);
			
			if (!activeStubs.containsKey(library))
				activeStubs.put(library, new HashMap<String, AbsoluteAddress>());
			activeStubs.get(library).put(symbol, functionAddress);
			addressMap.put(functionAddress, symbol);
			
			logger.debug("Created new stub for " + symbol + "@" + library);
		}
		return functionAddress;
	}

	@Override
	public SymbolFinder getSymbolFinder() {
		if (symFinder == null) {
			symFinder = new SymbolFinder() {
				
				@Override
				public boolean hasSymbolFor(AbsoluteAddress va) {
					return addressMap.containsKey(va);
				}
				
				@Override
				public String getSymbolFor(AbsoluteAddress va) {
					String sym = addressMap.get(va);
					if (sym == null) return va.toString();
					else return sym;
				}
				
				@Override
				public String getSymbolFor(long address) {
					return getSymbolFor(new AbsoluteAddress(address));
				}
			};
		}
		return symFinder;
	}
	
}
