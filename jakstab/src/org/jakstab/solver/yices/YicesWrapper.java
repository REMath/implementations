/*
 * YicesWrapper.java - This file is part of the Jakstab project.
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

package org.jakstab.solver.yices;

import java.io.*;

import org.jakstab.Options;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class YicesWrapper {

	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(YicesWrapper.class);
	
	private static String outputFile;
	private static BufferedReader outputReader;
	private static int verbosity;
	public static int numContexts = 0;
	
	static {
		logger.debug("Initializing Yices library.");
		
		// Select matching Yices library		
		String uname = System.getProperty("os.name");
		String arch = System.getProperty("os.arch");
		String yicesJNIdir = Options.jakstabHome.concat("/lib/");
		// Windows on x86
		if (arch.endsWith("86") && uname.startsWith("Windows")) {
			logger.debug("-- Loading Yices core DLL.");
			System.load(yicesJNIdir.concat("win32/libyices.dll"));
			logger.debug("-- Loading JNI dll.");
			System.load(yicesJNIdir.concat("win32/YicesJNI.dll"));
		} 
		// Linux on x86
		else if (arch.endsWith("86") && uname.startsWith("Linux")) {
			logger.debug("-- Loading Yices 32-bit JNI library.");
			System.load(yicesJNIdir.concat("linux32/libYicesJNI.so"));
		} 
		// Linux on AMD64
		else if (arch.equals("amd64") && uname.startsWith("Linux")) {
			logger.debug("-- Loading Yices 64-bit JNI library.");
			System.load(yicesJNIdir.concat("linux64/libYicesJNI.so"));
		} 
		// Fail otherwise
		else {
			throw new RuntimeException("Unsupported architecture/OS combination for Yices-binding: " + arch + " and " + uname);
		}
		logger.verbose("Successfully loaded Yices v" + getVersion());

		setVerbosity(0);
		enableLogFile("yiceslog.txt");

		outputFile = new File(System.getProperty("java.io.tmpdir").concat("/yices.out")).getAbsolutePath();
		
		initYicesOutputReader();

		if (logger.isDebugEnabled()) {
			enableTypeChecker((short)1);
		} else {
			enableTypeChecker((short)0);
		}
	}
	
	/**
	 * Set Yices output file and attach a reader to it. For some reason, this needs
	 * to be redone every time a context is deleted.
	 */
	public static void initYicesOutputReader() {
		YicesWrapper.setOutputFile(outputFile);
		try {
			outputReader = new BufferedReader(new FileReader(outputFile));
		} catch (FileNotFoundException e) {
			logger.error("Yices output not found!");
		}
	}

	public static int getVerbosity() {
		return verbosity;
	}

	public static void main(String[] args) {
		System.out.println("Yices test.");
		/*String eax = "eax";
		
		YicesContext ctx = new YicesContext();
		ctx.declareVariable(eax, makeBVType(32));
		ctx.putRetractableAssertion(makeEquality(eax, makeBVConstant(32, 5)));
		System.out.println("SAT: " + ctx.check());
		ctx.putRetractableAssertion(makeOperation("bv-gt", eax, makeBVConstant(32, 10)));
		System.out.println("SAT: " + ctx.check());
		*/
		YicesSolver[] contexts = new YicesSolver[100];

		for (int i=0; i<contexts.length; i++) {
			contexts[i] = new YicesSolver();
			assert(contexts[i].isSatisfiable());
		}
		logger.info("Starting destroyContext loop");
		for (int i=0; i<contexts.length - 1; i++) {
			assert(contexts[i].isSatisfiable());
		}
		
		System.out.println("Done");
	}

	public static String makeAnd(String e1, String e2) {
		return makeOperation("and", e1, e2); 
	}

	public static String makeBVAdd(String e1, String e2) {
		return makeOperation("bv-add", e1, e2);
	}

	public static String makeBVAnd(String e1, String e2) {
		return makeOperation("bv-and", e1, e2); 
	}

	public static String makeBVConstant(int size, long value) {
		assert size > 0 : "Trying to make constant of negative length!";
		return makeOperation("mk-bv", Integer.toString(size), Long.toString(value));
	}

	public static String makeBVExtract(String expr, int begin, int end) {
		return makeOperation("bv-extract", Integer.toString(end), 
				Integer.toString(begin), expr);
	}

	public static String makeBVGreaterOrEqual(String e1, String e2) {
		return makeOperation("bv-ge", e1, e2);
	}

	public static String makeBVGreaterThan(String e1, String e2) {
		return makeOperation("bv-gt", e1, e2);
	}

	public static String makeBVLessOrEqual(String e1, String e2) {
		return makeOperation("bv-le", e1, e2);
	}
	
	public static String makeBVLessThan(String e1, String e2) {
		return makeOperation("bv-lt", e1, e2);
	}
	
	public static String makeBVMul(String e1, String e2) {
		return makeOperation("bv-mul", e1, e2);
	}
	
	public static String makeBVNeg(String e) {
		return makeOperation("bv-neg", e);
	}
	
	public static String makeBVNot(String e1, String e2) {
		return makeOperation("bv-not", e1, e2); 
	}
	
	public static String makeBVOr(String e1, String e2) {
		return makeOperation("bv-or", e1, e2); 
	}
	
	public static String makeBVSignedGreaterOrEqual(String e1, String e2) {
		return makeOperation("bv-sge", e1, e2);
	}
	
	public static String makeBVSignedGreaterThan(String e1, String e2) {
		return makeOperation("bv-sgt", e1, e2);
	}
	
	public static String makeBVSignedLessOrEqual(String e1, String e2) {
		return makeOperation("bv-sle", e1, e2);
	}
	
	public static String makeBVSignedLessThan(String e1, String e2) {
		return makeOperation("bv-slt", e1, e2);
	}
	
	public static String makeBVSignExtend(String expr, int count) {
		return makeOperation("bv-sign-extend", expr, Integer.toString(count));
	}
	
	public static String makeBVSub(String e1, String e2) {
		return makeOperation("bv-sub", e1, e2);
	}
	
	public static String makeBVType(int size) {
		return makeOperation("bitvector", Integer.toString(size));
	}
	
	public static String makeBVXor(String e1, String e2) {
		return makeOperation("bv-xor", e1, e2); 
	}
	
	public static String makeBVZeroExtend(String expr, int zeroes) {
		assert zeroes > 0 : "Trying to add negative amount of zeroes";
		return makeBVConcat(makeBVConstant(zeroes, 0), expr);
	}
	
	public static String makeBVConcat(String e1, String e2) {
		return makeOperation("bv-concat", e1, e2);
	}
	
	public static String makeBVShiftRight(String e1, int shiftCount) {
		return makeOperation("bv-shift-right0", e1, Integer.toString(shiftCount));
	}
	
	public static String makeBVShiftLeft(String e1, int shiftCount) {
		return makeOperation("bv-shift-left0", e1, Integer.toString(shiftCount));
	}
	
	public static String makeDisequality(String e1, String e2) {
		return makeOperation("/=", e1, e2); 
	}
	
	public static String makeEquality(String e1, String e2) {
		return makeOperation("=", e1, e2); 
	}
	
	public static String makeImplication(String a, String b) {
		return makeOperation("=>", a, b);
	}
	
	public static String makeITE(String i, String t, String e) {
		return makeOperation("ite", i, t, e);
	}
	
	public static String makeOperation(String op, String... arg) {
		StringBuilder s = new StringBuilder(256);
		s.append('(');
		s.append(op);
		for (int i=0; i<arg.length; i++) {
			s.append(' ');
			s.append(arg[i]);
		}
		s.append(')');
		return s.toString();
	}
	
	public static String makeOr(String e1, String e2) {
		return makeOperation("or", e1, e2); 
	}
	
	public static String makeXor(String e1, String e2) {
		return makeOperation("xor", e1, e2); 
	}
	
	public static void setVerbosity(int v) {
		verbosity = v;
		setVerbosity((short) v);
	}

	/**
	 * Destroy Context sometimes disables output redirection of Yices (bug in Yices?),
	 * so we never destroy contexts for now but reuse them. 
	 */
	static void destroyContext(long ctx) {
		deleteContext(ctx);
		numContexts--;
	}

	static synchronized native long createContext();
	
	static synchronized native String getLastErrorMessage();
	
	static String getNextOutputLine() {
		String line = null;
		try {
			line = outputReader.readLine();
		} catch (IOException e) {
			throw new RuntimeException("Cannot open temporary yices output file!");
		}
		return line ;
	}

	public synchronized static native String getVersion();

	static synchronized native short inconsistent(long ctx);

	static synchronized native short read(long ctx, String cmd);

	private synchronized static native void deleteContext(long ctx);
	
	private synchronized static native void enableLogFile(String filename);

	private synchronized static native void enableTypeChecker(short flag);

	private synchronized static native void setOutputFile(String filename);

	private synchronized static native void setVerbosity(short l);

	private YicesWrapper() {
	}
}
