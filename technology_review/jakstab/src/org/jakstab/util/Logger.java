/*
 * Logger.java - This file is part of the Jakstab project.
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

package org.jakstab.util;

import java.io.PrintStream;

import org.jakstab.Options;

/**
 * @author Johannes Kinder
 */
public class Logger {

	public enum Level { FATAL, ERROR, WARN, INFO, VERBOSE, DEBUG }

	private static String globalPrefix = "";
	private static boolean showClass = false;

	public static Logger getLogger(Class<? extends Object> c) {
		return new Logger(c, System.out);
	}

	public static void setGlobalPrefix(String prefix) {
		globalPrefix = prefix + "\t";
	}

	private PrintStream out;
	private String prefix;
	
	private Logger(Class<? extends Object> clazz, PrintStream outStream) {
		this.out = outStream;
		this.prefix = (showClass ? (clazz.getSimpleName() + ":\t") : "");
	}

	private int getDebugLevel() {
		return Options.verbosity.getValue();
	}
	
	public boolean isDebugEnabled() {
		return Level.DEBUG.ordinal() <= getDebugLevel();
	}

	public boolean isVerboseEnabled() {
		return Level.VERBOSE.ordinal() <= getDebugLevel();
	}

	public boolean isInfoEnabled() {
		return Level.INFO.ordinal() <= getDebugLevel();
	}

	public void log(Level level) {
		if (level.ordinal() >= getDebugLevel())
			out.println();
	}

	public void log(Level level, Object message) {
		if (level.ordinal() <= getDebugLevel())
			out.println(globalPrefix + prefix + message);
	}

	public void log(Level level, Object message, Throwable t) {
		if (level.ordinal() <= getDebugLevel())
			out.println(globalPrefix + prefix + message + " " + t.getMessage());
	}

	public void logString(Level level, String string) {
		if (level.ordinal() <= getDebugLevel())
			out.print(globalPrefix + prefix + string);
	}

	public void debug() { 
		log(Level.DEBUG);
	}

	public void debug(Object message) { 
		log(Level.DEBUG, message);
	}

	public void debug(Object message, Throwable t) { 
		log(Level.DEBUG, message, t);
	}

	public void debugString(String message) {
		logString(Level.DEBUG, message);
	}

	public void verbose() { 
		log(Level.VERBOSE);
	}

	public void verbose(Object message) { 
		log(Level.VERBOSE, message);
	}

	public void verbose(Object message, Throwable t) { 
		log(Level.VERBOSE, message, t);
	}

	public void verboseString(String message) {
		logString(Level.VERBOSE, message);
	}

	public void info() { 
		log(Level.INFO);
	}

	public void info(Object message) { 
		log(Level.INFO, message);
	}

	public void infoString(String message) {
		logString(Level.INFO, message);
	}

	public void info(Object message, Throwable t) { 
		log(Level.INFO, message, t);
	}

	public void warn(Object message) { 
		log(Level.WARN, message);
	}

	public void warn(Object message, Throwable t) { 
		log(Level.WARN, message, t);
	}

	public void error(Object message) { 
		log(Level.ERROR, message);
	}

	public void error(Object message, Throwable t) { 
		log(Level.ERROR, message, t);
	}

	public void fatal(Object message) { 
		log(Level.FATAL, message);
	}

	public void fatal(Object message, Throwable t) { 
		log(Level.FATAL, message, t);
	}
}
