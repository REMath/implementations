/*
 * AnalysisManager.java - This file is part of the Jakstab project.
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
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.jakstab.analysis.ConfigurableProgramAnalysis;
import org.jakstab.util.Logger;

public class AnalysisManager {

	private static final Logger logger = Logger.getLogger(AnalysisManager.class);
	private static final AnalysisManager instance = new AnalysisManager();

	public static AnalysisManager getInstance() {
		return instance;
	}
	
	private Map<Character, Class<? extends ConfigurableProgramAnalysis>> shortHandMap;
	private Map<Class<? extends ConfigurableProgramAnalysis>, AnalysisProperties> analysisProperties;
	
	private AnalysisManager() {
		
		shortHandMap = new HashMap<Character, Class<? extends ConfigurableProgramAnalysis>>();
		analysisProperties = new HashMap<Class<? extends ConfigurableProgramAnalysis>, AnalysisProperties>();
		
		// Enumerate all analyses and register them
		String pkg = "org.jakstab.analysis";
  		File dir = new File(Options.jakstabHome + "/bin/" + pkg.replace(".", "/"));
		List<Class<? extends ConfigurableProgramAnalysis>> classes = findCPAClasses(dir, pkg);
		for(Class<? extends ConfigurableProgramAnalysis> cpaClass : classes) {
			AnalysisProperties aProps = new AnalysisProperties();
			try {
				//logger.debug("Trying to register " + cpaClass.getSimpleName());
				cpaClass.getMethod("register", AnalysisProperties.class).invoke(cpaClass, aProps);
				if (aProps.getShortHand() != ' ') {
					if (shortHandMap.containsKey(aProps.getShortHand())) {
						logger.fatal("Duplicate short hand '" + aProps.getShortHand() + "' registered by " + 
								shortHandMap.get(aProps.getShortHand()).getSimpleName() + " and " + cpaClass.getSimpleName() + ".");
					}
					shortHandMap.put(aProps.getShortHand(), cpaClass);
				}
				analysisProperties.put(cpaClass, aProps);
				// apply properties
			} catch (Exception e) {
				logger.warn("Failed to register " + cpaClass.getSimpleName());
				if (e instanceof RuntimeException) 
					e.printStackTrace();
			}
		}

	}
	
	public ConfigurableProgramAnalysis createAnalysis(char shortHand) {
		Class<? extends ConfigurableProgramAnalysis> cpaClass = shortHandMap.get(shortHand);
		
		if (cpaClass == null)
			return null;
		
		try {
			return cpaClass.newInstance();
		} catch (InstantiationException e) {
			e.printStackTrace();
			throw new RuntimeException(e);
		} catch (IllegalAccessException e) {
			e.printStackTrace();
			throw new RuntimeException(e);
		}
	}
	
	public String getName(char shortHand) {
		Class<? extends ConfigurableProgramAnalysis> cpaClass = shortHandMap.get(shortHand);
		
		if (cpaClass == null)
			return null;
		
		return analysisProperties.get(cpaClass).getName();
	}
	
	public String getDescription(char shortHand) {
		Class<? extends ConfigurableProgramAnalysis> cpaClass = shortHandMap.get(shortHand);
		
		if (cpaClass == null)
			return null;
		
		return analysisProperties.get(cpaClass).getDescription();
	}
	
	public AnalysisProperties getProperties(ConfigurableProgramAnalysis cpa) {
		return analysisProperties.get(cpa.getClass());
	}
	
	public String getShorthandsString() {
		char[] shds = new char[shortHandMap.size()];
		int i = 0;
		for (Character c : shortHandMap.keySet()) {
			shds[i++] = c;
		}
		Arrays.sort(shds);
		return new String(shds);
	}
	
	private static List<Class<? extends ConfigurableProgramAnalysis>> findCPAClasses(File directory, String packageName) {
		
        List<Class<? extends ConfigurableProgramAnalysis>> classes = new ArrayList<Class<? extends ConfigurableProgramAnalysis>>();

        for (File file : directory.listFiles()) {
        	String fileName = file.getName();
            if (file.isDirectory()) {
                assert !fileName.contains(".");
            	classes.addAll(findCPAClasses(file, packageName + "." + fileName));
            } else if (fileName.endsWith(".class")) {
            	Class<?> clazz;
            	try {
            		try {
            			clazz = Class.forName(packageName + '.' + fileName.substring(0, fileName.length() - 6));
            		} catch (ExceptionInInitializerError e) {
            			clazz = Class.forName(packageName + '.' + fileName.substring(0, fileName.length() - 6),
            					false, Thread.currentThread().getContextClassLoader());
            		}
            		if (ConfigurableProgramAnalysis.class.isAssignableFrom(clazz)) {
            			int mod = clazz.getModifiers();
            			if (!Modifier.isAbstract(mod) && !Modifier.isInterface(mod))
            				classes.add(clazz.asSubclass(ConfigurableProgramAnalysis.class));
            		}
            	} catch (ClassNotFoundException e) {
            		logger.warn("Could not load class " + packageName + "." + fileName);
            	}
            }
        }
        return classes;
    }
	
}
