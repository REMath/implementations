/*
 * AnalysisProperties.java - This file is part of the Jakstab project.
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

public class AnalysisProperties {

	private String name;
	private String description;
	private char shortHand = ' ';
	private boolean isExplicit = false;

	public String getName() {
		return name;
	}
	
	public void setName(String name) {
		this.name = name;
	}
	
	public String getDescription() {
		return description;
	}
	
	public void setDescription(String description) {
		this.description = description;
	}
	
	public char getShortHand() {
		return shortHand;
	}
	
	public void setShortHand(char shortHand) {
		this.shortHand = shortHand;
	}
	
	public boolean isExplicit() {
		return isExplicit;
	}
	
	public void setExplicit(boolean isExplicit) {
		this.isExplicit = isExplicit;
	}
	
}
