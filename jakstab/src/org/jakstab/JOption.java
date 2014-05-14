/*
 * JOption.java - This file is part of the Jakstab project.
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

public class JOption<T> {

	private final String name;
	private final String paramName;
	private final T defaultValue;
	private final String description;
	private T value;
	
	public static <T> JOption<T> create(String name, String paramName, T defaultValue, String description) {
		assert defaultValue != null;
		return new JOption<T>(name, paramName, defaultValue, description);
	}
	
	public static JOption<Boolean> create(String name, String description) {
		return new JOption<Boolean>(name, "", Boolean.FALSE, description);
	}

	private JOption(String name, String paramName, T defaultValue, String description) {
		super();
		assert (!name.startsWith("-")) : "Option names should be defined without dashes";
		if (name.length() == 1) {
			this.name = "-" + name;
		} else {
			this.name = "--" + name;
		}
		if (paramName != null && paramName != "")
			this.paramName = paramName;
		else 
			this.paramName = null;
		this.defaultValue = defaultValue;
		this.description = description;
		this.value = defaultValue;
		Options.addOption(this);
	}
	
	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}

	/**
	 * @return the paramName
	 */
	public String getParamName() {
		return paramName;
	}

	/**
	 * @return the paramType
	 */
	public T getDefaultValue() {
		return defaultValue;
	}

	/**
	 * @return the description
	 */
	public String getDescription() {
		return description;
	}

	/**
	 * @return the value
	 */
	public T getValue() {
		return value;
	}
	
	/**
	 * @param value the value to set
	 */
	@SuppressWarnings("unchecked")
	public void setValue(Object value) {
		this.value = (T)value;
	}

	@Override
	public String toString() {
		return "Option [name=" + name + ", paramName=" + paramName
				+ ", defaultValue=" + defaultValue + ", description="
				+ description + ", value=" + value + "]";
	}
	
}
