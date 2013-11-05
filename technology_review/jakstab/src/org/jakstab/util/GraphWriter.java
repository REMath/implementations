/*
 * GraphWriter.java - This file is part of the Jakstab project.
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

import java.awt.Color;
import java.io.IOException;
import java.util.Map;

public interface GraphWriter {

	public void close() throws IOException;

	public void writeNode(String id, String body) throws IOException;

	public void writeNode(String id, String body, Map<String, String> properties) throws IOException;

	public void writeEdge(String id1, String id2) throws IOException;

	public void writeEdge(String id1, String id2, Color color) throws IOException;

	public void writeEdge(String id1, String id2, Map<String, String> properties) throws IOException;

	public void writeLabeledEdge(String id1, String id2, String label) throws IOException;
	
	public void writeLabeledEdge(String id1, String id2, String label, Color color) throws IOException;

	public String getFilename();

}