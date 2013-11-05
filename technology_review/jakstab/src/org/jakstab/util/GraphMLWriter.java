/*
 * GraphMLWriter.java - This file is part of the Jakstab project.
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 * Copyright 2009 Daniel Reynaud <reynaud.daniel@gmail.com>
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
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;
import java.util.Map;

import org.jakstab.util.Logger;

/**
 * @author Daniel Reynaud, Johannes Kinder
 */
public class GraphMLWriter implements GraphWriter {

	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(GraphMLWriter.class);

	private final OutputStreamWriter out;
	private String filename;

	public GraphMLWriter(String filename) throws IOException {
		this.filename = filename + ".graphml";
		out = new OutputStreamWriter(new FileOutputStream(this.filename));
		out.write("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n");
		out.write("<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns/graphml\" " +
				"xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" " +
				"xmlns:y=\"http://www.yworks.com/xml/graphml\" " +
				"xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns/graphml " +
		"http://www.yworks.com/xml/schema/graphml/1.0/ygraphml.xsd\">\n");
		out.write("<key for=\"node\" id=\"d0\" yfiles.type=\"nodegraphics\"/>\n");
		out.write("<key for=\"edge\" id=\"d2\" yfiles.type=\"edgegraphics\"/>\n");
		out.write("<graph edgedefault=\"directed\">\n");
	}

	@Override
	public void close() throws IOException {
		out.write("</graph>\n");
		out.write("</graphml>\n");
		out.close();
	}

	@Override
	public final void writeNode(String id, String body) throws IOException {
		writeNode(id, body, null);
	}

	@Override
	public final void writeNode(String id, String body, Map<String,String> properties) throws IOException {
		out.write("<node id=\""+toIdentifier(id)+"\">\n");
		out.write("  <data key=\"d0\"><y:ShapeNode><y:NodeLabel>\n");
		out.write(sanitizeXML(body));
		/* properties ignored
		if (properties != null && properties.size() > 0) {
			for (Map.Entry<String, String> property : properties.entrySet()) {
				out.write(property.getKey());
				out.write("=");
				out.write(property.getValue());
				out.write("\n");
			}
		} */
		out.write("  </y:NodeLabel></y:ShapeNode></data>\n");
		out.write("</node>\n");
	}

	@Override
	public final void writeEdge(String id1, String id2) throws IOException {
		writeEdge(id1, id2, (Map<String, String>)null);
	}

	@Override
	public final void writeEdge(String id1, String id2, Map<String,String> properties) throws IOException {
		out.write("<edge source=\""+toIdentifier(id1)+"\" target=\""+toIdentifier(id2)+"\">\n");
		out.write("  <data key=\"d2\"><y:PolyLineEdge><y:Arrows source=\"none\" " +
		"target=\"standard\"/>\n");

		if (properties != null && properties.size() > 0) {
			for (Map.Entry<String, String> property : properties.entrySet()) {
				String key = property.getKey();
				out.write('<'+key+'>');
				out.write(sanitizeXML(property.getValue()));
				out.write("</"+property.getKey()+">\n");
			}
		}

		out.write("  </y:PolyLineEdge></data>\n");
		out.write("</edge>\n");
	}

	@Override
	public void writeEdge(String id1, String id2, Color color)
			throws IOException {
		Map<String,String> map = new HashMap<String, String>();
		if (color != null) {
			map.put("y:LineStyle", colorConvert(color));
		}
		writeEdge(id1, id2, map);
	}

	@Override
	public final void writeLabeledEdge(String id1, String id2, String label) throws IOException {
		writeLabeledEdge(id1, id2, label, null);
	}

	@Override
	public final void writeLabeledEdge(String id1, String id2, String label, Color color) throws IOException {
		Map<String,String> map = new HashMap<String, String>();
		map.put("y:EdgeLabel", label);
		if (color != null) {
			map.put("y:LineStyle", colorConvert(color));
		}
		writeEdge(id1, id2, map);
	}

	private static final String toIdentifier(String id) {
		id = id.replace('@', '_');
		id = id.replace('.', '_');
		id = id.replace(':', '_');
		if (!Character.isLetter(id.charAt(0)))
			return "a" + id;
		else return id;
	}

	private static final String sanitizeXML(String str) {
		String out = str.replace("&", "&amp;");
		out = out.replace(">", "&gt;");
		out = out.replace("<", "&lt;");
		return out;
	}

	@Override
	public String getFilename() {
		return filename;
	}
	
	private static String colorConvert(Color color) {
		return String.format("color=\"#%02x%02x%02x\"", color.getRed(), color.getGreen(), color.getBlue());
	}

}