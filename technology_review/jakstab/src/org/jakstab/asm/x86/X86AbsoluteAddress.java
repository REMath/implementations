/*
 * Copyright 2002-2003 Sun Microsystems, Inc.  All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
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
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Sun Microsystems, Inc., 4150 Network Circle, Santa Clara,
 * CA 95054 USA or visit www.sun.com if you need additional information or
 * have any questions.
 *  
 */

/* 
 * Original code for this class taken from the Java HotSpot VM. 
 * Modified for use with the Jakstab project. All modifications 
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 */

package org.jakstab.asm.x86;

import org.jakstab.asm.AbsoluteAddress;

public class X86AbsoluteAddress extends AbsoluteAddress {

	private long segment;

	/**
	 * Creates a new direct address from numeric segment and offset values.
	 * This is only used by CALL FAR and JMP FAR (lcall and ljmp in AT&T).
	 * @param segment the numeric segment value of the address
	 * @param disp the address's offset from the segment start
	 */
	public X86AbsoluteAddress(long segment, long disp) {
		super(disp);
		this.segment = segment;
	}
	
	public X86AbsoluteAddress(long disp) {
		super(disp);
		this.segment = 0;
	}

	public String toString() {
		StringBuffer buf = new StringBuffer();
		if (getSegment() != 0) {
			buf.append("0x");
			buf.append(Long.toHexString(getSegment()));
			buf.append(":");
		}
		//buf.append("[");  --JK AT&T syntax...
		buf.append(super.toString());
		//buf.append("]");

		return buf.toString();
	}

	/* (non-Javadoc)
	 * @see org.jakstab.asm.AbsoluteAddress#getEffectiveValue(long)
	 */
	@Override
	public long getEffectiveValue(long pcValue) {
		return value + 16 * segment;
	}
	
	long getSegment() {
		return segment;
	}
}
