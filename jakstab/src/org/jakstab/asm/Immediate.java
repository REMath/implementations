/*
 * Copyright 2002 Sun Microsystems, Inc.  All Rights Reserved.
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

package org.jakstab.asm;

/**
 * An Immediate is a numeric operand to an instruction.
 */
public class Immediate extends ImmediateOrRegister {
   private final Number value;
   private final DataType dataType;

   public Immediate(Number value, DataType dataType) {
      this.value = value;
      this.dataType = dataType;
   }

   public Number getNumber() {
      return value;
   }
   
   public DataType getDataType() {
	   return dataType;
   }

   public String toString() {
      return "$0x" + Integer.toHexString(value.intValue());// + "<" + dataType + ">";
   }

   public int hashCode() {
      return value.hashCode();
   }

   public boolean equals(Object obj) {
      if (obj == null || getClass() != obj.getClass())
         return false;
      return value.equals(((Immediate)obj).value);    
   }
}
