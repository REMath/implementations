/*
 * ByteBuffer.java - This file is part of the Jakstab project.
 * 
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 * Copyright (C) 2003 The University of Arizona
 *
 * The original code for this class was taken from "MBEL: The Microsoft 
 * Bytecode Engineering Library" and modified for use with Jakstab.
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

package org.jakstab.loader.pe;

/** This class is used for temporary storage and manipulation of a stream
  * of bytes. All of the signature classes parse themselves out of ByteBuffers,
  * and the emitter makes large use of them for storing intermediate chunks of 
  * the final module file. This class is vaguely modelled after java.nio.ByteBuffer,
  * but it has some extra functionality that makes it specifically useful to MBEL.
  * The concept behind a ByteBuffer is that it is an infinitely large 0-based array 
  * of bytes. There is a current byte index pointer given by getPosition(). The user can 
  * also set the current position using setPosition(int). Setting the position to a 
  * very high value will not grow the underlying array, but writing to it will (i.e. 
  * space is not allocated until needed). Both reading and writing advance the current
  * position pointer by the specified amount. Since one main use of the ByteBuffer
  * is as a convenient way to write an array of bytes, the ByteBuffer maintains the 
  * index of the greatest position that has been written to. Everything up to this point is 
  * returned when you call toByteArray(). 
  * @author Michael Stepp
  */
public class ByteBuffer{
   private static final int SIZE = 1000;
   private byte[][] buffer;
   private int position;
   private int last;

   /** Makes a ByteBuffer that is initially intended to be read from, not written to.
     * This constructor sets the current position to 0.
     * @param init the initial bytes to put into the array, starting from index 0 (if null, and empty ByteBuffer is created)
     */
   public ByteBuffer(byte[] init){
      if (init==null || init.length==0){
         buffer = new byte[1][SIZE];
         last = -1;
      }else{
         buffer = new byte[init.length/SIZE+1][SIZE];
         for (int i=0;i<init.length;i++)
            buffer[i/SIZE][i%SIZE] = init[i];
         last = init.length-1;
      }
      position = 0;
   }

   /** Makes a ByteBuffer that is initially intended for writing.
     * The current position pointer is set to 0.
     * @param capacity the minimum capacity of this ByteBuffer (for convenience)
     */
   public ByteBuffer(int capacity){
      buffer = new byte[capacity/SIZE+1][SIZE];
      position = 0;
      last = -1;
   }

   /** Returns the current maximum capacity of the underlying array.
     * This value is not an absolute maximum, because ByteBuffers grow as needed.
     */
   public int getCapacity(){
      return (buffer.length*SIZE);
   }

   /** Returns the index of the current position in the ByteBuffer.
     * This value will be >=0.
     */
   public int getPosition(){
      return position;
   }
   
   /** Returns the index of the last position written to (initially -1).
     */
   public int getLast(){
      return last;
   }

   /** Returns the byte stored in this ByteBuffer at the current position.
     * Advances the current position by 1.
     * (note: if the current position is past the end of any user-written data, this will return 0)
     */
   public byte get(){
      if (position>=getCapacity()){
         position++;
         return 0;
      }
      byte value = buffer[position/SIZE][position%SIZE];
      position++;
      return value;
   }

   /** Returns a 2-byte unsigned little-endian integer, starting at the current position.
     * Advances the current position by 2 (see get())
     */
   public int getWORD(){
      int value = (get()&0xFF);
      value |= (get()&0xFF)<<8;
      value &= 0xFFFF;
      return value;
   }
   
   /** Returns a 4-byte unsigned little-endian integer, starting at the current position.
     * Advances the current position by 4 (see get())
     */
   public long getDWORD(){
      long value = (get()&0xFFL);
      value |= (get()&0xFFL)<<8;
      value |= (get()&0xFFL)<<16;
      value |= (get()&0xFFL)<<24;
      value &= 0xFFFFFFFFL;
      return value;
   }

   /** Returns the byte stored in this ByteBuffer at the current position.
     * This method does not advance the current position.
     * (note: if the current position is past the end of any user-written data, this will return 0)
     */
   public byte peek(){
      if (position>=getCapacity())
         return 0;
      return buffer[position/SIZE][position%SIZE];
   }

   /** Sets the current position of this ByteBuffer.
     * @param pos the new position (if <0, ignored)
     */
   public void setPosition(int pos){
      if (pos>=0)
         position = pos;
   }

   /** Decrements the current position by 1 (if >0).
     */
   public void back(){
      // moves the position back by one
      if (position>0)
         position--;
   }
   
   /** Returns the contents of this ByteBuffer as a single contiguous byte array.
     * This returns everything from byte 0 to byte getLast(), inclusive.
     */
   public byte[] toByteArray(){
      // gets everything up to 'last'
      byte[] newarr = new byte[last+1];
      for (int i=0;i<newarr.length;i++)
         newarr[i] = buffer[i/SIZE][i%SIZE];
      return newarr;
   }
   
   /** Pads this ByteBuffer with 0s up to the next multiple of 'align'.
     * @param align the value to align to (if <=0, ignored)
     */
   public void pad(int align){
      if (align<=0) 
         return;
      while((position%align)!=0)
         put(0);
   }
   
   /** Writes the lowest 8 bits of the given int to this ByteBuffer, at the current position.
     * Advances the current position by 1.
     */
   public void put(int b){
      put((byte)(b&0xFF));
   }

   /** Writes a single byte to this ByteBuffer, at the current position.
     * Advances the current position by 1.
     */
   public void put(byte data){
      if (position>=getCapacity()){
         byte[][] newbuf = new byte[position/SIZE+2][];
         for (int i=0;i<buffer.length;i++)
            newbuf[i] = buffer[i];
         for (int i=buffer.length;i<newbuf.length;i++)
            newbuf[i] = new byte[SIZE];
         buffer = newbuf;
      }

      buffer[position/SIZE][position%SIZE] = data;
      last = Math.max(last,(position++));
   }

   /** Writes the given byte array to this ByteBuffer, starting at the current position.
     * Advances the current position by data.length.
     * @param data the bytes to write in this buffer (if null, writes nothing)
     */
   public void put(byte[] data){
      if (data==null)
         return;
      if (data.length+position >= getCapacity()){
         byte[][] newbuf = new byte[(data.length+position)/SIZE+2][];
         for (int i=0;i<buffer.length;i++)
            newbuf[i] = buffer[i];
         for (int i=buffer.length;i<newbuf.length;i++)
            newbuf[i] = new byte[SIZE];
         buffer = newbuf;
      }

      for (int i=0;i<data.length;i++){
         buffer[position/SIZE][position%SIZE] = data[i];
         last = Math.max(last,(position++));
      }
   }
   
   /** Writes a signed little-endian int16 to this ByteBuffer, starting at the current position.
     * Advances the current position by 2.
     */
   public void putINT16(int int16){
      put((byte)(int16&0xFF));
      put((byte)((int16>>8)&0xFF));
   }
   
   /** Writes an unsigned little-endian int16 to this ByteBuffer, starting at the current position.
     * Advances the current position by 2.
     */
   public void putWORD(int uint16){
      put((byte)(uint16&0xFF));
      put((byte)((uint16>>8)&0xFF));
   }
   
   /** Writes a signed little-endian int32 to this ByteBuffer, starting at the current position.
     * Advances the current position by 4.
     */
   public void putINT32(int int32){
      put((byte)(int32&0xFF));
      put((byte)((int32>>8)&0xFF));
      put((byte)((int32>>16)&0xFF));
      put((byte)((int32>>24)&0xFF));
   }

   /** Writes an unsigned little-endian int32 to this ByteBuffer, starting at the current position.
     * Advances the current position by 4.
     */
   public void putDWORD(long uint32){
      put((byte)(uint32&0xFF));
      put((byte)((uint32>>8)&0xFF));
      put((byte)((uint32>>16)&0xFF));
      put((byte)((uint32>>24)&0xFF));
   }
   
   /** Writes metadata token encoded in a long to this ByteBuffer, starting at the current position.
     * Advances the current position by 4.
     */
   public void putTOKEN(long token){
      putDWORD(token);
   }
   
   /** Writes a signed little-endian int64 to this ByteBuffer, starting at the current position.
     * Advances the current position by 8.
     */
   public void putINT64(long int64){
      put((byte)(int64&0xFF));
      put((byte)((int64>>8)&0xFF));
      put((byte)((int64>>16)&0xFF));
      put((byte)((int64>>24)&0xFF));
      put((byte)((int64>>32)&0xFF));
      put((byte)((int64>>40)&0xFF));
      put((byte)((int64>>48)&0xFF));
      put((byte)((int64>>56)&0xFF));
   }

   /** Writes a float32 to this ByteBuffer, starting at the current position.
     * Advances the current position by 4.
     */
   public void putR4(float r4){
      int bits = Float.floatToIntBits(r4);
      putINT32(bits);
   }
   
   /** Writes a float64 to this ByteBuffer, starting at the current position.
     * Advances the current position by 8.
     */
   public void putR8(double r8){
      long bits = Double.doubleToLongBits(r8);
      putINT64(bits);
   }
   
   /** Concatenates the given ByteBuffer to the end of this ByteBuffer, 
     * starting from 0 and ending at buf.getLast(), inclusive.
     * @param buf the ByteBuffer to concatenate to the end of this one (if null, ignored)
     */
   public void concat(ByteBuffer buf){
      if (buf==null)
         return;
      for (int i=0;i<=buf.last;i++){
         put(buf.buffer[i/SIZE][i%SIZE]);
      }
   }
}
