/*******************************************************************************
 * The MIT License
 *
 * Copyright (c) 2008 Adam Kiezun
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 ******************************************************************************/
package hampi.utils;

import java.util.*;

/**
 * ASCII utilities.
 */
public final class ASCIITable{

  /**
   * Lowest character in ASCII range.
   */
    public static final char lowestChar = 0; // PIETER: previously 32

  /**
   * Highest character in ASCII range.
   */
    public static final char highestChar = 255; // PIETER: previously 126

  static{
    if (lowestChar > highestChar)
      throw new IllegalStateException("invalid ascii range");
  }

  /** Return ascii code for a character. */
  public static int asciiCode(char c){
    return c;
  }

  /** Return ascii char for a code. */
  public static char asciiChar(int i){
    return (char) i;
  }

  /**
   * Return all ascii codes.
   */
  public static int[] codes(){
    int low = asciiCode(lowestChar);
    int high = asciiCode(highestChar);
    int[] codes = new int[high - low + 1];
    for (int i = 0; i < codes.length; i++){
      codes[i] = low + i;
    }
    return codes;
  }

  /**
   * Return all ascii chars.
   */
  public static char[] chars(){
    return range(lowestChar, highestChar);
  }

  /**
   * Returns all characters from the given range;
   */
  public static char[] range(char lowC, char highC){
    int low = asciiCode(lowC);
    int high = asciiCode(highC);
    char[] chars = new char[high - low + 1];
    for (int i = 0; i < chars.length; i++){
      chars[i] = asciiChar(low + i);
    }
    return chars;
  }

  /** Returns whether the character is ascii. */
  public static boolean isAscii(char c){
    int asciiCode = ASCIITable.asciiCode(c);
    return asciiCode >= asciiCode(lowestChar) && asciiCode <= asciiCode(highestChar);
  }

  /**
   * Returns the boolean array that stores values for bits encoding the given
   * value.
   */
  public static boolean[] asciiBits(int code, int bitCount){
    String binaryString = Integer.toBinaryString(code);
    boolean[] result = new boolean[bitCount];//all initialized to false
    // System.out.println(binaryString);
    int lenDiff = result.length - binaryString.length();
    for (int i = 0; i < binaryString.length(); i++){
      result[lenDiff + i] = binaryString.charAt(i) == '1';
    }
    // System.out.println(Arrays.toString(result));
    return result;
  }

  /**
   * Returns the set of characters in the ASCII range.
   */
  public static Set<Character> charSet(){
    char[] chars = ASCIITable.chars();
    Set<Character> result = new LinkedHashSet<Character>();
    for (char c : chars){
      result.add(c);
    }
    return result;
  }

  public static boolean isReadable(char c){
    return c > 31 && c < 255;
  }
}
