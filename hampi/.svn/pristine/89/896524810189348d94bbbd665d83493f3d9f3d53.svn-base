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

import java.io.*;
import java.util.Arrays;

public class Utils{

  public static final String nl      = System.getProperty("line.separator");

  public static final String newLine = System.getProperty("line.separator");

  public static void assertCond(boolean b){
    if (!b)
      throw new RuntimeException("Assertion violation.");
  }

  public static void assertCond(boolean b, String message){
    if (!b)
      throw new RuntimeException("Assertion violation: " + message);
  }

  public static boolean iff(boolean a, boolean b){
    return a == b;
  }

  public static boolean implies(boolean a, boolean b){
    return !a || b;
  }

  /**
   * If both parameters are null, returns true. If one parameter is null and the
   * other isn't, returns false. Otherwise, returns o1.equals(o2).
   * 
   * @param o1
   * @param o2
   */
  public static boolean equalsWithNull(Object o1, Object o2){
    if (o1 == null)
      return o2 == null;
    if (o2 == null)
      return false;
    return o1.equals(o2);
  }

  public static boolean isJavaIdentifier(String s){
    if (s == null || s.length() == 0 || !Character.isJavaIdentifierStart(s.charAt(0)))
      return false;
    for (int i = 1; i < s.length(); i++){
      if (!Character.isJavaIdentifierPart(s.charAt(i)))
        return false;
    }
    return true;
  }

  public static String convertToHexString(String unicodeString){
    char[] chars = unicodeString.toCharArray();
    StringBuilder output = new StringBuilder();
    for (char element : chars){
      output.append("\\u");
      String hex = Integer.toHexString(element);
      if (hex.length() < 4){
        output.append("0");
      }
      if (hex.length() < 3){
        output.append("0");
      }
      if (hex.length() < 2){
        output.append("0");
      }
      if (hex.length() < 1){
        output.append("0");
      }

      output.append(hex);
    }
    return output.toString();
  }

  public static int occurCount(StringBuilder text, String pattern){
    if (pattern.length() == 0)
      throw new IllegalArgumentException("empty pattern");
    int i = 0;
    int currIdx = text.indexOf(pattern);
    while (currIdx != -1){
      i++;
      currIdx = text.indexOf(pattern, currIdx + 1);
    }
    return i;
  }

  /**
   * Creates a string with n repetitions of character ch.
   */
  public static String repeat(int n, char ch){
    char[] chars = new char[n];
    Arrays.fill(chars, ch);
    return new String(chars);
  }

  /**
   * Creates a string with n spaces.
   */
  public static String spaces(int n){
    return repeat(n, ' ');
  }

  // ------Copied from UtilMDE to add a missing rpad(long, int)

  // Returns a string of the specified length, truncated if necessary,
  // and padded with spaces to the right if necessary.
  public static String rpad(String s, int length){
    if (s.length() < length){
      StringBuffer buf = new StringBuffer(s);
      for (int i = s.length(); i < length; i++){
        buf.append(" ");
      }
      return buf.toString();
    }else
      return s.substring(0, length);
  }

  // Converts the int to a String, then formats it using rpad
  public static String rpad(int num, int length){
    return rpad(String.valueOf(num), length);
  }

  // Converts the long to a String, then formats it using rpad
  public static String rpad(long num, int length){
    return rpad(String.valueOf(num), length);
  }

  // Converts the double to a String, then formats it using rpad
  public static String rpad(double num, int length){
    return rpad(String.valueOf(num), length);
  }

  public static String stripQuotes(String str){
    assert str.length() >= 2 && str.startsWith("\"") && str.endsWith("\"");
    return str.substring(1, str.length() - 1);
  }

  public static String quotes(String str){
    return "\"" + str + "\"";
  }

  /**
   * Serialize the given object to the file.
   */
  public static void serialize(Object o, String fName) throws IOException{
    ObjectOutputStream oos = new ObjectOutputStream(new BufferedOutputStream(new FileOutputStream(new File(fName))));
    try{
      oos.writeObject(o);
    }finally{
      oos.close();
    }
  }

  /**
   * Read a serialized object from the file.
   */
  public static Object deserialize(String fName) throws IOException,ClassNotFoundException{
    File file = new File(fName);
    if (!file.exists())
      throw new IllegalArgumentException("file does not exist:" + fName);
    ObjectInputStream ois = new ObjectInputStream(new BufferedInputStream(new FileInputStream(file)));
    try{
      return ois.readObject();
    }finally{
      ois.close();
    }
  }

}
