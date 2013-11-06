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
import java.util.*;

public final class Files{
  private Files(){
    throw new IllegalStateException("no instances");
  }

  /**
   * Creates a stream that forwards all data to all the provided streams.
   */
  public static OutputStream tee(final OutputStream... streams){
    return new OutputStream(){
      @Override
      public void write(int b) throws IOException{
        for (OutputStream os : streams){
          os.write(b);
        }
      }
    };
  }

  /**
   * Deletes all files and subdirectories under dir. Returns true if all
   * deletions were successful. If a deletion fails, the method stops attempting
   * to delete and returns false.
   */
  public static boolean deleteDir(File dir){
    if (dir.isDirectory()){
      String[] children = dir.list();
      for (String element : children){
        boolean success = deleteDir(new File(dir, element));
        if (!success)
          return false;
      }
    }

    // The directory is now empty so delete it
    return dir.delete();
  }

  /**
   * Returns all file names from the given directory. The names of the files
   * must start and end with the specified strings.
   */
  public static List<File> findFilesInDir(File dir, String startsWith, String endsWith){
    if (!dir.isDirectory())
      throw new IllegalArgumentException("not a directory: " + dir.getAbsolutePath());
    File currentDir = dir;
    List<File> retval = new ArrayList<File>();
    for (File file : currentDir.listFiles()){
      String fileName = file.getName();
      if (fileName.startsWith(startsWith) && fileName.endsWith(endsWith)){
        retval.add(file);
      }
    }
    return retval;
  }

  public static File writeToFile(String s, File file) throws IOException{
    writeToFile(s, file, false);
    return file;
  }

  public static File writeToFile(String s, String fileName) throws IOException{
    return writeToFile(s, fileName, false);
  }

  public static File writeToFile(String s, File file, boolean append) throws IOException{
    BufferedWriter writer = new BufferedWriter(new FileWriter(file, append));
    try{
      writer.append(s);
      return file;
    }finally{
      writer.close();
    }
  }

  public static File writeToFile(String s, String fileName, boolean append) throws IOException{
    File f = new File(fileName);
    writeToFile(s, f, append);
    return f;
  }

  /**
   * Reads the whole file. Does not close the reader. Returns the list of lines.
   */
  public static List<String> readWhole(BufferedReader reader) throws IOException{
    List<String> result = new ArrayList<String>();
    String line = reader.readLine();
    while (line != null){
      result.add(line);
      line = reader.readLine();
    }
    return Collections.unmodifiableList(result);
  }

  /**
   * Reads the whole file. Returns the list of lines.
   */
  public static List<String> readWhole(String fileName) throws IOException{
    return readWhole(new File(fileName));
  }

  /**
   * Reads the whole file. Returns the list of lines.
   */
  public static List<String> readWhole(File file) throws IOException{
    BufferedReader in = new BufferedReader(new FileReader(file));
    try{
      return readWhole(in);
    }finally{
      in.close();
    }
  }

  /**
   * Reads the whole file. Returns the list of lines. Does not close the stream.
   */
  public static List<String> readWhole(InputStream is) throws IOException{
    BufferedReader in = new BufferedReader(new InputStreamReader(is));
    return readWhole(in);
  }

  /**
   * Reads the whole contents read from the stream. Returns one big String.
   * Closes the stream.
   */
  public static String getFileContents(InputStream is) throws IOException{
    return getFileContents(new BufferedReader(new InputStreamReader(is)));
  }

  /**
   * Reads the whole file. Returns one big String.
   */
  public static String getFileContents(File file) throws IOException{
    if (!file.exists())
      return null;
    return getFileContents(new BufferedReader(new FileReader(file)));
  }

  private static String getFileContents(Reader in) throws IOException{
    StringBuilder result = new StringBuilder();
    try{
      int c;
      while ((c = in.read()) != -1){
        result.append((char) c);
      }
      in.close();
      return result.toString();
    }finally{
      in.close();
    }
  }

  /**
   * Reads the whole file. Returns one big String.
   */
  public static String getFileContents(String path) throws IOException{
    return getFileContents(new File(path));
  }

  public static LineNumberReader getFileReader(String fileName){
    return getFileReader(new File(fileName));
  }

  public static LineNumberReader getFileReader(File fileName){
    LineNumberReader reader;
    try{
      reader = new LineNumberReader(new BufferedReader(new FileReader(fileName)));
    }catch (FileNotFoundException e1){
      throw new IllegalStateException("File was not found " + fileName + " " + e1.getMessage());
    }
    return reader;
  }

  public static String addProjectPath(String string){
    return System.getProperty("user.dir") + File.separator + string;
  }

  public static boolean deleteFile(String path){
    File f = new File(path);
    return f.delete();
  }

  /**
   * Reads a single long from the file. Returns null if the file does not exist.
   * 
   * @throws IllegalStateException
   *           is the file contains not just 1 line or if the file contains
   *           something.
   */
  public static Long readLongFromFile(File file){
    if (!file.exists())
      return null;
    List<String> lines;
    try{
      lines = readWhole(file);
    }catch (IOException e){
      throw new IllegalStateException("Problem reading file " + file + " ", e);
    }
    if (lines.size() != 1)
      throw new IllegalStateException("Expected exactly 1 line in " + file + " but found " + lines.size());
    try{
      return Long.valueOf(lines.get(0));
    }catch (NumberFormatException e){
      throw new IllegalStateException("Expected a number (type long) in " + file + " but found " + lines.get(0));
    }
  }

  // Process only files under dir
  public static List<File> recursiveFindFilesInDir(File dir, String startsWith, String endsWith){
    List<File> retval = new ArrayList<File>();
    if (dir.isDirectory()){
      String[] children = dir.list();
      for (String element : children){
        retval.addAll(recursiveFindFilesInDir(new File(dir, element), startsWith, endsWith));
      }
    }else{
      if (dir.getPath().startsWith(startsWith) && dir.getPath().endsWith(endsWith)){
        retval.add(dir);
      }
    }

    return retval;
  }

  public static List<File> recursiveFindFilesWithPattern(File dir, String includeFileNamePattern){
    List<File> retval = new ArrayList<File>();
    if (dir.isDirectory()){
      String[] children = dir.list();
      for (String element : children){
        retval.addAll(recursiveFindFilesWithPattern(new File(dir, element), includeFileNamePattern));
      }
    }else{
      if (dir.getName().matches(includeFileNamePattern)){
        retval.add(dir);
      }
    }

    return retval;
  }

  /**
   * Given a path and a base, returns the relative path.
   */
  public static String relative(File path, File base){
    return base.toURI().relativize(path.toURI()).getPath();
  }
}
