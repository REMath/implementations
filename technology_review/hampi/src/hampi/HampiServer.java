package hampi;

import java.io.*;
import java.net.*;
import java.util.*;

/**
 * This runs Hampi as a server. Clients connect to it and pass file names. <br>
 * The server terminates when the input line is "SHUTDOWN".<br>
 * <br>
 * XXX: this is not secure because we read files from the disk (whatever the
 * client says).
 */
public final class HampiServer{
  public static final String HAMPISERVER_RUNNING = ".hampiserverRunning";

  public static void main(String[] args) throws Exception{
    if (args.length != 1){
      System.out.println("usage: HampiServer port");
      System.out.println("send \"SHUTDOWN\" to shut down (e.g., echo SHUTDOWN | nc localhost port)");
      return;
    }
    // create socket
    int port = Integer.parseInt(args[0]);
    ServerSocket serverSocket = new ServerSocket(port, 1, InetAddress.getByName("localhost"));
    System.err.println(new Date() + " started Hampi server on port " + port);

    //create file to indicate that server is running. NOTE this is lame
    File serverRunning = new File(HAMPISERVER_RUNNING);
    boolean lockCreated = serverRunning.createNewFile();
    if (lockCreated == false)
      throw new IllegalStateException("Remove the " + HAMPISERVER_RUNNING + " file");
    serverRunning.deleteOnExit();

    // repeatedly wait for connections, and process
    while (true){

      // a "blocking" call which waits until a connection is requested
      Socket clientSocket = serverSocket.accept();
      System.out.println(new Date() + " accepted connection");

      // open up IO streams
      In in = new In(clientSocket);
      Out out = new Out(clientSocket);

      // waits for data and reads it in until connection dies
      // readLine() blocks until the server receives a new line from client
      String fname = in.readLine();

      if (fname.equals("SHUTDOWN")){
        Date now = new Date();
        System.out.println(now + " Hampi server shutting down on port " + port);
        out.println(now + " Hampi server shutting down on port " + port);
        out.close();
        in.close();
        clientSocket.close();
        return;
      }
      System.out.println("solving: " + fname);

      PrintStream oldOut = System.out;
      try{
        OutputStream os = new ByteArrayOutputStream();
        System.setOut(new PrintStream(os));
        File file = new File(fname);
        if (file.exists()){
          Hampi.run(false, false, new FileInputStream(file));
          out.println(os.toString());
        }else{
          out.println("ERROR file " + fname + " does not exist");
          oldOut.println("ERROR file " + fname + " does not exist");
        }
      }catch (HampiResultException e){
        oldOut.println(e.getMessage());
        out.println(e.getMessage());
      }catch (ThreadDeath t){
        oldOut.println("ERROR server dies " + t);
        throw t;
      }catch (Throwable t){
        out.println("ERROR " + t.getMessage());
        oldOut.println("ERROR " + t.getMessage());
      }finally{
        System.setOut(oldOut);
        // close IO streams, then socket
        System.out.println(new Date() + " closing connection");
        out.close();
        in.close();
        clientSocket.close();
      }

    }
  }
}

/**
 * <i>Input</i>. This class provides methods for reading strings and numbers
 * from standard input, file input, URL, and socket.
 * <p>
 * The Locale used is: language = English, country = US. This is consistent with
 * the formatting conventions with Java floating-point literals, command-line
 * arguments (via <tt>Double.parseDouble()</tt>) and standard output (via
 * <tt>System.out.print()</tt>). It ensures that standard input works the number
 * formatting used in the textbook.
 * <p>
 * For additional documentation, see <a
 * href="http://www.cs.princeton.edu/introcs/31datatype">Section 3.1</a> of
 * <i>Introduction to Programming in Java: An Interdisciplinary Approach</i> by
 * Robert Sedgewick and Kevin Wayne.
 */
final class In{
  private Scanner scanner;

  // assume Unicode UTF-8 encoding
  //private String charsetName = "UTF-8";

  private final String charsetName = "ISO-8859-1";

  // assume language = English, country = US for consistency with System.out.
  private final Locale usLocale = new Locale("en", "US");

  /**
   * Create an input stream for standard input.
   */
  public In(){
    scanner = new Scanner(System.in, charsetName);
    scanner.useLocale(usLocale);
  }

  /**
   * Create an input stream from a socket.
   */
  public In(Socket socket){
    try{
      InputStream is = socket.getInputStream();
      scanner = new Scanner(is, charsetName);
      scanner.useLocale(usLocale);
    }catch (IOException ioe){
      System.err.println("Could not open " + socket);
    }
  }

  /**
   * Create an input stream from a URL.
   */
  public In(URL url){
    try{
      URLConnection site = url.openConnection();
      InputStream is = site.getInputStream();
      scanner = new Scanner(is, charsetName);
      scanner.useLocale(usLocale);
    }catch (IOException ioe){
      System.err.println("Could not open " + url);
    }
  }

  /**
   * Create an input stream from a file or web page.
   */
  public In(String s){

    try{
      // first try to read file from local file system
      File file = new File(s);
      if (file.exists()){
        scanner = new Scanner(file, charsetName);
        scanner.useLocale(usLocale);
        return;
      }

      // next try for files included in jar
      URL url = getClass().getResource(s);

      // or URL from web
      if (url == null){
        url = new URL(s);
      }

      URLConnection site = url.openConnection();
      InputStream is = site.getInputStream();
      scanner = new Scanner(is, charsetName);
      scanner.useLocale(usLocale);
    }catch (IOException ioe){
      System.err.println("Could not open " + s);
    }
  }

  /**
   * Does the input stream exist?
   */
  public boolean exists(){
    return scanner != null;
  }

  /**
   * Is the input stream empty?
   */
  public boolean isEmpty(){
    return !scanner.hasNext();
  }

  /**
   * Read and return the next line or null if there is no next line.
   */
  public String readLine(){
    if (!scanner.hasNextLine())
      return null;
    return scanner.nextLine();
  }

  /**
   * Read and return the next character.
   */
  public char readChar(){
    // (?s) for DOTALL mode so . matches any character, including a line termination character
    // 1 says look only one character ahead
    // consider precompiling the pattern
    String s = scanner.findWithinHorizon("(?s).", 1);
    return s.charAt(0);
  }

  // return rest of input as string
  /**
   * Read and return the remainder of the input as a string.
   */
  public String readAll(){
    if (!scanner.hasNextLine())
      return null;

    // reference: http://weblogs.java.net/blog/pat/archive/2004/10/stupid_scanner_1.html
    return scanner.useDelimiter("\\A").next();
  }

  /**
   * Return the next string from the input stream.
   */
  public String readString(){
    return scanner.next();
  }

  /**
   * Return the next int from the input stream.
   */
  public int readInt(){
    return scanner.nextInt();
  }

  /**
   * Return the next double from the input stream.
   */
  public double readDouble(){
    return scanner.nextDouble();
  }

  /**
   * Return the next float from the input stream.
   */
  public double readFloat(){
    return scanner.nextFloat();
  }

  /**
   * Return the next long from the input stream.
   */
  public long readLong(){
    return scanner.nextLong();
  }

  /**
   * Return the next byte from the input stream.
   */
  public byte readByte(){
    return scanner.nextByte();
  }

  /**
   * Return the next boolean from the input stream, allowing "true" or "1" for
   * true and "false" or "0" for false.
   */
  public boolean readBoolean(){
    String s = readString();
    if (s.equalsIgnoreCase("true"))
      return true;
    if (s.equalsIgnoreCase("false"))
      return false;
    if (s.equals("1"))
      return true;
    if (s.equals("0"))
      return false;
    throw new java.util.InputMismatchException();
  }

  /**
   * Close the input stream.
   */
  public void close(){
    scanner.close();
  }
}

class Out{
  private PrintWriter out;

  // for stdout
  public Out(OutputStream os){
    out = new PrintWriter(os, true);
  }

  public Out(){
    this(System.out);
  }

  // for Socket output
  public Out(Socket socket){
    try{
      out = new PrintWriter(socket.getOutputStream(), true);
    }catch (IOException ioe){
      ioe.printStackTrace();
    }
  }

  // for file output
  public Out(String s){
    try{
      out = new PrintWriter(new FileOutputStream(s), true);
    }catch (IOException ioe){
      ioe.printStackTrace();
    }
  }

  public void close(){
    out.close();
  }

  public void println(){
    out.println();
    out.flush();
  }

  public void println(Object x){
    out.println(x);
    out.flush();
  }

  public void println(boolean x){
    out.println(x);
    out.flush();
  }

  public void println(char x){
    out.println(x);
    out.flush();
  }

  public void println(double x){
    out.println(x);
  }

  public void println(float x){
    out.println(x);
  }

  public void println(int x){
    out.println(x);
  }

  public void println(long x){
    out.println(x);
  }

  public void print(){
    out.flush();
  }

  public void print(Object x){
    out.print(x);
    out.flush();
  }

  public void print(boolean x){
    out.print(x);
    out.flush();
  }

  public void print(char x){
    out.print(x);
    out.flush();
  }

  public void print(double x){
    out.print(x);
    out.flush();
  }

  public void print(float x){
    out.print(x);
    out.flush();
  }

  public void print(int x){
    out.print(x);
    out.flush();
  }

  public void print(long x){
    out.print(x);
    out.flush();
  }
}
