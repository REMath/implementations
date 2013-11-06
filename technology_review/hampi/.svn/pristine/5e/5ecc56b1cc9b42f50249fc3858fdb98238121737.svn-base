package hampi;

/**
 * This exception is thrown by Hampi to communicate that a solution was found.
 */
public final class HampiResultException extends RuntimeException{

  private static final long serialVersionUID = -1646032817161163868L;

  public static final int CODE_UNSAT = 1;
  public static final int CODE_PARSE_ERROR = 2;
  public static final int CODE_USAGE_ERROR = 3;
  public static final int CODE_TIMEOUT = 4;
  public static final int CODE_INTERNAL_ERROR = 5;

  private final int code;

  private HampiResultException(String string, int code){
    super(string);
    this.code = code;
  }

  public int getExitCode(){
    return code;
  }

  public boolean isUnsat(){
    return code == CODE_UNSAT;
  }

  public static HampiResultException unsat(){
    return new HampiResultException("UNSAT", CODE_UNSAT);
  }

  public static HampiResultException parse(String string){
    return new HampiResultException("ERROR " + string, CODE_PARSE_ERROR);
  }

  public static HampiResultException usage(String string){
    return new HampiResultException("ERROR " + string, CODE_USAGE_ERROR);
  }
}
