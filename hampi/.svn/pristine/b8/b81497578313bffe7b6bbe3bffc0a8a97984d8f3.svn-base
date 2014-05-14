package hampi;

import java.io.*;
import java.util.Properties;

/**
 * This class collects Hampi-wide options, such as locations of certain file
 * etc.
 */
public final class HampiOptions{
  public static final HampiOptions INSTANCE = new HampiOptions();
  private final Properties props;

  private HampiOptions(){
    this.props = new Properties();
    try{
      this.props.load(new FileInputStream("hampi.properties"));
    }catch (IOException e){
      throw new HampiException(e);
    }
  }

  /**
   * Returns the value for the given option.
   */
  public String get(String optionName){
    return props.getProperty(optionName);
  }
}
