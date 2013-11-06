package hampi.stp;

import hampi.utils.*;
import stp.*;

/**
 * Encoding is a bidirectional mapping between integers and characters. Size of
 * the encoding is the number of bits needed to represent each character. For
 * example, if the alphabet has only 2 characters, then a 1-bit encoding is
 * enough.
 */
public final class CharacterEncoding{
  private static final int                      ENC                 = 8;

  /**
   * Specifies whether we optimize the size of the encoding.
   */
  public static final boolean                   OPTIM_ENCODING_SIZE = false;

  private final OneToOneMap<Integer, Character> mapping             = new OneToOneMap<Integer, Character>();

  /**
   * Creates an STP constant of the right bit-length. The argument is the
   * already encoded value.
   */
  public Expr stpConst(VC vc, int num){
    assert num >= 0 && (num <= (1 << ENC) - 1) : "invalid number to encode " + num + " encoding size:" + ENC;
    return vc.bvConstExprFromInt(ENC, num);
  }

  /**
   * Returns the STPExpression that corresponds to the n-th character of the
   * bitvector.
   */
  public STPExpr extractedChar(int n, BVExpr bv){
    return bv.extract(ENC * (n + 1) - 1, ENC * n, ENC);
  }

  /**
   * Returns the decoded string value for the counterexample produced by STP.
   */
  public String decodeValue(VC vc, Expr bv){
    String str = vc.getCounterExample(bv).toString();
    if (str.startsWith("0hex")){
      str = str.substring("0hex".length()).trim();
      if (ENC >= 4)
        return decodeString(str, false);
      else
        return decodeString(toBinary(str), true);
    }else if (str.startsWith("0bin")){
      str = str.substring("0bin".length()).trim();
      return decodeString(str, true);
    }else
      throw new IllegalStateException("unexpected " + str);

  }

  /**
   * Decodes a binary or hex string.
   */
  private String decodeString(String str, boolean isBinary){
    int letterEncodingLength = ENC / (isBinary ? 1 : 4);//how many chars in stp output encode 1 letter
    assert letterEncodingLength != 0 : "invalid encoding length str:" + str;
    int remainder = str.length() % (letterEncodingLength);
    assert remainder == 0 : "unexpected length of " + str;
    StringBuilder b = new StringBuilder();
    for (int i = (str.length() / letterEncodingLength) - 1; i >= 0; i--){
      String s = str.substring(letterEncodingLength * i, letterEncodingLength * (i + 1));
      assert s.length() == letterEncodingLength : "incorrect substring " + s;
      int val = Integer.parseInt(s, isBinary ? 2 : 16);
      char decodeInt = decodeInt(val);
      if (ASCIITable.isReadable(decodeInt)){
        b.append(decodeInt);
      }else{
        b.append("?");
      }
    }
    return b.toString();
  }

  /**
   * Converts the hex string to binary.
   */
  public static String toBinary(String hexStr){
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < hexStr.length(); i++){
      char s = hexStr.charAt(i);
      int val = Integer.parseInt(String.valueOf(s), 16);//hex
      String binaryString = lpadZeros(Integer.toBinaryString(val), 4);
      b.append(binaryString);
    }
    return b.toString();
  }

  private static String lpadZeros(String binaryString, int i){
    int len = binaryString.length();
    assert len <= i : "invalid length " + binaryString;
    return Utils.repeat(i - len, '0') + binaryString;
  }

  /**
   * Returns the size of the encoding, i.e., the number of bits per character.
   */
  public int size(){
    return ENC;
  }

  /**
   * Returns the character that is encoded by the given int. Note: this never
   * creates a new char-int mapping and fails with assetions error if there is
   * no mapping. The reason is that you should encode before you decode.
   */
  public char decodeInt(int i){
    if (OPTIM_ENCODING_SIZE){
      Character v = mapping.getV(i);
      assert v != null : "missing mapping for " + i;
      return v;
    }else
      return (char) i; //XXX for now
  }

  /**
   * Returns the int that encodes the given char. Creates a new char-int mapping
   * if needed.
   */
  public int encodedValue(char c){
    if (OPTIM_ENCODING_SIZE){
      Integer k = mapping.getK(c);
      if (k != null)
        return k;
      k = Integer.valueOf(mapping.size());
      mapping.put(k, c);
      return k;
    }else
      return c;
  }
}
