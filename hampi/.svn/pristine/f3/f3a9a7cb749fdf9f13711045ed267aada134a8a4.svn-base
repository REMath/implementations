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
package hampi.grammars.lexer;

import hampi.grammars.apps.GramgenException;
import hampi.utils.Files;

import java.io.IOException;
import java.util.*;

/**
 * Reads the input file and returns a stream of tokens.
 */
public final class Lexer{

  private char[]            m_data;
  private int               m_count;
  private int               m_size;
  private int               m_currentPtr;
  private int               m_line;
  private final List<Token> m_tokens;

  // Create the lexer from the file given by fname
  public Lexer(String fname) throws IOException{
    m_currentPtr = 0;
    m_count = 0;
    m_line = 1;
    m_tokens = new ArrayList<Token>();

    readFile(fname);
  }

  // How many tokens have been read so far.
  public int getReadTokenCount(){
    return m_count;
  }

  // Prints token names .
  public String tokenString(){
    StringBuilder sb = new StringBuilder();
    Token t = next();
    while (t.m_kind != TokenKind.TEOF){
      sb.append(t.toString());
      sb.append(" ");
      t = next();
    }
    sb.append(t.toString());
    sb.append("\n");
    return sb.toString();
  }

  // Read in the file in one big chunk.
  public void readFile(String fname) throws IOException{
    String fileContents = Files.getFileContents(fname);
    if (fileContents == null){
      System.out.printf("ERROR: unable to open file %s\n", fname);
      throw new GramgenException(1);
    }

    m_size = fileContents.length();
    m_data = fileContents.toCharArray();
  }

  private Token createSimpleToken(TokenKind k){
    Token token = new SimpleToken(k, m_line);
    addToken(token);
    return token;
  }

  private Token createNonterminalToken(int offset, int size){
    String str = new String(m_data, offset, size);// name of the nonterminal
    Token token = new NonterminalToken(str, m_line);
    addToken(token);
    return token;
  }

  private Token createTerminalToken(int offset, int size){
    String str = new String(m_data, offset, size);// name of the terminal
    Token token = new TerminalToken(str, m_line);
    addToken(token);
    return token;
  }

  private Token createSpecialToken(int offset, int size){
    String str = new String(m_data, offset, size);// name of the special token
    Token token = new SpecialToken(str, m_line);
    addToken(token);
    return token;
  }

  private void addToken(Token token){
    m_tokens.add(token);
  }

  // consumes white space characters and update the line number counter.
  private void eatWS(){
    while (m_currentPtr < m_size && (m_data[m_currentPtr] == '\n' || m_data[m_currentPtr] == '\r' || m_data[m_currentPtr] == '\t' || m_data[m_currentPtr] == ' ')){
      if (m_currentPtr < m_size - 1 && m_data[m_currentPtr] == '\r' && m_data[m_currentPtr + 1] == '\n'){
        m_line++; // NOTE works only for LF+CR newlines
      }

      m_currentPtr++;
    }
  }

  // Creates and returns the terminal token that starts at the current
  // position.
  private Token readTerminal(){
    // scan until unescaped double quote
    int i = m_currentPtr + 1;

    for (; i < m_size; i++){
      if (m_data[i] == '"' && i == 0){
        break;
      }
      if (m_data[i] == '"' && m_data[i - 1] != '\\'){
        break;
      }
    }

    // now i points one past the quote (or exactly one past the end in case
    // of EOF)
    int size = i - m_currentPtr + 1;
    int offset = m_currentPtr;
    m_currentPtr += size;

    return createTerminalToken(offset, size);
  }

  // Creates and returns the special token that starts at the current
  // position.
  private Token readSpecial(){
    // scan until closing angle bracket
    int i = m_currentPtr;

    for (; i < m_size; i++){
      if (m_data[i] == '>'){
        break;
      }
    }

    // now i points one past the '>' (or exactly one past the end in case of
    // EOF)
    int size = i - m_currentPtr + 1;
    int offset = m_currentPtr;
    m_currentPtr += size;

    return createSpecialToken(offset, size);
  }

  // Creates and returns the nonterminal token that starts at the current
  // position.
  private Token readNonterminal(){
    // scan until not alpha
    int i = m_currentPtr;

    for (; i < m_size; i++){
      boolean isFirstCharacter = i == m_currentPtr;
      if (isFirstCharacter){
        if (!isAlphaOrUnderscore(m_data[i])){
          break;
        }
      }else{
        if (!isAlphaOrUnderscore(m_data[i]) && !isDigit(m_data[i])){
          break;
        }
      }
    }

    // now i points one past the name (or exactly one past the end in case
    // of EOF)
    int size = i - m_currentPtr;
    int offset = m_currentPtr;
    m_currentPtr += size;

    return createNonterminalToken(offset, size);
  }

  // Returns the kind of the next token, without advancing the current-token
  // pointer.
  public TokenKind lookahead(){
    // save state, read token, restore state

    int size = m_size;
    int currentPtr = m_currentPtr;
    int line = m_line;

    Token t = next();

    m_size = size;
    m_currentPtr = currentPtr;
    m_line = line;
    if (!m_tokens.isEmpty()){
      m_tokens.remove(m_tokens.size() - 1);
      m_count--;
    }

    TokenKind result = t.m_kind;
    return result;
  }

  // Returns the next token in the stream. If you read past the end, it will
  // keep returning TEOF.
  public Token next(){
    eatWS();
    m_count++;

    if (m_currentPtr >= m_size)
      return createSimpleToken(TokenKind.TEOF);

    char ch = m_data[m_currentPtr];
    switch (ch){
    case '(': {
      m_currentPtr++;
      return createSimpleToken(TokenKind.TOPENP);
    }
    case ')': {
      m_currentPtr++;
      return createSimpleToken(TokenKind.TCLOSEP);
    }
    case '|': {
      m_currentPtr++;
      return createSimpleToken(TokenKind.TBAR);
    }
    case '+': {
      m_currentPtr++;
      return createSimpleToken(TokenKind.TPLUS);
    }
    case '?': {
      m_currentPtr++;
      return createSimpleToken(TokenKind.TOPTION);
    }
    case '*': {
      m_currentPtr++;
      return createSimpleToken(TokenKind.TSTAR);
    }
    case '=': {
      m_currentPtr++;
      return createSimpleToken(TokenKind.TEQUALS);
    }
    case ';': {
      m_currentPtr++;
      return createSimpleToken(TokenKind.TSEMICOLON);
    }
    case '"': {
      return readTerminal();// counter increased inside based on size
    }
    case '<': {
      return readSpecial();// counter increased inside based on size
    }
    default: {
      if (isAlphaOrUnderscore(ch))
        return readNonterminal();// counter increased inside based on
      // size
      else{
        System.out.printf("Next: unexpected character '%c' at position %d line %d\n", ch, m_currentPtr, m_line);
        throw new GramgenException(1);
      }
    }
    }
  }

  private boolean isAlphaOrUnderscore(char ch){
    return ch == '_' || ch >= 'a' && ch <= 'z' || ch >= 'A' && ch <= 'Z';
  }

  private boolean isDigit(char ch){
    return ch >= '0' && ch <= '9';
  }
}
