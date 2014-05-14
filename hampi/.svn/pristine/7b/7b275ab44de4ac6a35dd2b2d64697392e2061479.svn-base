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

public final class SimpleToken extends Token{
  public SimpleToken(TokenKind tk, int line){
    super(tk, line);
  }

  @Override
  public String toString(){
    switch (m_kind){
    case TEOF:
    case TSEMICOLON:
    case TEQUALS:
    case TBAR:
    case TPLUS:
    case TOPTION:
    case TSTAR:
    case TOPENP:
    case TCLOSEP: {
      return m_kind.toString();
    }
    default: {
      System.out.printf("ToString: unexpected token kind %dline %d\n", m_kind, m_line);
      throw new GramgenException(1);
    }
    }
  }
}
