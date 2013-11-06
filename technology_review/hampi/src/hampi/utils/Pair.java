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

import java.io.Serializable;

public final class Pair<L, R> implements Serializable{
  private static final long serialVersionUID = 4302199860575637153L;

  public Pair(L l, R r){
    this.first = l;
    this.second = r;
  }

  public static <L, R> Pair<L, R> create(L l, R r){
    return new Pair<L, R>(l, r);//NOTE: this method is a workaround for missing param type inference for constructors
  }

  public L first;
  public R second;

  @Override
  public String toString(){
    return "<" + first + ", " + second + ">";
  }

  @Override
  public int hashCode(){
    return (first.hashCode() + 17) * (second.hashCode() + 29);
  }

  @SuppressWarnings("unchecked")
  @Override
  public boolean equals(Object obj){
    if (!(obj instanceof Pair))
      return false;
    Pair<L, R> that = (Pair<L, R>) obj;
    return this.first.equals(that.first) && this.second.equals(that.second);
  }
}
