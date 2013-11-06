/**
The MIT License

Copyright (c) 2007 Adam Kiezun

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*/
package stp;

/**
 * Abstract class for all STP-related classes. 
 */
public abstract class STPObject {
    /**
     * The is the raw pointer. Use it directly only if you know what you're doing.   
     */
    public final long handle;
    
    public STPObject(long handle) {
        this.handle= handle;
    }
    
    @Override
    public final boolean equals(Object obj) {
        return obj != null && (obj.getClass().equals(this.getClass())) && ((STPObject)obj).handle == this.handle;
    }
    
    @Override
    public final int hashCode() {
        return (int)handle;
    }

    /**
     * Returns handles for the given objects. 
     */
    static long[] handles(STPObject[] objects) {
        if (objects == null) throw new IllegalArgumentException("null argument");
        
        long[] result= new long[objects.length];
        for (int i = 0; i < result.length; i++) {
            result[i] = objects[i].handle;
        }
        return result;
    }
}
