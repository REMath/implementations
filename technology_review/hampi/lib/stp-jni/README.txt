This is a Java binding for the STP decision procedure.
The binding was done on 4 Jan 2008 by akiezun@mit.edu and is relased under the MIT licence.

You can use either the STPJNI class, which provides a raw, C-like access to STP, or you can use the STPObject hierarchy, which gives more 
object-oriented access. The latter is almost always preferable. 

To build on 64-bit machines, use make all64. Consult the Makefile
To run the examples (and use the binding in general), you need to set LD_LIBRARY_PATH to the lib folder (or use the java.library.path property).

The binding is almost finished. The only remaining APIs are: 
(left undone because they require some C hacking and I did not need them immediately - please send me patches)

   void vc_printExprToBuffer(VC vc, Expr e, char **buf, unsigned long * len);
   void vc_printQueryStateToBuffer(VC vc, Expr e, char **buf, unsigned long *len, int simplify_print);
   void vc_printCounterExampleToBuffer(VC vc, char **buf,unsigned long *len);
   unsigned long long int getBVUnsignedLongLong(Expr e);
   unsigned int getBVUnsigned(Expr e);
   Expr vc_bvConstExprFromLL(VC vc, int n_bits, unsigned long long value);
   void vc_registerErrorHandler(void (*error_hdlr)(const char* err_msg));  

Please send enhancements, fixes and problem reports to me or Vijay Ganesh, the author or STP. 