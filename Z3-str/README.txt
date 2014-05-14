Z3-str is a string theory plug-in built on the powerful Z3 SMT solver (http://z3.codeplex.com/).

Z3-str is implemented using a Linux build of Z3 4.1, which is a version before Z3 became open-source. However, the download link for the Linux build of Z3 4.1 on Z3's old website (http://research.microsoft.com/en-us/um/redmond/projects/z3/old/download.html) seems gone. 

Instead, our implementation can be built with Z3 4.1.1. The source code of version 4.1.1 is available at Z3's new official web site (http://z3.codeplex.com/releases/view/95640).

  
  
What are in the tarball:
----------------------------
test                   small test cases for Z3-str
testcase_in_kaluza     test cases used to compare with Kaluza( http://webblaze.cs.berkeley.edu/2010/kaluza/ )
testcase_rce           test cases used to compare with our previous RCE detection work in ICSE'13
Z3-str.py              Wrapper. Once the binary of Z3-str is built, run the string solver with this script


Usage:
----------------------------
1. Download the source code of Z3 4.1.1 (http://z3.codeplex.com/releases/view/95640) and build.
     $autoconf
     $./configure
     $make
     $make a     
   ------------------  
   Note: You may need to modify Z3's code to compile (at least for me in Ubuntu 12.10).
     
     (1) 243 @ lib/buffer.h:
         push_back(elems[i]);  
         ==>  this->push_back(elems[i]);
     
     (2) 201 @ lib/ref_vector.h:
         append(other);        
         ==>  this->append(other);
         
         206 @ lib/ref_vector.h:
         append(sz, data);
         ==>  this->append(sz, data);
       
         274 @ lib/ref_vector.h:
         append(other);
         ==>  this->append(other);
         
     (3) Add "#include <unistd.h>" in lib/debug.cpp
   ------------------  

2. Modify variable "Z3_path" in the Makefile of Z3-str to indicate the location of headers and libs of Z3 4.1.1.

3. Build Z3-str
     $make
   ------------------  
   Note: If you see linking errors like:
           > scoped_timer.cpp: undefined reference to `timer_create'
           > scoped_timer.cpp: undefined reference to `timer_settime'
           > scoped_timer.cpp: undefined reference to `timer_delete'
         please add '-lrt' in the g++ line of the Makefile to fix these. 
         [Thanks Benjamin Spencer for pointing this out]
   ------------------      
  
4. In "Z3-str.py", change the value of the variable "solver" to point to the Z3-str binary "str" built.    

5. Run Z3-str
     $./Z3-str.py <inputFile>
   e.g 
     $./Z3-str.py test/concat-002