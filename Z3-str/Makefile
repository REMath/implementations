default: all

# Change the path to Z3 4.1.1 accordingly
# The directory indicated by this path should contain "lib" and "bin"
# e.g. "/home/z3_src_4.1.1"
Z3_path = z3_src_4.1.1

#-----------------------------------------

JUNK = str
SOURCE = strTheory.cpp testMain.cpp
INCLUDE = $(Z3_path)/lib
LIB = $(Z3_path)/bin/external


all: $(SOURCE)
	g++ -O3 -fopenmp -static -I$(INCLUDE) -L$(LIB) $(SOURCE) -lz3 -o str -Wall
	
clean:
	rm -f $(JUNK)

