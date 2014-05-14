CC=clang

all:
	#clang -D_CFI_USE_FAR_JMP -c main.c 
	clang -c main.c 
	clang -shared -fomit-frame-pointer  -Wimplicit-function-declaration -nostdlib  -Wl,-soname=libmainclang.so -o libmainclang.so main.c  -lc -ldl 
	gcc -o mainclang main.c -ldl
	./extract_code.py main.o code
	#gcc -shared -Wl,-soname=libmain.so -o libmain.so main.c -ldl -lc
	#gcc -o mymain mymain.s -Wl,-rpath=${PWD} -L${PWD} -lmainclang -lc -ldl

clean:
	rm -f mymain libmainclang.so libmain.so mainclang main.o code
