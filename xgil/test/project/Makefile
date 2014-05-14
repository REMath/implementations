
all: main.o work.o
	gcc-4.7 -o crashAndBurn main.o work.o

%.o: %.c
	gcc-4.7 -c -o $@ $<

clean:
	rm -f *.o crashAndBurn
