@echo off
rem Build ISO image, assuming boot loader and all coq has been built

coqc -dont-load-proofs -I . -I x86 -I charge x86\mainbin.v >iso.hex
x86\bin\hexbin iso.hex x86\bin\iso_dir\iso.bin

x86\bin\cdimage -j1 -liSO -bx86\bin\etfs.bin x86\bin\iso_dir x86\bin\iso.iso

