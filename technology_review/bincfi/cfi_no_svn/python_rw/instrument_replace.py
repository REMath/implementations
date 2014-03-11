#!/usr/bin/python
from __future__ import with_statement
from struct import *

import sys
import os
#default_path="/home/mingwei/Downloads/eglibc-2.13/build/../installdir/lib/"
default_path="/home/bip/installdir/lib/"
target_dir="./target_elf"

def main():
	cmd = sys.argv[1];
	if(cmd == "-i"):
		#instrument elf
		if(check_if_instrumented(sys.argv[2]) == 0):
			replace_elf(sys.argv[2],sys.argv[3:]);
		else:
			print "there is no need to instrument this file";
	elif(cmd == "-r"):
		#recover original elf
		restore_elf(sys.argv[2]);
	elif(cmd == "-ri"):
		restore_elf(sys.argv[2]);	
		if(check_if_instrumented(sys.argv[2]) == 0):
			replace_elf(sys.argv[2],sys.argv[3:]);
	elif(cmd == "-I"):
		#instrument elf
		if(check_if_instrumented(default_path+sys.argv[2]) == 0):
			replace_elf(default_path+sys.argv[2],sys.argv[3:]);
		else:
			print "there is no need to instrument this file";
	elif(cmd == "-R"):
		#recover original elf
		restore_elf(default_path+sys.argv[2]);
	elif(cmd == "-RI"):
		restore_elf(default_path+sys.argv[2]);
		if(check_if_instrumented(default_path+sys.argv[2]) == 0):
			replace_elf(default_path+sys.argv[2],sys.argv[3:]);


def replace_elf(binpath,args):
	binname = os.path.basename(binpath);
	dirname = os.path.dirname(binpath);
	new_dirname = dirname+"_orig";
	print "begin instrumenting binary file: %s"%binname;
	cmd = "./modify_elf.py "+binpath+" "+" ".join(args);
	os.system(cmd);
	if(os.path.exists(target_dir+"/"+binname+"/stat") == False):
		print "error in translating elf file";
		exit(1);
	cmd = "mkdir -p  "+new_dirname;
	os.system(cmd);
	print "renaming original binary file: %s"%binname;
	cmd = "mv  "+binpath+ " "+new_dirname;
	os.system(cmd);
	print "copying new binary: %s_final"%binname
	cmd = "cp -P "+target_dir+"/"+binname+"/"+binname+"_final   "+binpath;
	os.system(cmd);
def restore_elf(binpath):
	binname = os.path.basename(binpath);	
	dirname = os.path.dirname(binpath);
	new_dirname = dirname+"_orig";

	cmd = "cp -P "+new_dirname+"/"+binname+" "+binpath;
	os.system(cmd);
	print "elf file restored";
	
def check_if_instrumented(binpath):
	fd = os.open(binpath, os.O_RDONLY)
	if(fd == -1):
		return 1;
	os.lseek(fd, 12, os.SEEK_SET);
	value = unpack('<i',os.read(fd, 4))[0]
	print "value: %d"%value;
	if(value !=0):
		print "this is an instrumented elf file";
		return 1;
	else:
		print "this is an original elf file";
		return 0;
main();
