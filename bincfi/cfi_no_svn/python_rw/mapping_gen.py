#!/usr/bin/python
from __future__ import with_statement
from struct import *
import os
import re

def generate_mapping(binname, mytext_addr,output):
	mytext_addr = int(mytext_addr, 16)
	fd = os.open(output,os.O_CREAT|os.O_TRUNC|os.O_RDWR, 0644)

	pattern = re.compile(r"^(?P<offset>[0-9a-fA-F]{1,8})\s+"
				"(?P<type>[^\s]+)\s\_"
				"(?P<addr>[0-9a-fA-F]+)\s*$")
	cmd = "nm "+binname
	with os.popen(cmd) as file:
		for line in file:
			line = line.strip();
			m = pattern.match(line);
			if(m != None):
				#print line;
				old_addr = m.group('addr');
				string = ".long\t0x"+old_addr+"\n"
				os.write(fd, string)
				offset = int(m.group('offset'),16)
				new_addr = offset + mytext_addr
				new_addr = "%lx"%new_addr
				string = ".long\t0x"+new_addr+"\n"
				os.write(fd,string)	
		
generate_mapping("./generated_asm.o","0x04040000","./mapping.s")		
