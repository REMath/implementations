#!/usr/bin/python
from __future__ import with_statement
from struct import *

#from __future__ import with_statement
import re
import os
import sys

def get_section_info(binname, secname, info):
	pattern = re.compile(r"\s*\[\s*(?P<num>[\d]{1,2})\]\s*"
				"(?P<name>[\S]+)\s*"
				"(?P<type>[\S]+)\s*"
				"(?P<addr>[\S]+)\s*"
				"(?P<offset>[\S]+)\s*"
				"(?P<size>[\S]+)\s*"
				"[^\n]*$")
	cmd = "readelf -S " + binname;
	with os.popen(cmd) as file:
		for line in file:
			line = line.strip();
			m=pattern.match(line);
			if((m != None) and (m.group('name') == secname)):
				if(info == 'num'):
					return int(m.group(info),10)
				if((info == 'addr') or 
				(info == 'offset') or
				(info == 'size')
				):
					return int(m.group(info),16)
				else:
					return m.group(info)
				return m.group(info)
	return None


def extract_data(binname,secname,output):
	gen_asm_offset = get_section_info(binname, secname, "offset");	
	gen_asm_size = get_section_info(binname, secname, "size");
	fd = os.open(binname,os.O_RDWR);
	os.lseek(fd, gen_asm_offset, os.SEEK_SET);
	buf = os.read(fd, gen_asm_size);
	fd2 = os.open(output, os.O_CREAT|os.O_TRUNC|os.O_RDWR, 0644)
	os.write(fd2,buf);
	os.close(fd2);
	os.close(fd);
	print "text offset %lx"%gen_asm_offset
	print "text size %lx"%gen_asm_size


def main():
	orig_bin = sys.argv[1];
	output_file = sys.argv[2];
	extract_data(orig_bin, ".text",output_file);


main();
