#!/usr/bin/python
from __future__ import with_statement
from struct import *

#from __future__ import with_statement
import re
import os
def get_section_info(binname, secname, info):
	pattern = re.compile(r"\s*\[\s*(?P<num>[\d]{1,2})\]\s*"
				"(?P<name>[\S]+)\s*"
				"(?P<type>[\S]+)\s*"
				"(?P<addr>[\S]+)\s*"
				"(?P<offset>[\S]+)\s*"
				"(?P<size>[\S]+)\s*"
				"[^\n]*$")
	cmd = "readelf -S " + binname
	with os.popen(cmd) as file:
		for line in file:
			line = line.strip()
			m = pattern.match(line)
			if((m != None) and (m.group('name') == secname)):
				print line
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
"""
				"(?P<info>[0-9a-fA-F]{1,8})\s+"
				"(?P<type>[^\s]+)\s+"
				"(?P<symvalue>[0-9a-fA-F]{1,8})\s+"
	"(?P<name>[^\n]+)$")
"""
def patch_mytext(binname):
	fd = os.open(binname, os.O_RDWR)
	base = get_section_info(binname,".mytext",'offset')
	value = get_section_info(binname,".mydata",'addr')
	pattern = re.compile(r"^(?P<offset>[0-9a-fA-F]{1,8})\s+"
				"(?P<info>[0-9a-fA-F]{1,8})\s+"	
				"(?P<type>[^\s]+)\s+"
				"(?P<symvalue>[0-9a-fA-F]{1,8})\s+"
				"(?P<name>[^\n]+)$")
	#print "base:%x"%base
			
	cmd = "readelf -r ./lyx/generated_asm.o"
	with os.popen(cmd) as file:
		for line in file:
			line = line.strip()
			m = pattern.match(line)
			#print line
			if(m != None):
				print line
				offset = base + int(m.group('offset'),16)
				os.lseek(fd, offset, os.SEEK_SET)
				os.write(fd, pack('<i',value))
patch_mytext("./lyx/lyx_final")
