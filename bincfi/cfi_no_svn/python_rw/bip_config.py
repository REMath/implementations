#!/usr/bin/python
from __future__ import with_statement
from struct import *

#from __future__ import with_statement
import re
import os
import sys
import bitarray
import operator
from elf_basic import *

class bip_config(object):

	BITARRAY_SIZE = 64 #in bits
	BITARRAY_LEN = 8   #in bytes
	BITARRAY_OFFSET = 0x64
	#bip_opt: str_name <=> str_value
	def __init__(self, fname):
		self.initialized = 1;
		self.get_bitarray_offset()
		self.init_mapping_from_file(fname);
		self.opt_array = bitarray.bitarray(bip_config.BITARRAY_SIZE)
		self.opt_array.setall(False)

	def __init__(self, fname, bip_opt):
		self.initialized = 1;
		self.get_bitarray_offset()
		self.init_mapping_from_file(fname);
		self.opt_array = bitarray.bitarray(bip_config.BITARRAY_SIZE)
		self.opt_array.setall(False)
		self.setup_bitarray(bip_opt)

	def setup_bitarray(self,  options):
		for opt in options:
			#print opt;
			if opt in self.idx_mapping:
				idx = self.idx_mapping[opt]
				#print "index:%d"%idx
				length = self.len_mapping[opt]
				bstr = ( bin(int(options[opt],10))[2:] ).zfill(64);
				bstr = bstr[64-length:]
				#print bstr
				tmp = bitarray.bitarray(bstr);
				bstr_len = len(bstr)
				base = self.idx_mapping[opt];
				for i in range(0,bstr_len):	
					self.opt_array[base+i] = tmp[i];
		#print self.opt_array
			
	#mapping: str_name <=> idx
	def init_mapping_from_file(self, fname):
		self.idx_mapping = dict();
		self.len_mapping = dict();
		fd = open(fname,'r');
		#print "hello, world";
		p = re.compile(r"([0-9]+)\t([0-9]+)\t(.*)\s*$");
		real_offset = 0;
		for line in fd.readlines():
			m = p.match(line)
			if(m != None):
				#print "%s %s"%(m.group(1), m.group(2))
				opt_name = m.group(3);
				self.idx_mapping[opt_name] = real_offset;
				length = int(m.group(2), 10)
				self.len_mapping[opt_name] = length;
				real_offset += length;

	def write_options(self, fd):
		b = self.opt_array.tobytes();
		l = len(b);
		for i in range(l):
			os.write(fd, b[i]);
		#with open(binfile,'wb') as fh:
			#fh.close()
	#		fh.seek(offset);

	def get_bitarray_offset(self):
		cmd = "cp asm_utility/signature.s /tmp"
		os.system(cmd)
		cmd = "gcc -o /tmp/signature.o -c /tmp/signature.s"
		os.system(cmd)
		cmd = "readelf -r /tmp/signature.o"
		with os.popen(cmd) as file:
			p = re.compile(r"^(?P<offset>[0-9a-fA-F]{1,8})\s+"
				"(?P<info>[0-9a-fA-F]{1,8})\s+"	
				"(?P<type>[^\s]+)\s+"
				"(?P<symvalue>[0-9a-fA-F]{1,8})\s+"
				"(?P<name>bip_options_begin)\s*$")
			for line in file:
				m = p.match(line);
				if(m != None):
					#print line;
					offset =int(m.group('offset'),16)
					bip_config.BITARRAY_OFFSET = offset;

		#print "offset is %d"%bip_config.BITARRAY_OFFSET
					
	def read_options(self, binname):
		eb = elf_basic();
		mytext_base = eb.get_section_info(binname,".mytext",'offset');
		if(mytext_base == None):
			return;
		with open(binname, 'rb') as fh:
			fh.seek(mytext_base+bip_config.BITARRAY_OFFSET);
			#buf = bytearray(fh.read(bip_config.BITARRAY_LEN))
			buf=fh.read(bip_config.BITARRAY_LEN)
			self.opt_array = bitarray.bitarray()
			self.opt_array.frombytes(buf);
			#print self.opt_array

	def print_options(self):
		sorted_opt = sorted(self.idx_mapping.iteritems(), key=operator.itemgetter(1))
		for opt in sorted_opt:
			idx = opt[1];
			name = opt[0];
			length = self.len_mapping[name]
			#print "%d"%length
			tmp = self.opt_array[idx:idx+length].to01()
			#print "%s"%tmp
			tmp = int(tmp,2);
			print "%d\t%s=%d"%(idx,name,tmp)

if(len(sys.argv) <2):
	print "usage ./bip_config.py <binary name>"
	exit(0);

binname = sys.argv[1];


bip_opt = dict();
#bip_opt['transparent_call'] = '1'
#bip_opt['bundle_align'] = '2'
#bip_opt['nsparent_call'] = '1';

conf = bip_config("bip_options",bip_opt);
#conf.get_bitarray_offset();
conf.read_options(binname)
conf.print_options();
