#!/usr/bin/python
from __future__ import with_statement
from struct import *

#from __future__ import with_statement
import re
import os
import sys
import math
import random
import string
import ctypes
import argparse
class arch(object):
		INT_SIZE=4

class phdr(object):
	PT_NULL		= 0
	PT_LOAD		= 1
	PT_DYNAMIC	= 2
	PT_INTERP	= 3
	PT_NOTE		= 4
	PT_SHLIB	= 5
	PT_PHDR		= 6
	PT_TLS		= 7
	PT_NUM		= 8
	PT_LOOS		= 0x60000000
	PT_GNU_EH_FRAME	= 0x6474e550
	PT_GNU_STACK	= 0x6474e551
	PT_GNU_RELRO	= 0x6474e552
	PT_LOSUNW	= 0x6ffffffa
	PT_SUNWBSS	= 0x6ffffffa
	PT_SUNWSTACK	= 0x6ffffffb
	PT_HISUNW	= 0x6fffffff
	PT_HIOS		= 0x6fffffff
	PT_LOPROC	= 0x70000000
	PT_HIPROC	= 0x7fffffff
	#offset of fields in a PHDR entry
  	p_type		= arch.INT_SIZE *0
  	p_offset	= arch.INT_SIZE *1		
  	p_vaddr		= arch.INT_SIZE *2		
  	p_paddr		= arch.INT_SIZE *3		
  	p_filesz	= arch.INT_SIZE *4		
  	p_memsz		= arch.INT_SIZE *5		
  	p_flags		= arch.INT_SIZE *6		
  	p_align		= arch.INT_SIZE *7		


class  elf_basic(object):

	instance = None;

	@classmethod
	def getELFobject(cls):
		if(cls.instance !=None):
			return cls.instance;
		else:
			cls.instance = elf_basic()
			return cls.instance
	def set_binname(self,name):
		self.binname = name;
	def __init__(self):
		self.offset_dynamic = 0
		elf_basic.instance = self;

	def myprint(self):
		print "this is a test of elf_basic"

	def get_elfhdr_info(self, binpath, attribute):
		elfhdr_pa = re.compile(r'[^:]:\s*[^\n]$');

		cmd = "readelf -h ";
		cmd += binpath;
		with os.popen(cmd) as file:
			for line in file:
				line = line.rstrip()
				if attribute in line:
					str = line.split(':');
					str = str[1].strip();
					str = str.split(' ');
					if(attribute == "Entry point address:"):
						info = str[0];
					elif(attribute == "Type:"):
						info = str[0];
					else:
						info = str[0];
						info = int(str[0],10);
					#print info;
			
		return info

	def convert_vma_to_offset(self, binname, vma):
		vma = int(vma, 16)
		num = self.get_elfhdr_info(binname, "Number of section headers:")
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
				if(m != None):
					vma_start = int(m.group('addr'),16)
					size = int(m.group('size'),16)
					if(((vma_start+size) <= vma) or (vma < vma_start)):
						continue
					else:	
						if(m.group('name') == '.bss'):
							return int(m.group('offset'),16) 
						else:
							offset_start = int(m.group('offset'), 16)
							offset = offset_start + (vma - vma_start)
							return offset 
		return 0

	def get_section_info(self, binname, secname, info):
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

	"""
	ELF Header Format:
		Field		Size		Offset
		magic:		16bytes		0
		type:		2 bytes		16
		machine:	2 bytes		18
		version:	4 bytes		20
		entry:		4 bytes		24
		phdr_offset:	4 bytes		28
		sechdr_offset:	4 bytes		32
		flags:		4 bytes		36
		elfhdr_size:	2 bytes		40
		phdr_ent_size:	2 bytes		42
		phdr_ent_cnt:	2 bytes		44
		sechdr_ent_size:2 bytes		46
		sechdr_ent_cnt:	2 bytes		48
		sechdr_strtab:	2 bytes		50

	total byte: 0x34 bytes( should be)
	"""
	def modify_elfhdr_info(self, binpath, attribute, value):
		fd = os.open(binpath, os.O_RDWR);
		if(attribute == "entrypoint"):
			os.lseek(fd, 24, os.SEEK_SET);
			value = pack("<i",value);
			os.write(fd, value);
			value = unpack('<i',value)
			print "modify entry point to %lx\n"%value;
		os.close(fd);
	def modify_phdr_info(self, binname, offset, seg_type, attribute, value):
		global arch;
		phdr_num = self.get_elfhdr_info(binname, "Number of program headers:");
		phdr_size = self.get_elfhdr_info(binname,"Size of program headers:");
		phdr_start = self.get_elfhdr_info(binname,"Start of program headers:");
		fd = os.open(binname, os.O_RDWR);
		os.lseek(fd, phdr_start, os.SEEK_SET)

		for idx in xrange(0, phdr_num):
			stype = unpack('<i',os.read(fd,4))[0];
			#if phdr_type == 0x00000003: #phdr entry type: interp
			os.lseek(fd, -arch.INT_SIZE, os.SEEK_CUR)
			print "index:%d, type:%x"%(idx, stype);
			if(stype == seg_type):
				if(stype == phdr.PT_LOAD):
					os.lseek(fd, phdr.p_offset, os.SEEK_CUR)
					p_offset = unpack('<i',os.read(fd,4))[0];
					if(p_offset == offset):
						os.lseek(fd, -(phdr.p_offset+4), os.SEEK_CUR)
						#print "match  segement";
						break;
					else:
						os.lseek(fd, -(phdr.p_offset+4), os.SEEK_CUR)
						os.lseek(fd, phdr_size, os.SEEK_CUR)
						continue;	
				else:
					#print "match  segement";
					break;
			os.lseek(fd, phdr_size, os.SEEK_CUR)
		
		os.lseek(fd, attribute, os.SEEK_CUR)
		os.write(fd, pack('<i',value));
		pass

	def modify_section_info(self, binpath, secname, attribute,value):
		secnum = self.get_section_info(binpath, secname, "num")
		if(secnum == None):
			print "section %s does not exists\n"%secname;
			return
		print "section num: %d"%secnum
		sectable_start = self.get_elfhdr_info(binpath, "Start of section headers:")
		print "section table start:%x"%sectable_start
		section_size = self.get_elfhdr_info(binpath, "Size of section headers:")
		print "section entry size:%d"%section_size
		interp_offset = sectable_start +secnum * section_size
		if(attribute == "index"):
			interp_offset = interp_offset + 0
		elif(attribute == "type"):
			interp_offset = interp_offset + 4;
		elif(attribute == "flags"):
			interp_offset = interp_offset + 8;
		elif(attribute == "addr"):
			interp_offset = interp_offset + 12;
		elif(attribute == "offset"):
			interp_offset = interp_offset + 16;
		elif(attribute == "size"):
			interp_offset = interp_offset + 20;
		elif(attribute == "link"):
			interp_offset = interp_offset + 24;
		elif(attribute == "info"):
			interp_offset = interp_offset + 28;
		elif(attribute == "align"):
			interp_offset = interp_offset + 32;
		elif(attribute == "entsize"):
			interp_offset = interp_offset + 36;
		fd = os.open(binpath, os.O_RDWR);
		os.lseek(fd, interp_offset, os.SEEK_SET);
		os.write(fd, pack('<i',value));
		fd = os.close(fd);

	def add_dynamic_option(self, binname,option, value):	
		#now get the PHDR information
		phdr_num = self.get_elfhdr_info(binname, "Number of program headers:");
		phdr_size = self.get_elfhdr_info(binname,"Size of program headers:");
		phdr_start = self.get_elfhdr_info(binname,"Start of program headers:");

		dyn_offset = 0;
		dyn_infile_size = 0;

		#enlarge the dynamic segment by 8 bytes
		offset_begin = phdr_start
		fd_phdr = os.open(binname, os.O_RDWR);
		os.lseek(fd_phdr, offset_begin, os.SEEK_SET)
		print "phdr_num:%lx"%phdr_num
		for size in xrange(0, phdr_num):
			os.lseek(fd_phdr, phdr_size, os.SEEK_CUR)
			phdr_type = unpack('<i',os.read(fd_phdr,4))[0];
			os.lseek(fd_phdr,-4,os.SEEK_CUR);
			print "phdr_type: %lx"%phdr_type
			if phdr_type == 0x00000002: #phdr entry type: dynamic
				os.lseek(fd_phdr,4,os.SEEK_CUR);
				dyn_offset = unpack('<i',os.read(fd_phdr,4))[0];
				print "offset of dynamic segment: %lx"%dyn_offset
				os.lseek(fd_phdr,8,os.SEEK_CUR);
				dyn_infile_size = unpack('<i',os.read(fd_phdr,4))[0]
				os.lseek(fd_phdr,-4,os.SEEK_CUR);
			
		print "offset of dynamic segment: %lx"%dyn_offset
		print "size of dynamic segment: %lx"%dyn_infile_size
		#os.close(fd_phdr);

		fd = os.open(binname,os.O_RDWR);
		os.lseek(fd, dyn_offset, os.SEEK_SET);
		#os.lseek(fd, dyn_offset + dyn_infile_size - 8, os.SEEK_SET);
		print "move to beginning of dynamic segment: %lx"%(dyn_offset )
		
		dyn_start = dyn_offset;
		dyn_end = dyn_offset + dyn_infile_size - 8;
		enlarge_dynamic = 1;
		while (dyn_start < dyn_end):
			dyn_option = unpack('<i', os.read(fd,4))[0];
			dyn_content = unpack('<i', os.read(fd,4))[0];
			if(dyn_option ==0 and dyn_content ==0):
			#reach the end of dynamic segment
				enlarge_dynamic = 0;
				os.lseek(fd, -8, os.SEEK_CUR);
				os.write(fd,pack('<i',option));#0x18 means BIND_NOW
				os.write(fd,pack('<i',value));
				break;
			dyn_start+=8;
			
		
		if(enlarge_dynamic ==1):
			os.write(fd,pack('<i',option));#0x18 means BIND_NOW
			os.write(fd,pack('<i',value));
			os.write(fd,pack('<i',0x00000000));
			os.write(fd,pack('<i',0x00000000));
			os.write(fd_phdr,pack('<i',dyn_infile_size+8))
			os.write(fd_phdr,pack('<i',dyn_infile_size+8))

	def get_dynamic_offset(self,binname):
		phdr_num = self.get_elfhdr_info(binname, "Number of program headers:");
		phdr_size = self.get_elfhdr_info(binname,"Size of program headers:");
		phdr_start = self.get_elfhdr_info(binname,"Start of program headers:");

		dyn_offset = 0;
		dyn_infile_size = 0;

		offset_begin = phdr_start
		fd_phdr = os.open(binname, os.O_RDWR);
		os.lseek(fd_phdr, offset_begin, os.SEEK_SET)
		print "phdr_num:%lx"%phdr_num
		for size in xrange(0, phdr_num):
			os.lseek(fd_phdr, phdr_size, os.SEEK_CUR)
			phdr_type = unpack('<i',os.read(fd_phdr,4))[0];
			os.lseek(fd_phdr,-4,os.SEEK_CUR);
			#print "phdr_type: %lx"%phdr_type
			if phdr_type == 0x00000002: #phdr entry type: dynamic
				os.lseek(fd_phdr, 4, os.SEEK_CUR);
				self.offset_dynamic = unpack('<i',os.read(fd_phdr,4))[0]
				os.close(fd_phdr);
				return self.offset_dynamic;
		os.close(fd_phdr);
		return None

	def read_dynamic_option(self, binname, option):
		if(self.offset_dynamic == 0):
			self.offset_dynamic=self.get_dynamic_offset(binname);
			if(self.offset_dynamic == 0):
				print "cannot find dynamic segment, abort";
				exit(1);
		fd = os.open(binname,os.O_RDWR);
		os.lseek(fd, self.offset_dynamic, os.SEEK_SET);


		dyn_opt = unpack('<i', os.read(fd,4))[0];
		while(dyn_opt != 0):
			#print "dynamic option type: %d"%dyn_opt
			dyn_value = unpack('<i', os.read(fd,4))[0];
			if(dyn_opt == option):
				os.close(fd);
				return dyn_value
			dyn_opt = unpack('<i', os.read(fd,4))[0];
		return None

	def update_dynamic_option(self, binname, option,new_value):
		if(self.offset_dynamic == 0):
			self.offset_dynamic=self.get_dynamic_offset(binname);
			if(self.offset_dynamic == 0):
				print "cannot find dynamic segment, abort";
				exit(1);
		fd = os.open(binname,os.O_RDWR);
		os.lseek(fd, self.offset_dynamic, os.SEEK_SET);

		dyn_opt = unpack('<i', os.read(fd,4))[0];
		while(dyn_opt != 0):
			#print "dynamic option type: %d"%dyn_opt
			if(dyn_opt == option):
				os.write(fd,pack('<i',new_value));
				os.close(fd);
				return 1;
			dyn_value = unpack('<i', os.read(fd,4))[0];
			dyn_opt = unpack('<i', os.read(fd,4))[0];
		return None

	def get_exec_memory_range(self, binpath):
		#step 1: get code memory range
		cmd="readelf -W -S "+binpath+'| sed \'s/\[\s*//g\'|grep \' AX \'| awk \'{print $4 \" \" $5 \" \" $6}\''
		pattern = re.compile(r"^(\S+)\s+(\S+)\s+(\S+)");
		exec_begin = 0x7fffffff;
		exec_end = 0x0;
		exec_end_size = 0;
		with os.popen(cmd) as file:
			for line in file:
				line = line.strip()
				m = pattern.match(line);
				if(m != None):
					#print line
					#print m.group(1);
					addr = int(m.group(1), 16);
					size = int(m.group(3), 16);
					if(addr < exec_begin):
						exec_begin = addr
					if(addr > exec_end):
						exec_end = addr
						exec_end_size = size;
			exec_end += exec_end_size;
			#print "exec_begin %x"%exec_begin
			#print "exec_end %x"%exec_end
			print "%x %x"%(exec_begin, exec_end);
		return (exec_begin, exec_end)
	def extract_data(self, binname,secname,output):
		gen_asm_offset = self.get_section_info(binname, secname, "offset");	
		gen_asm_size = self.get_section_info(binname, secname, "size");
		if(gen_asm_offset == None):
			print "extract_data: "+binname+" file does not exist";
			return;
		fd = os.open(binname,os.O_RDWR);
		os.lseek(fd, gen_asm_offset, os.SEEK_SET);
		buf = os.read(fd, gen_asm_size);
		fd2 = os.open(output, os.O_CREAT|os.O_TRUNC|os.O_RDWR, 0644)
		os.write(fd2,buf);
		os.close(fd2);
		os.close(fd);
		print "text offset %lx"%gen_asm_offset
		print "text size %lx"%gen_asm_size
	
	def compile_inject_data(self, htables, binname):
		for h in htables:
			base = os.path.basename(h.output_data)
			raw = base.split('.')[0] #eliminate the extention name
			cmd = "gcc -c "+base
			os.system(cmd)
			obj = raw+".o"
			sec = h.get_secname();
			
			self.extract_data(obj,".text",raw)

			cmd = "objcopy --add-section "+sec+"="+raw +" "+binname + " " + binname
			print "%s"%cmd
			os.system(cmd)
			self.modify_section_info(binname,sec,"align",0x00001000)



def static_var(varname, value):
    def decorate(func):
        setattr(func, varname, value)
        return func
    return decorate

@static_var("initialized", False)
def translate_orig_addr_to_offset(binname, address):
	if(translate_orig_addr_to_offset.initialized == False):
		#os.chdir("./target_elf/"+binname)
		value = get_mapping_offset(address)
		#os.chdir("../..")
		return value
	else:
		return get_mapping_offset(address)

#from the original address to get the offset in generated binary
#address: string type representing an address
@static_var("initialized", False)
@static_var("file_nm", None)
@static_var("htable", dict)
def get_mapping_offset(address):
	addr = int(address, 16);
	p = re.compile(r"^([0-9a-fA-Fx]+)\s+([\S]+)\s+_([0-9a-fA-F]+)$");
	cmd = "nm generated_asm.o >static_symbols"
	file_begin = int("0",10);
	#address = address.lstrip('0x');
	file_nm = None;
	if(get_mapping_offset.initialized == False):
		print "inside"
		os.system(cmd);
		get_mapping_offset.file_nm = open("./static_symbols",'r');
		get_mapping_offset.initialized = True;
		get_mapping_offset.htable = dict();
		get_mapping_offset.htable[addr] = None;
		for line in get_mapping_offset.file_nm:
			line = line.strip()
			m = p.match(line);
			if(m != None):
				get_mapping_offset.htable[int(m.group(3),16)] = m.group(1);

	return get_mapping_offset.htable.get(addr, None);


def main():
	parser = argparse.ArgumentParser()
	parser.add_argument('binfile', nargs='?');
	parser.add_argument('-exec_range', action="store_true")
	args = parser.parse_args()

	binname = args.binfile;
	eb = elf_basic();

	if(args.exec_range):
		eb.get_exec_memory_range(binname);


if __name__ == "__main__":
	main()
