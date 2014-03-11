#!/usr/bin/python
from __future__ import with_statement
from struct import *

#from __future__ import with_statement
import re
import os
import os.path
import sys
import math
import random
import string
import ctypes
import argparse
#==================================
from elf_basic import *
from bip_config import *
from hash_lookup import *
eb = None # the basic object containing elf operations
lookup_routines = None # the customer hash lookup routines

#global variables are defined below
#==================================
start_of_mytext = None #the address of _start in generated binary
mytext_base = None #the starting address of generated binary in orignal ELF image
orig_entry_addr = None
orig_entry_offset = None
global_binname = None;

mapping_size = 0 # the size of instruction mapping
local_mapping_size = 0 # the size of instruction mapping for translated address
insn_mask = 0
insn_begin = 0
insn_end = 0
local_insn_begin = 0
local_insn_end = 0

ret_insn_begin = 0
ret_insn_end = 0
ret_local_insn_begin = 0
ret_local_insn_end = 0
ret_mapping_size = 0 # the size of instruction mapping for ret enforcement
ret_local_mapping_size=0
ret_insn_mask=0

#enforcing that ijmp in PLT only goes to exported symbol
plt_insn_begin = 0
plt_insn_end = 0
plt_local_insn_begin = 0
plt_local_insn_end = 0
plt_mapping_size = 0 # the size of instruction mapping for plt jump enforcement
plt_local_mapping_size=0
plt_insn_mask=0
plt_longest_collision=0;

#elf options 
ET_NONE=0
ET_REL=1
ET_EXEC=2
ET_DYN=3
ET_CORE=4
#elf link options:
DYNAMIC_LINKED=0;
STATIC_LINKED=1;
#option in dynamic section
DT_NULL=0
DT_NEEDED=1
DT_PLTRELSZ=2
DT_PLTGOT=3
DT_HASH=4
DT_STRTAB=5
DT_SYMTAB=6
DT_RELA=7
DT_RELASZ=8
DT_RELAENT=9
DT_STRSZ=10
DT_SYMENT=11
DT_INIT=12
DT_FINI=13
DT_SONAME=14
DT_RPATH=15
DT_SYMBOLIC=16
DT_REL=17
DT_RELSZ=18
DT_RELENT=19
DT_PLTREL=20
DT_DEBUG=21
DT_TEXTREL=22
DT_JMPREL=23
DT_BIND_NOW=24
DT_INIT_ARRAY=25
DT_FINI_ARRAY=26
DT_INIT_ARRAYSZ=27
DT_FINI_ARRAYSZ=28
DT_RUNPATH=29
DT_FLAGS=30
DT_ENCODING=32
DT_PREINIT_ARRAY=32
DT_PREINIT_ARRAYSZ=33
DT_NUM=34
DT_LOOS=0x6000000d
DT_HIOS=0x6ffff000
DT_LOPROC=0x70000000
DT_HIPROC=0x7fffffff
#bin_type : EXEC|RTLD|LIB
bin_type = "";
#link_type : STATIC_LINKED|DYNAMIC_LINKED
link_type= -1;
elf_type = ET_NONE
got_plt_address = 0 # got.plt address

#configuration object
myconf = None
#default configurations
target_dir = "./target_elf"
config_file = "./config";
profile_file = "";
client_file = None;
gen_hash = 1;
use_local_hash =1;
use_trap_redirect4bundle=0
use_ret=0
use_far_jmp=0;
only_local_lookup=0;
config_modify_interpreter = 1
pic_change_stack=0;
ret_to_orig=0;
enforce_ret=0;
transparent_call=0;
debug_mode=0;
save_eflags=0;
enforce_e_cfi=0;
enforce_plt=0;
use_segv=0;
only_gen_asm=0
init_gs=0
def id_generator(size=32, chars=string.ascii_uppercase + string.digits):
	return ''.join(random.choice(chars) for x in range(size))


def get_new_segment_base_addr(binname):
	global elf_type;
	global eb
	if(elf_type == ET_EXEC):
		return 0x0a000000;
	elif(elf_type == ET_DYN):
		#FIXME: segment base should not be zero
		bss_addr = eb.get_section_info(binname, ".bss", "addr");
		print "bss_addr :%lx"%bss_addr
		bss_size = eb.get_section_info(binname, ".bss", "size");
		print "bss_size :%lx"%bss_size
		mytext_addr = ((bss_addr + bss_size ) & 0xfffff000) + 0x1000
		print "segment base address is %lx"%mytext_addr
		return mytext_addr;
	else:
		print "elf type unsupported, abort";
		exit(1);

def generate_hash_v2(binname, mytext_addr, output,local,pattern,datatype):
	mapping_size = 0
	insn_mapping = {}
	insn_array = []
	print "this is the hash table generation routine"
	print "hashtable type: %s %d"%(datatype, local);
	print "mytext address is %s"%mytext_addr
	mytext_addr = int(mytext_addr, 16)
	print "mytext address is %lx"%mytext_addr
	fd = os.open(output,os.O_CREAT|os.O_TRUNC|os.O_RDWR, 0644)
	os.write(fd, ".text\n")
	icf_file = "./icf_target_addr"
	plt_file = "./plt_target_addr"
	ret_file = "./ret_target_addr"
	first_insn = 0x7fffffff;
	last_insn = -1;
	old_addr = None;
	offset = None;
	new_addr = None;
	#we should accept both original address and modified address
	mypattern = re.compile(r"^([0-9a-fA-F]+)\s*$");
	mypattern_trans = re.compile(r"^translate_([0-9a-fA-F]+)\s*$");
	
	if(datatype == "plt"):
		icf_file = plt_file;
	elif(datatype == "return"):
		icf_file = ret_file
	else:
		icf_file = icf_file;

	try:
		fd_icf = open(icf_file, 'r');
	except IOError:
		print "file %s does not exist"%icf_file
		return 0
	#with fd_icf as file:
	for line in fd_icf.readlines():
		line = line.strip();
		m = mypattern.match(line);
		m1 = mypattern_trans.match(line);
		if( m != None):
			mapping_size +=1
			old_addr = m.group(1);
			offset = get_mapping_offset(old_addr)
			if(offset == None):
				print "warning: itarget invalid, old_addr1:%s"%old_addr;
				exit(1);
				continue;
			new_addr = int(offset,16) + mytext_addr
			old_addr = int(old_addr, 16);
			if(local == 1):
				old_addr = new_addr;
			insn_mapping[old_addr] = new_addr

		elif (m1 != None):
			mapping_size +=1
			old_addr = m1.group(1);
			offset = get_mapping_offset(old_addr)
			if(offset == None):
				print "warning: itarget invalid, old_addr:%s"%old_addr;
				exit(1);
				continue;
			new_addr = int(offset,16) + mytext_addr
			old_addr = new_addr;
			insn_mapping[old_addr] = new_addr
		if(m != None or m1 != None):
			if(first_insn > old_addr):
				#print "1st insn:%lx"%old_addr
				first_insn = old_addr
			if(last_insn < old_addr):
				#print "last insn:%lx"%old_addr
				last_insn = old_addr

	mapping_size  = len(insn_mapping)

			#else:
				#print "uncognized line:%s"%line
	#for key in insn_mapping.keys():
	#	print "0x%lx 0x%lx"%(key, insn_mapping[key]);

	#FIXME: this is hacking code, icf targets for instrumentation code need
	# an independent hash lookup, but now it is combined with the lookup of
	# target application code.
	aaa="""
	if((local == 1) and (datatype == "return")):
		instru_pattern = re.compile(r"__INSTRUMENT_RET_");
		cmd = "nm "+binname+" |sort -d -k1 "
		with os.popen(cmd) as file:
			for line in file:
				line = line.strip();
				m = instru_pattern.match(line);
				if( m != None):
					mapping_size +=1
					#old_addr = m.group('addr');
					#old_addr = int(old_addr, 16);
					offset = int(m.group('offset'),16)
					new_addr = offset + mytext_addr
					insn_mapping[new_addr] = new_addr
					if(first_insn > new_addr):
						#print "1st insn:%lx"%new_addr
						first_insn = new_addr
					if(last_insn < new_addr):
						#print "last insn:%lx"%new_addr
						last_insn = new_addr
"""
	

	if(last_insn == None):
		print "address of last insn is None, no hash table is generated.";
		return 0;
	print "address of 1st insn is:%lx"%first_insn;
	print "address of last insn is:%lx"%last_insn;
	
	if(local == 0):
		if(datatype == "normal"):
			global insn_begin ;
			global insn_end  ;
			insn_begin = first_insn;
			insn_end = last_insn;
		elif(datatype == "return"):
			global ret_insn_begin ;
			global ret_insn_end  ;
			ret_insn_begin = first_insn;
			ret_insn_end = last_insn;
		elif(datatype == "plt"):
			global plt_insn_begin ;
			global plt_insn_end  ;
			plt_insn_begin = first_insn;
			plt_insn_end = last_insn;

	else:
		if(datatype == "normal"):
			global local_insn_begin ;
			global local_insn_end ;
			local_insn_begin = first_insn;
			local_insn_end = last_insn;
		elif(datatype == "return"):	
			global ret_local_insn_begin ;
			global ret_local_insn_end  ;
			ret_local_insn_begin = first_insn;
			ret_local_insn_end = last_insn;
		elif(datatype == "plt"):	
			global plt_local_insn_begin ;
			global plt_local_insn_end  ;
			plt_local_insn_begin = first_insn;
			plt_local_insn_end = last_insn;


	print "mapping size is %d"%mapping_size;

	if(mapping_size == 0):
		return 0;
	hash_size_log = int(math.log(mapping_size, 2));
	hash_log = int(hash_size_log);
	hash_log_f = math.log(mapping_size,2);
	if(hash_log_f - hash_log >0.5):
		hash_log +=2;
	else:
		hash_log+=1;
	if(datatype == "plt"):
		hash_log+=1;
	insn_len = int(math.pow(2,hash_log))
	#global insn_mask
	_insn_mask = insn_len -1;
	insn_array = [[0,0] for i in xrange(0,insn_len)]
	#insn_array = [0,0] *insn_len
	print "hash table size: 2^%d"%(hash_log)
	collision = 0;
	total_collision = 0;
	longest_collision = 0;
	for key in insn_mapping.keys():
		idx =  key - first_insn;
		idx = idx % insn_len
		#print "0x%lx 0x%lx"%(key, insn_mapping[key]);
		#print "%d 0x%lx"%(idx, insn_mapping[key]);
		collision = 0;
		#if(insn_array[idx] != None):
		if(insn_array[idx][0] != 0):
			collision =1;
			successflag = 0;
			for i in xrange(1, insn_len):
				#idx = (idx +1)%insn_len;
				idx = (idx + i ) & _insn_mask 
				if(insn_array[idx][0] != 0):
					collision += 1;
					continue	
				else:
					insn_array[idx][0] = key
					insn_array[idx][1] = insn_mapping[key];
					#print "key is %d"%insn_array[idx][0]
					successflag = 1;
					#print "collision time is:%d"%collision
					#print "solve a collision, offset:%d"%i;
					total_collision += collision;
					if(collision>longest_collision):
						longest_collision = collision;
					break;
			if(successflag == 0):

				print "longest collision is:%d"%longest_collision
				print "too many collisions, abort";
				exit(1);
		else:
			insn_array[idx][0] = key
			insn_array[idx][1] = insn_mapping[key];
	if(local == 0):
		for idx in xrange(0, insn_len):
			string = ".long\t0x%lx\n.long\t0x%lx\n"%(insn_array[idx][0], insn_array[idx][1])
			os.write(fd,string);
	else:
		for idx in xrange(0, insn_len):
			string = ".long\t0x%lx\n"%(insn_array[idx][0])
			os.write(fd,string);
	if(datatype == "normal"):
		global insn_mask;
		insn_mask = _insn_mask;
	elif(datatype == "return"):
		global ret_insn_mask;
		ret_insn_mask = _insn_mask;
	elif(datatype == "plt"):
		global plt_insn_mask;
		plt_insn_mask = _insn_mask;


	os.close(fd);
	print "total collision time is:%d"%total_collision
	aveg_collision = float(total_collision)/float(mapping_size);
	print "average collision is:%f"%aveg_collision
	print "longest collision is:%d"%longest_collision 
	print "insn array len is %d"%insn_len
	print "insn mask is %lx"%_insn_mask
	print "\n";

	if(datatype == "plt"):
		global plt_longest_collision
		plt_longest_collsion = longest_collision

	return mapping_size


#local:0 generate hash for old->new mapping
#local:1 generate hash for new->new mapping. This one is a local hash
#return: the mapping size (# of hasthtable entries)
def generate_hash(binname, mytext_addr, output,local,pattern,datatype):
	mapping_size = 0
	insn_mapping = {}
	insn_array = []
	print "this is the hash table generation routine"
	print "mytext address is %s"%mytext_addr
	mytext_addr = int(mytext_addr, 16)
	print "mytext address is %lx"%mytext_addr
	fd = os.open(output,os.O_CREAT|os.O_TRUNC|os.O_RDWR, 0644)
	os.write(fd, ".text\n")
	cmd = "nm "+binname+" |sort -d -k1 "
	first_insn = -1;
	old_addr = None;
	offset = None;
	new_addr = None;
	with os.popen(cmd) as file:
		for line in file:
			line = line.strip();
			m = pattern.match(line);
			if( m != None):
				mapping_size +=1
				old_addr = m.group('addr');
				old_addr = int(old_addr, 16);
				offset = int(m.group('offset'),16)
				new_addr = offset + mytext_addr
				if(local == 1):
					old_addr = new_addr;
				insn_mapping[old_addr] = new_addr

				if(first_insn == -1):
					print "1st insn:%lx"%old_addr
					first_insn = old_addr
			#else:
				#print "uncognized line:%s"%line
	#for key in insn_mapping.keys():
	#	print "0x%lx 0x%lx"%(key, insn_mapping[key]);
	if(old_addr == None):
		print "address of last insn is None, no hash table is generated.";
		return 0;
	print "address of 1st insn is:%lx"%first_insn;
	print "address of last insn is:%lx"%old_addr;
	
	if(local == 0):
		if(datatype == "normal"):
			global insn_begin ;
			global insn_end  ;
			insn_begin = first_insn;
			insn_end = old_addr;
		elif(datatype == "return"):
			global ret_insn_begin ;
			global ret_insn_end  ;
			ret_insn_begin = first_insn;
			ret_insn_end = old_addr;
		elif(datatype == "plt"):
			global plt_insn_begin ;
			global plt_insn_end  ;
			plt_insn_begin = first_insn;
			plt_insn_end = last_insn;


	else:
		if(datatype == "normal"):
			global local_insn_begin ;
			global local_insn_end ;
			local_insn_begin = first_insn;
			local_insn_end = old_addr;
		elif(datatype == "return"):	
			global ret_local_insn_begin ;
			global ret_local_insn_end  ;
			ret_local_insn_begin = first_insn;
			ret_local_insn_end = old_addr;
		elif(datatype == "plt"):	
			global plt_local_insn_begin ;
			global plt_local_insn_end  ;
			plt_local_insn_begin = first_insn;
			plt_local_insn_end = last_insn;


	print "mapping size is %d"%mapping_size;
	if(mapping_size == 0):
		return 0;

	hash_size_log = int(math.log(mapping_size, 2));
	hash_log = int(hash_size_log);
	hash_log_f = math.log(mapping_size,2);
	if(hash_log_f - hash_log >0.5):
		hash_log +=2;
	else:
		hash_log+=1;
	insn_len = int(math.pow(2,hash_log))
	#global insn_mask
	_insn_mask = insn_len -1;
	insn_array = [[0,0] for i in xrange(0,insn_len)]
	#insn_array = [0,0] *insn_len
	print "hash table size: 2^%d\n"%(hash_log)
	collision = 0;
	total_collision = 0;
	longest_collision = 0;
	for key in insn_mapping.keys():
		idx =  key - first_insn;
		idx = idx % insn_len
		#print "0x%lx 0x%lx"%(key, insn_mapping[key]);
		#print "%d 0x%lx"%(idx, insn_mapping[key]);
		collision = 0;
		if(insn_array[idx][0] != 0):
			collision =1;
			successflag = 0;
			for i in xrange(1, insn_len):
				#idx = (idx +1)%insn_len;
				idx = (idx + i ) & _insn_mask 
				if(insn_array[idx][0] != 0):
					collision += 1;
					continue	
				else:
					insn_array[idx][0] = key
					insn_array[idx][1] = insn_mapping[key];
					#print "key is %d"%insn_array[idx][0]
					successflag = 1;
					#print "collision time is:%d"%collision
					#print "solve a collision, offset:%d"%i;
					total_collision += collision;
					if(collision>longest_collision):
						longest_collision = collision;
					break;
			if(successflag == 0):

				print "longest collision is:%d"%longest_collision
				print "too many collisions, abort";
				exit(1);
		else:
			insn_array[idx][0] = key
			insn_array[idx][1] = insn_mapping[key];
	if(local == 0):
		for idx in xrange(0, insn_len):
			string = ".long\t0x%lx\n.long\t0x%lx\n"%(insn_array[idx][0], insn_array[idx][1])
			os.write(fd,string);
	else:
		for idx in xrange(0, insn_len):
			string = ".long\t0x%lx\n"%(insn_array[idx][0])
			os.write(fd,string);
	if(datatype == "normal"):
		global insn_mask;
		insn_mask = _insn_mask;
	elif(datatype == "return"):
		global ret_insn_mask;
		ret_insn_mask = _insn_mask;
	elif(datatype == "plt"):
		global plt_insn_mask;
		plt_insn_mask = _insn_mask;

	os.close(fd);
	print "total collision time is:%d"%total_collision
	aveg_collision = float(total_collision)/float(mapping_size);
	print "average collision is:%f"%aveg_collision
	print "longest collision is:%d"%longest_collision
	print "insn array len is %d"%insn_len
	print "insn mask is %lx"%_insn_mask
	return mapping_size

def generate_mapping(binname, mytext_addr,output):
	global mapping_size
	print "mytext address is %s"%mytext_addr
	mytext_addr = int(mytext_addr, 16)
	print "mytext address is %lx"%mytext_addr
	fd = os.open(output,os.O_CREAT|os.O_TRUNC|os.O_RDWR, 0644)
	os.write(fd, ".text\n")
	pattern = re.compile(r"^(?P<offset>[0-9a-fA-F]{1,8})\s+"
				"(?P<type>[^\s]+)\s\_"
				"(?P<addr>[0-9a-fA-F]+)\s*$")
	if(generate_mapping.initialized == False):
		cmd = "nm "+binname
		fd_nm = os.popen(cmd);
		generate_mapping.initialized = True;
	os.lseek(fd_nm, 0, os.SEEK_SET);
	with fd_nm as file:
		for line in file:
			line = line.strip();
			m = pattern.match(line);
			if(m != None):
				#print line;
				mapping_size = mapping_size + 1
				old_addr = m.group('addr');
				string = ".long\t0x"+old_addr+"\n"
				os.write(fd, string)
				offset = int(m.group('offset'),16)
				new_addr = offset + mytext_addr
				new_addr = "%lx"%new_addr
				string = ".long\t0x"+new_addr+"\n"
				os.write(fd,string)	


#.bss need special consideration in offset ==>vma
def convert_offset_to_vma(binname, offset):
	offset = int(offset, 16)
	global eb
	num = eb.get_elfhdr_info(binname, "Number of section headers:")
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
				offset_start = int(m.group('offset'),16)
				size = int(m.group('size'),16)
				if(m.group('name') == '.bss'):
					if(offset == offset_start):
						return int(m.group('addr'),16) 
					else:
						continue

				if(((offset_start+size) <= offset) or (offset < offset_start)):
					continue
				else:
					vma_start = int(m.group('addr'), 16)
					vma = vma_start + (offset - offset_start)
					return vma 
	return 0;

def convert_vma_to_offset(binname, vma):
	vma = int(vma, 16)
	global eb
	num = eb.get_elfhdr_info(binname, "Number of section headers:")
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


a = """
	get_mapping_offset.file_nm.seek(0);
	for line in get_mapping_offset.file_nm:
		line = line.strip()
		m = p.match(line);
		if(m != None):
			#print "in get_mapping_offset, address is %s"%address
			addr_reloc = int(m.group(3), 16);
			if(addr == addr_reloc):
				return m.group(1);
	return None		
"""
"""
08049a30 <.text>:
 8049a30:       31 ed                   xor    %ebp,%ebp
 8049a32:       5e                      pop    %esi
 8049a33:       89 e1                   mov    %esp,%ecx
 8049a35:       83 e4 f0                and    $0xfffffff0,%esp
 8049a38:       50                      push   %eax
 8049a39:       54                      push   %esp
 8049a3a:       52                      push   %edx
 8049a3b:       68 a0 a1 05 08          push   $0x805a1a0
 8049a40:       68 40 a1 05 08          push   $0x805a140
 8049a45:       51                      push   %ecx
 8049a46:       56                      push   %esi
 8049a47:       68 90 f9 04 08          push   $0x804f990  /*** address of main ***/
 8049a4c:       e8 2f fb ff ff          call   8049580 <__libc_start_main@plt>
"""	
def get_main_from_start(binpath, offset_start):
	#from the above code, we can see that the address of start is pushed as a parameter
	#so we can simple modify this value to the new address of main
	#this value is 0x18 bytes from the beginning of _start
	magic_place = offset_start + 0x18
	fd = os.open(binpath, os.O_RDWR);
	os.lseek(fd, magic_place, os.SEEK_SET)
	addr_main = os.read(fd,4);
	addr_main = unpack("<i", addr_main)
	print "magic place is %lx"%magic_place
	print "address of main is %x"%addr_main
	os.close(fd);
	return addr_main
#__libc_csu_fini
def get_libc_csu_fini_from_start(binpath, offset_start):
	#from the above code, we can see that the address of start is pushed as a parameter
	#so we can simple modify this value to the new address of __libc_csu_fini
	#this value is 0x0d bytes from the beginning of _start
	magic_place = offset_start + 0x0c
	fd = os.open(binpath, os.O_RDWR);
	os.lseek(fd, magic_place, os.SEEK_SET)
	addr = os.read(fd,4);
	addr = unpack("<i", addr)
	print "magic place is %lx"%magic_place
	print "address of __libc_csu_fini is %x"%addr
	os.close(fd);
	return addr

#__libc_csu_init
def get_libc_csu_init_from_start(binpath, offset_start):
	#from the above code, we can see that the address of start is pushed as a parameter
	#so we can simple modify this value to the new address of __libc_csu_init
	#this value is 0x12 bytes from the beginning of _start
	magic_place = offset_start + 0x11
	fd = os.open(binpath, os.O_RDWR);
	os.lseek(fd, magic_place, os.SEEK_SET)
	addr = os.read(fd,4);
	addr = unpack("<i", addr)
	print "magic place is %lx"%magic_place
	print "address of __libc_csu_init is %x"%addr
	os.close(fd);
	return addr

# This function returns the offset of main function in the generated code
def get_main_offset(binpath, offset_entry):
	return offset_entry+0x18	

def get_libc_csu_fini_offset(binpath, offset_entry):
	return offset_entry+0x0c	

def get_libc_csu_init_offset(binpath, offset_entry):
	return offset_entry+0x11	

def modify_phdr_info(binpath, phdr_name, attribute, value):
	pass



#patch all relocations in .mytext
def patch_mytext(binname):
	global mapping_size;
	global mytext_base;
	global elf_type;
	global bin_type;
	global eb
	fd = os.open(binname, os.O_RDWR)
	base = eb.get_section_info(binname,".mytext",'offset')
	hash_base = eb.get_section_info(binname,".func_orig",'addr')
	local_hash_base = eb.get_section_info(binname,".func_local",'addr')
	ret_hash_base =eb.get_section_info(binname,".ret_orig",'addr')
	ret_local_hash_base = eb.get_section_info(binname,".ret_local",'addr')
	plt_hash_base = eb.get_section_info(binname, ".plt_data", 'addr')

	pattern = re.compile(r"^(?P<offset>[0-9a-fA-F]{1,8})\s+"
				"(?P<info>[0-9a-fA-F]{1,8})\s+"	
				"(?P<type>[^\s]+)\s+"
				"(?P<symvalue>[0-9a-fA-F]{1,8})\s+"
				"(?P<name>[^\n]+)$")
	#pic code relocation
	pic_pa_got = re.compile(r"pic_([0-9a-fA-F]+)$");
	pic_pa_addr = re.compile(r"pic_(?P<addr>[0-9a-f]+)_(?P<offset>[0-9a-f]+)$");

	#plt code relocation
	plt_reloc = re.compile(r"value_in_0x([0-9a-fA-F]+)$");
	plt_reloc_pic = re.compile(r"value_in_gotplus_([0-9a-fA-F]+)$");

	#relocation for tranparent call
	ret_addr_reloc = re.compile(r"offset_([0-9a-fA-F]+)$");
	#print "base:%x"%base
	#relocation that need translated address value
	trans_reloc = re.compile(r"trans_([0-9a-f]+)$");		
	cmd = "readelf -W -r generated_asm.o"
	with os.popen(cmd) as file:
		for line in file:
			line = line.strip()
			m = pattern.match(line)
			#print line
			if(m != None):
				print line	
				if(pic_pa_got.match(m.group('name')) != None):
					global mytext_base	
					_pic = pic_pa_got.match(m.group('name'));
					off = _pic.group(1);
					off = get_mapping_offset(off);
					off = int (off, 16);
					got_addr = eb.read_dynamic_option(binname, DT_PLTGOT);
					#print "got.plt address is %lx"%got_addr
					#got_addr = get_section_info(binname,".got.plt","addr");
					value = -(mytext_base + off - got_addr)
					os.lseek(fd, base + int(m.group('offset'),16), os.SEEK_SET);
					os.write(fd, pack('<i', value));
				elif( pic_pa_addr.match(m.group('name')) != None):
					#global mytext_base	
					_pic = pic_pa_addr.match(m.group('name'));
					off = _pic.group('offset');
					off = get_mapping_offset(off);
					off = int (off, 16);
					orig_addr = int(_pic.group('addr'),16);
					value = -(mytext_base + off - orig_addr)
					os.lseek(fd, base + int(m.group('offset'),16), os.SEEK_SET);
					os.write(fd, pack('<i', value));
				elif( ret_addr_reloc.match(m.group('name')) != None):
					#global mytext_base
					_ret = ret_addr_reloc.match(m.group('name'));
					orig_addr = _ret.group(1);
					offset = get_mapping_offset(orig_addr);
					orig_addr = int(orig_addr,16);
					if(offset == None):
						print "address %x does not exist"%orig_addr
						exit(1);
					value = mytext_base + int(offset,16) - orig_addr;
					os.lseek(fd, base + int(m.group('offset'),16), os.SEEK_SET);
					os.write(fd, pack('<i', value));
	
				elif( plt_reloc.match(m.group('name')) != None):
					_loc = plt_reloc.match(m.group('name'));
					print "match value_in_0x%s"%_loc.group(1);
					addr = _loc.group(1);
					#global eb
					offset = eb.convert_vma_to_offset(binname, addr);
					fd_plt = os.open(binname, os.O_RDWR);
					os.lseek(fd_plt, offset, os.SEEK_SET);
					value = unpack('<i',os.read(fd_plt,4))[0];
					patch_loc=m.group('offset');
					patch_loc=int(patch_loc,16)+base;
					os.lseek(fd_plt,patch_loc , os.SEEK_SET);
					os.write(fd_plt, pack("<i", value));
					os.close(fd_plt);
				elif( plt_reloc_pic.match(m.group('name')) != None):
					_loc = plt_reloc_pic.match(m.group('name'));
					print "match value_in_gotplus_%s"%_loc.group(1);
					addr_str = _loc.group(1);
					addr = int(addr_str,16) + eb.read_dynamic_option(binname, DT_PLTGOT);
					addr_str = "%x"%addr;
					#global eb
					offset = eb.convert_vma_to_offset(binname, addr_str);
					fd_plt = os.open(binname, os.O_RDWR);
					os.lseek(fd_plt, offset, os.SEEK_SET);
					value = unpack('<I',os.read(fd_plt,4))[0];
					#we only use the last byte to guess whether is symbol is resolved or not
					#in dump2asm.pl, the relocation we need to patch is set to 1 byte long
					#so, here, only 1 unsigned char need to be written.
					value = value & 0x000000ff;
					patch_loc=m.group('offset');
					patch_loc=int(patch_loc,16)+base;
					os.lseek(fd_plt,patch_loc , os.SEEK_SET);
					os.write(fd_plt, pack('<B', value));
					#os.lseek(fd_plt,-2, os.SEEK_CUR);
					#null_insn = 0x9066;
					#os.write(fd_plt, pack('<H',null_insn));
					os.close(fd_plt);
				
				elif(trans_reloc.match(m.group('name')) != None):
					_trans = trans_reloc.match(m.group('name'));
					old_addr = _trans.group(1);
					new_offset = get_mapping_offset(old_addr);
					new_addr = 0;
					if(new_offset !=None):
						new_addr = mytext_base + int(new_offset, 16);
						print "translating adddress: %s ==> %x"%(old_addr, new_addr)
					else:
						print "warning: there is non-existent icf target in speculation info";
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i',new_addr))

				elif( m.group('name') == 'array'):
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i',hash_base))
				elif( m.group('name') == 'array_4'):
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					offset_4_hash_base = hash_base+4;
					os.write(fd, pack('<i',offset_4_hash_base))
				elif( m.group('name') == 'ret_array'):
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i',ret_hash_base))
				elif( m.group('name') == 'ret_array_4'):
					offset = base + int(m.group('offset'),16)
					offset_4_ret_hash_base = ret_hash_base+4;
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i',offset_4_ret_hash_base))
				elif( m.group('name') == 'local_array'):
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					print "value of local_hash_base:%lx"%local_hash_base
					os.write(fd, pack('<i',local_hash_base))
				elif( m.group('name') == 'local_array_4'):
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					offset_4 = local_hash_base+4;
					os.write(fd, pack('<i',offset_4))
				elif( m.group('name') == 'plt_array'):
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i',plt_hash_base))
				elif( m.group('name') == 'plt_array_4'):
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					offset_4_hash_base = plt_hash_base+4;
					os.write(fd, pack('<i',offset_4_hash_base))
				elif( m.group('name') == 'ret_local_array'):
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					print "value of local_hash_base:%lx"%ret_local_hash_base
					os.write(fd, pack('<i',ret_local_hash_base))
				elif( m.group('name') == 'ret_local_array_4'):
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					offset_4 = ret_local_hash_base+4;
					os.write(fd, pack('<i',offset_4))
				elif(m.group('name') == 'size'):
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', mapping_size))	
				elif(m.group('name') == 'ret_size'):
					global ret_mapping_size
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', ret_mapping_size))	
				elif(m.group('name') == 'plt_size'):
					global plt_longest_collision
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', plt_longest_collision))	
				elif(m.group('name') == 'local_insn_end'):
					global local_insn_end;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', local_insn_end))
				elif(m.group('name') == 'ret_local_insn_end'):
					global ret_local_insn_end;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', ret_local_insn_end))
				elif(m.group('name') == 'local_insn_begin'):
					global local_insn_begin;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', local_insn_begin))
				elif(m.group('name') == 'ret_local_insn_begin'):
					global ret_local_insn_begin;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', ret_local_insn_begin))
				elif(m.group('name') == 'insn_begin'):
					global insn_begin;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', insn_begin))
					#os.write(fd, pack('<i', 0x8048000))
					#elf_base = eb.get_elfhdr_info(binname,"Start of program headers:");
					#elf_base = elf_base - 0x34;
					#os.write(fd, pack('<i', elf_base))
				elif(m.group('name') == 'ret_insn_begin'):
					global ret_insn_begin;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', ret_insn_begin))
				elif(m.group('name') == 'plt_insn_begin'):
					global plt_insn_begin;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', plt_insn_begin))
				elif(m.group('name') == 'plt_insn_end'):
					global plt_insn_end;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', plt_insn_end))
				elif(m.group('name') == 'insn_end'):
					global insn_end;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', insn_end))
				elif(m.group('name') == 'ret_insn_end'):
					global ret_insn_end;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', ret_insn_end))
				elif(m.group('name') == 'insn_mask'):
					global insn_mask;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', insn_mask))
				elif(m.group('name') == 'ret_insn_mask'):
					global ret_insn_mask;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', ret_insn_mask))
				elif(m.group('name') == 'plt_insn_mask'):
					global plt_insn_mask;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', plt_insn_mask))
				elif(m.group('name') == 'elf_type'):
					global elf_type;
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<b', elf_type))
				elif(m.group('name') == 'module_name_begin'):
					global global_binname
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					ss = global_binname[:64]
					os.write(fd, ss)
				elif(m.group('name') == 'bip_options_begin'):
					global myconf
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					myconf.write_options(fd)
					print "hello"
				elif(m.group('name') == '__REAL_INIT_FUNC'):
					print "found REAL_INIT_FUNC";
					offset = base + int(m.group('offset'),16)
					address = mytext_base + int(m.group('offset'),16)
					modify_init_address(binname,offset,address);
				elif(m.group('name') == 'orig_entrypoint'):
					#global eb;
					entrypoint = eb.get_elfhdr_info(binname,"Entry point address:")
					entrypoint = int(entrypoint, 16)
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					os.write(fd, pack('<i', entrypoint))

				elif(m.group('name') == '.text'):
					#global mytext_base	
					offset = base + int(m.group('offset'),16)
					os.lseek(fd, offset, os.SEEK_SET)
					value = unpack('<i',os.read(fd,4))[0];
					print ".text relocation, value:%lx"%value
					value += mytext_base
					os.lseek(fd, -4, os.SEEK_CUR);
					os.write(fd, pack('<i', value))
					print "patch .text relocation with value:%lx"%value
				elif(m.group('name') == 'global_lookup'):
					cmd = 'readelf --dyn-syms /lib/ibc.so.6 |sed \' s/\s+/\s/g\'|awk  \'{print $2 "\t" $8}\''
					p = re.compile(r"([\S]+)\s+([\S]+)$");
					found=0;
					with os.popen(cmd) as file:
						for line in file:
							_m = p.match(line);
							if(_m!=None):
								if(_m.group(2).strip() == "global_lookup"):
									found =1;
									lookup_offset = int(_m.group(1),16);
									offset = base + int(m.group('offset'),16)
									os.lseek(fd, offset, os.SEEK_SET)
									os.write(fd, pack('<i',lookup_offset))
					if(found == 0):
						print "Did not find location of global_lookup, abort!";
						#exit(1);
				else:
					print "error in patching mytext"
					print "relocation name:%s unrecognized"%m.group('name')
					#exit();

	os.close(fd);


def get_generated_symbol_address(binname, sym_name):
	global mytext_base
	symbol_pa = re.compile(r"(?P<offset>[\S]+)\s+(?P<type>[\S]+)\s+(?P<name>[\S]+)\s*$");
	cmd = "nm generated_asm.o"
	with os.popen(cmd) as file:
		for line in file:
			line = line.strip()
			_m = symbol_pa.match(line)	
			if( _m == None):
				continue;

			if(_m.group('name') == sym_name):
				return mytext_base + int(_m.group('offset'), 16);
	return None;

def intercept_init_function(binname, new_init_addr):
	global eb
	preinit_array = eb.read_dynamic_option(binname, DT_PREINIT_ARRAY);
	if(preinit_array != None):
	#not implemented yet
		return None;
	init_array = eb.read_dynamic_option(binname, DT_INIT_ARRAY);
	if(init_array != None):
		init_offset = eb.get_section_info(binname,".init_array","offset");
		fd = os.open(binname, os.O_RDWR);
		os.lseek(fd, init_offset, os.SEEK_SET);
		init_addr = unpack('<i',os.read(fd,4))[0];
		os.lseek(fd, -4, os.SEEK_CUR);
		os.write(fd, pack("<i", new_init_addr));
		os.close(fd);
		return init_addr;

	init_addr = eb.read_dynamic_option(binname, DT_INIT);
	if(init_addr == None):
		return None;
	init_addr_str = "%x"%init_addr;
	print "old init_addr is %s"%init_addr_str
	#new_init_offset = get_mapping_offset(init_addr_str);
	#new_init_addr = mytext_base + int(new_init_offset,16);
	print "new init_addr is %x"%new_init_addr
	eb.update_dynamic_option(binname, DT_INIT, new_init_addr);
	return init_addr

def modify_init_address(binname,where_to_patch, memory_location):
	global mytext_base;

	#STEP 1: figure out the address of __my_trap_redirector
	my_trap_addr = get_generated_symbol_address(binname, '__my_trap_redirector');
	print "my trap address is: 0x%x"%my_trap_addr;
	if(my_trap_addr == None):
		print "did not find the address of my_trap_redirector, abort";
		exit(1);
	#STEP 2: figure out which function to intercept and intercept it
	orig_addr = intercept_init_function(binname, my_trap_addr);	
	if(orig_addr == None):
		print "did not find the address of an initialization function to intercept";
		if((bin_type == "RTLD") and (elf_type == ET_DYN)):
		#check if it is ld.so
			return;
		else:
			exit(1);
	#STEP 3: patch the tail jmp target with the original init function
	fd = os.open(binname, os.O_RDWR);
	os.lseek(fd, where_to_patch, os.SEEK_SET);
	orig_offset = unpack('<i',os.read(fd,4))[0];
	new_offset = orig_addr - memory_location + orig_offset;
	print "orig address: %lx"%orig_addr
	print "patch address: %lx"%where_to_patch
	print "orig offset: %lx"%orig_offset
	print "new offset: %lx"%new_offset

	os.lseek(fd, -4, os.SEEK_CUR);
	os.write(fd, pack("<i",new_offset));
	print "patching the tail jmp to target the original function";

def modify_entry_point(orig_bin, binname):
	#modify the entry point
	global eb
	entry_addr = eb.get_elfhdr_info(orig_bin, "Entry point address:")
	entry_offset = get_mapping_offset(entry_addr);
	if(entry_offset == None):
		print "there is no entry point in translated segment";
		return;
	entry_addr = int(entry_addr, 16);
	entry_offset = int(entry_offset, 16);


	global start_of_mytext
	if(start_of_mytext != None):
		new_entry_addr = entry_offset + start_of_mytext
		print "start of mytext is %lx"%start_of_mytext
		print "new entry point addr is %lx"%new_entry_addr
	else:
		print "start of mytext is None, abort!"
		return
	print "entry point offset is %lx"%entry_offset
	eb.modify_elfhdr_info(binname, "entrypoint", new_entry_addr)
def load_config(config_file):
	if(config_file == None):
		config_file = './config'
	pattern = re.compile("^([\S]+)\s*=\s*([\S]+)$");
	comment = re.compile("^\s*#[^\n]*$");
	global gen_hash;
	global use_local_hash;
	global myconf;	
	bip_opt = dict();


	#assume config file is at the same directory
	with open(config_file) as file:
		for line in file:
			line = line.strip();
			m = comment.match(line);
			if( m != None):
				continue;
			m = pattern.match(line);
			if(m != None):
				opt = m.group(1);
				val = m.group(2);
				bip_opt[opt] = val;

				if(opt == "use_local_hash"):
					use_local_hash = int(val,10);
				elif(opt == "gen_hash"):
					gen_hash = int(val,10);
				elif(opt == "return2lookup_use_ret"):
					global use_ret
					use_ret = int(val,10);
				elif(opt == "use_far_jmp"):
					global use_far_jmp
					use_far_jmp = int(val,10);
				elif(opt == "only_local_lookup"):
					global only_local_lookup
					only_local_lookup = int(val,10);
				elif(opt == "pic_change_stack"):
					global pic_change_stack;
					pic_change_stack=int(val,10);
				elif(opt == "ret_to_orig"):
					global ret_to_orig;
					ret_to_orig = int(val,10);
				elif(opt == "enforce_ret"):
					global enforce_ret;
					enforce_ret = int(val,10);
				elif(opt == "transparent_call"):
					global transparent_call;
					transparent_call = int(val,10);	
				elif(opt == "debug_mode"):
					global debug_mode;
					debug_mode = int(val,10);
				elif(opt == "save_eflags"):
					global save_eflags;
					save_eflags = int(val,10);
				elif(opt == "enforce_e_cfi"):
					global enforce_e_cfi;
					enforce_e_cfi = int(val,10);
				elif(opt == "enforce_plt"):
					global enforce_plt;
					enforce_plt = int(val,10);
				elif(opt == "use_segv"):
					global use_segv;
					use_segv = int(val,10);
				elif(opt == "init_gs"):
					global init_gs;
					init_gs = int(val,10);

				elif(opt == "only_gen_asm"):
					global only_gen_asm;
					only_gen_asm = int(val,10);

				else:
					print "unrecognized option:%s"%opt;
	
	myconf = bip_config("bip_options",bip_opt);

def append_transparent_callstubs(servicefile):
	global transparent_call;
	if(transparent_call ==0):
		return;

	cmd = "gcc -E ./transparent_callstubs.S |sed 's/;/\\n/g' >>"+servicefile
	os.system(cmd);


def append_myrodata(servicefile):
	global elf_type
	if(elf_type == ET_EXEC):
		cmd = "cat ./myrodata.s >>"+servicefile
		os.system(cmd);

def append_trap_redirect(servicefile):
	global elf_type
	cmd = "cat ./sigaction.S >>"+servicefile
	os.system(cmd)
	if(elf_type == ET_EXEC):
		cmd = "cat ./trap_redirect_service.s >>"+servicefile
	elif(elf_type == ET_DYN):
		#if(bin_type == "RTLD"):
		#	cmd = "cat ./trap_redirect_ld_so.s >>"+servicefile
		#else:
		cmd = "cat ./trap_redirect_pic.s >>"+servicefile
	else:
		print "elf type unsupported, abort";
		exit(1);
	os.system(cmd);

	if(use_trap_redirect4bundle==1):
		cmd ="cat ./trap4bundle.s>>"+servicefile
		os.system(cmd);
	else:
		if(elf_type == ET_EXEC):
			cmd ="cat ./trap_normal.s>>"+servicefile
	
		elif(elf_type == ET_DYN):
			cmd ="cat ./trap_normal_pic.s>>"+servicefile	
		else:
			print "elf type unsupported, abort";
			exit(1);
		os.system(cmd);

	cmd = "cat ./alloc_page.s >>"+servicefile;
	os.system(cmd);

	return servicefile
def append_signature(servicefile):
	cmd = 'cat ./signature.s >>'+servicefile
	os.system(cmd);

	#the following is old version
	#now module name is written using relocation

	#cmd = 'echo "module_name:">>'+servicefile
	#os.system(cmd);
	#global global_binname
	#str_name = global_binname[:128];
	#cmd = 'echo ".string \\\"'+str_name +'\\\"">>'+servicefile
	#os.system(cmd);

	if(use_far_jmp == 1):
		cmd = 'echo "use_far_jmp:">>'+servicefile
		os.system(cmd);
	if(only_local_lookup==1):
		cmd = 'echo "only_local_lookup:">>'+servicefile
		os.system(cmd);
	if(bin_type == "LIB"):
		cmd = 'echo "code_is_shared_library:">>'+servicefile
		os.system(cmd);
	if(ret_to_orig == 1):
		cmd = 'echo "ret_to_orig:">>'+servicefile
		os.system(cmd);
	if(use_ret == 1):
		cmd = 'echo "use_ret:" >>'+servicefile;
		print "cmd:%s"%cmd
		os.system(cmd);
	if(save_eflags ==1):
		cmd = 'echo "enforce_save_eflags:">>'+servicefile;
		os.system(cmd);
	if(elf_type == ET_DYN):
		cmd = 'echo "is_pic:">>'+servicefile;
		os.system(cmd);
	if(link_type == STATIC_LINKED):
		cmd = 'echo "init_gs:">>'+servicefile
		os.system(cmd);
	if(init_gs == 1):
		cmd = 'echo "init_gs:">>'+servicefile
		os.system(cmd);
	if(bin_type == "RTLD"):
		cmd = 'echo "transparent_entry:">>'+servicefile
		os.system(cmd);
		cmd = 'echo "init_gs:">>'+servicefile
		os.system(cmd);

	#testing code here
	if(use_segv == 1):
		cmd = 'echo "#define USE_SIGSEGV">>'+servicefile
		os.system(cmd)
	else:
		cmd = 'echo "#undef USE_SIGSEGV">>'+servicefile
		os.system(cmd)

	#testing code end
	cmd = 'echo ".p2align 9">>'+servicefile
	os.system(cmd);
	

def recognize_binary_type(binname):
	global bin_type
	global link_type
	setup_elf_type(binname, "Type:");
	if(elf_type == ET_EXEC):
		bin_type = "EXEC";
	elif(elf_type == ET_DYN):
		p = re.compile(r"^\(SONAME\)\s*\[(?P<soname>[\S]+)\]$")
		cmd = "readelf -d "+binname+"| awk '{print $2 \" \" $5}' ";
		bin_type = "EXEC";
		#PIE code does not have SONAME entry in dynamic section
		#ld.so has SONAME entry, but should be regarded as an executable
		with os.popen(cmd) as file:
			for line in file:
				line = line.strip();
				m = p.match(line);
				if(m != None):
					print "library name (SONAME): %s"%m.group('soname');
					if(check_if_ld_so(m.group('soname')) == 1):
						print "this is the dynamic linker (ld.so)"
						bin_type = "RTLD";
					else:
						bin_type = "LIB";
	else:
		print "uncognized elf file type";
		return;
	print "the binary file type is: %s"%bin_type;
	global eb
	if(eb.get_section_info(binname,'.dynamic','addr') == None):
		link_type = STATIC_LINKED;
	else:
		link_type = DYNAMIC_LINKED;	
	
def check_if_ld_so(soname):
	p1 = re.compile(r"^ld-linux\.so\.[0-9]$")
	p2 = re.compile(r"^linux-ld\.so\.[0-9]$")
	m1 = p1.match(soname);
	m2 = p2.match(soname);
	if((m1 != None) or(m2 != None)):
		return 1;
	else:
		return 0;

def construct_service_file(servicefile):
	new_file="./service.s"
	append_signature(servicefile);
	append_icf_search(servicefile);
	append_trap_redirect(servicefile);
	cmd = "gcc -E "+servicefile+" |sed 's/;/\\n/g' >"+new_file
	os.system(cmd)
	#cmd = "mov "+servicefile+" "+servicefile+".orig"
	return new_file

def attach_reference_monitor(orig_bin):
	#randstr = id_generator();
	#servicefile = "/tmp/"+randstr+'.S';
	#cmd = 'rm '+servicefile + '; touch '+servicefile
	#os.system(cmd);	
	servicefile = "./service.S"

	servicefile = construct_service_file(servicefile)
	#append_signature(servicefile);
	#append_icf_search(servicefile);
	#append_trap_redirect(servicefile);

	cmd = "cat generated_asm.s>>"+servicefile;
	os.system(cmd);
	cmd = "cat "+servicefile+">generated_asm.s";
	os.system(cmd);
	append_transparent_callstubs("generated_asm.s");
	#any code should be added before myrodata
	append_myrodata("generated_asm.s");

def setup_elf_type (binname, attribute):
	global elf_type;
	global eb
	elf_type_str = eb.get_elfhdr_info(binname, attribute);
	if(elf_type_str == "DYN"):
		elf_type = ET_DYN;
		print "this is a shared library or a PIE executable";
	elif(elf_type_str == "EXEC"):
		elf_type = ET_EXEC;
		print "this is a normal elf executable";
	else:
		print "the elf file type is not supported yet, abort";
		exit(1);


def main():
	global eb;
	global config_file;
	global client_file;
	global profile_file;
	eb = elf_basic();

	parser = argparse.ArgumentParser()
	parser.add_argument('binfile', nargs='?')
	parser.add_argument('asmfile', nargs='?')
	parser.add_argument('-c', '--config',  nargs='?' ,const='./config', default='./config');
	parser.add_argument('-t', '--client',  nargs='?', default=None);
	parser.add_argument('-p', '--profile',  nargs='?', default=None);
	args = parser.parse_args();

	orig_path = args.binfile;
	asm_path = args.asmfile;
	config_file = args.config;
	client_file = args.client;
	profile_file = args.profile;
	#orig_path = sys.argv[1];
	#arglen = len(sys.argv);
	#initialize all global objects here
	#if(client_file != None):
		#args = sys.argv;
		#idx_dslash = args.index('--') if '--' in args else len(args)
		#print "client with arguments is not supported yet";
	#loading config
	load_config(config_file);

	#get binary type: EXEC/LIB
	#get elf type: EXEC/DYN
	recognize_binary_type(orig_path);
	
	if(asm_path != None):
		lift_main(orig_path, asm_path)
	else:
		test_main(orig_path)

def lift_main(orig_path,asm):
	orig_bin = os.path.basename(orig_path);
	cmd = "mkdir -p "+orig_bin
	os.system(cmd)

	cmd = "cp "+orig_path+ ' ./' + orig_bin + '/' + orig_bin;
	os.system(cmd)

	modified_bin_1 = "./" + orig_bin + "_modified_1"
	modified_bin_2 = "./" + orig_bin + "_modified_2"
	binname = "./"+orig_bin + "_final"

	cmd="./asm2asm.pl "+ asm +" "+orig_path
	os.system(cmd)
	cmd="mv generated_asm.s "+orig_bin
	os.system(cmd)
	os.chdir("./"+orig_bin);
	
	attach_reference_monitor(orig_bin);

	cmd3 = "gcc -c generated_asm.s"
	os.system(cmd3);
	
	eb.extract_data("./generated_asm.o",".text","./generated_input")
	cmd = "objcopy --add-section .mytext=generated_input "+orig_bin + " " + modified_bin_1
	os.system(cmd); 

	#generating instruction mapping
	#global eb
	mytext_start = eb.get_section_info(modified_bin_1,".mytext","offset");
	print "mytext_start is %lx"%mytext_start
	segment_base = get_new_segment_base_addr(modified_bin_1);
	mytext_addr = segment_base + (mytext_start & 0x00000fff)
	print "mytext_addr is %lx"%mytext_addr
	mytext_addr = "%lx"%mytext_addr
	#generate_mapping("./generated_asm.o",mytext_addr,"./mapping.s");
	generate_insn_mapping("./generated_asm.o",mytext_addr,"mapping.s");
	cmd = "gcc -c mapping.s"
	os.system(cmd)
	
	eb.extract_data("./mapping.o",".text","./mapping_input")
	cmd = "objcopy --add-section .func_orig=mapping_input "+modified_bin_1 + " " + modified_bin_2
	os.system(cmd)
	eb.modify_section_info(modified_bin_2,".func_orig","align",0x00001000)
	cmd = "objcopy " + modified_bin_2 + " " + binname;
	os.system(cmd)


	modify_orig_elf(binname);

	modify_entry_point(orig_bin, binname);
	

	
	#update_callback_func(orig_bin, binname, get_main_from_start, get_main_offset);
	#update_callback_func(orig_bin, binname, get_libc_csu_init_from_start, get_libc_csu_init_offset);
	#update_callback_func(orig_bin, binname, get_libc_csu_fini_from_start, get_libc_csu_fini_offset);

def special_handling_ld_so(binname):
	if(bin_type != "RTLD"):
		return;
	fill_section(binname, ".comment",0x0);
	#delete_signature_in_elf_header(binname);

def append_icf_search(tmpfile):
	global gen_hash;
	global elf_type;
	fname = None;
	#append restore_eflags function(macro)
	#should be added before icf_search
	cmd = 'cat restore_eflags.s >>'+tmpfile
	os.system(cmd);

	if(gen_hash == 1):
		if(elf_type == ET_EXEC):
			fname = "icf_search.s";
			cmd ="cat ./icf_search.s>>"+tmpfile
		elif(elf_type == ET_DYN):
			fname = "icf_search_pic.s";
			cmd ="cat ./icf_search_pic.s>>"+tmpfile
		else:
			print "elf file type unsupported, abort";
			exit(1);
	else:
		if(elf_type == ET_EXEC):
			cmd = "cat ./binsearch.s >>"+tmpfile
		else:
			print "elf file type unsupported, abort";
			exit(1);
	
	os.system(cmd);

	if(enforce_plt ==1):
		if(elf_type == ET_DYN):	
			cmd2 = 'cat '+fname+'|sed \'s/\$insn/$plt_insn/g\'| \
				sed \'s/binsearch/plt_search/g\'|  \
				sed \'s/\$local/$plt_local/g\'| \
				sed \'s/\$size/$plt_size/g\'| \
				sed \'s/\$insn_mask/$plt_insn_mask/g\'| \
				sed \'s/0x03000000/0x03000800/g\'| \
				sed \'s/call print_log/mov %gs:0x40, %edx\\naddl %ecx, %edx\\nmov %edx, %gs:0x40\\njmp binsearch/g\'| \
				sed \'s/array/plt_array/g\' >>'+tmpfile
		elif(elf_type == ET_EXEC):
			cmd2 = 'cat '+fname+'|sed \'s/\$insn/$plt_insn/g\'| \
				sed \'s/binsearch/plt_search/g\'|  \
				sed \'s/\$local/$plt_local/g\'| \
				sed \'s/\$size/$plt_size/g\'| \
				sed \'s/\$insn_mask/$plt_insn_mask/g\'| \
				sed \'s/0x03000000/0x03000800/g\'| \
				sed \'s/call print_log/jmp binsearch/g\'| \
				sed \'s/array/plt_array/g\' >>'+tmpfile
		print "cmd2:%s"%cmd2
		os.system(cmd2);
	
	if(transparent_call == 1):
		if(elf_type == ET_EXEC):
			fname = "icf_search_ret.s";
		elif(elf_type == ET_DYN):
			fname = "icf_search_ret_pic.s";
			#print "currently, transparent call/ret is not supported for DYN elf";
			#exit(1);
	
	cmd2 = 'cat '+fname+'|sed \'s/\$insn/$ret_insn/g\'| \
				sed \'s/binsearch/ret_search/g\'|  \
				sed \'s/\$local/$ret_local/g\'| \
				sed \'s/\$size/$ret_size/g\'| \
				sed \'s/\$insn_mask/$ret_insn_mask/g\'| \
				sed \'s/0x03000000/0x03000400/g\'| \
				sed \'s/array/ret_array/g\' >>'+tmpfile
	print "cmd2:%s"%cmd2
	os.system(cmd2);
	global use_local_hash;
	if(use_local_hash == 1):
		if(elf_type == ET_EXEC):
			fname = "icf_search_local.s"
			cmd ="cat ./icf_search_local.s>>"+tmpfile
		elif(elf_type == ET_DYN):
			fname = "icf_search_local_pic.s"
			cmd ="cat ./icf_search_local_pic.s>>"+tmpfile
		os.system(cmd);

		cmd2 = 'cat '+fname+'|sed \'s/\$local_insn/$ret_local_insn/g\'| \
					sed \'s/fake_use_ret/use_ret/g\'| \
					sed \'s/local_search/ret_local_search/g\'|  \
					sed \'s/\$local/$ret_local/g\'| \
					sed \'s/restore_and_jmp/ret_restore_and_jmp/g\'| \
					sed \'s/\$size/$ret_size/g\'| \
					sed \'s/\$insn_mask/$ret_insn_mask/g\'| \
					sed \'s/0x03000200/0x03000600/g\'| \
					sed \'s/local_array/ret_local_array/g\' >>'+tmpfile
		#add fake_use_ret so that icf_search(_pic).s won't use ret to jmp
		#the side effect is that use_ret is never effective when enforce_ret is 0
		os.system(cmd2);

	#generalize custom hash lookup routines

	#append print_log function
	cmd = 'cat print_log.s >>'+tmpfile
	os.system(cmd);
	
	lookup_routines.generate_asm()
	lookup_routines.output_asm(tmpfile)

	return tmpfile


def generate_insn_mapping(binname, mytext_addr,output):
	global gen_hash;
	global enforce_ret;
	global enforce_e_cfi
	global enforce_plt;

	global mapping_size	
	global local_mapping_size
	global ret_mapping_size
	global ret_local_mapping_size
	global plt_mapping_size
	global plt_local_mapping_size

	pattern = re.compile(r"^(?P<offset>[0-9a-fA-F]{1,8})\s+"
				"(?P<type>[^\s]+)\s\_"
				"(?P<addr>[0-9a-fA-F]+)\s*$")
	pattern_ret = re.compile(r"^(?P<offset>[0-9a-fA-F]{1,8})\s+"
				"(?P<type>[^\s]+)\s\_callnext_"
				"(?P<addr>[0-9a-fA-F]+)\s*$")

	if(gen_hash == 1):
		#mapping_size = generate_hash(binname, mytext_addr,output,0,pattern,"normal");
		plt_output = "plt_"+output;
		if(enforce_e_cfi ==1):
			mapping_size = generate_hash_v2(binname, mytext_addr,output,0,pattern,"normal");
		else:	
			mapping_size = generate_hash(binname, mytext_addr,output,0,pattern,"normal");

		cmd = "gcc -c "+output;
		os.system(cmd)


		if(enforce_plt == 1):
			plt_mapping_size = generate_hash_v2(binname, mytext_addr,plt_output,0,pattern,"plt");
			cmd = "gcc -c "+plt_output;
			os.system(cmd)

	
		ret_output = "ret_"+output;
		if(enforce_ret == 1):
			ret_mapping_size = generate_hash_v2(binname, mytext_addr,ret_output,0,pattern_ret,"return");
		else:
			ret_mapping_size = generate_hash(binname, mytext_addr,ret_output,0,pattern_ret,"return");
		cmd = "gcc -c "+ret_output;
		os.system(cmd)

	else:
		generate_mapping(binname, mytext_addr,output);

	if(use_local_hash ==1):
		local_output = "local_"+output
		if(enforce_e_cfi ==1):
		#local_mapping_size = generate_hash(binname, mytext_addr,local_output,1,pattern,"normal");
			local_mapping_size = generate_hash_v2(binname, mytext_addr,local_output,1,pattern,"normal");
		else:
			local_mapping_size = generate_hash(binname, mytext_addr,local_output,1,pattern,"normal");
		cmd = "gcc -c "+local_output;
		os.system(cmd)
		ret_local_output = "ret_"+local_output
		if(enforce_ret == 1):
			ret_local_mapping_size = generate_hash_v2(binname, mytext_addr,ret_local_output,1,pattern_ret,"return");
		else:
			ret_local_mapping_size = generate_hash(binname, mytext_addr,ret_local_output,1,pattern_ret,"return");
		cmd = "gcc -c "+ret_local_output;
		os.system(cmd)
def add_signature_in_elf_header(binname):
	global mytext_base;
	fd = os.open(binname,os.O_RDWR)
	os.lseek(fd, 12,os.SEEK_SET)
	os.write(fd, pack("<i",mytext_base));
	print "write mytext_base:%lx into elf header"%mytext_base
	os.close(fd);

def delete_signature_in_elf_header(binname):
	fd = os.open(binname,os.O_RDWR)
	os.lseek(fd, 12,os.SEEK_SET)
	os.write(fd, pack("<i",0));
	print "deleting signature in elf header";
	os.close(fd);

def mark_got_jmp_slot_zero(binname):
	#if(bin_type == "RTLD"):
	#	return;
	p = re.compile(r"^0x([0-9a-f]+)\s*$");
	fd = os.open(binname,os.O_RDWR)
	with open("./got_slots") as file:	
		for line in file:
			#print "gotslot:%s\n"%line;
			line = line.strip();
			m = p.match(line);
			if(m != None):
				addr = m.group(0);
				#print "addr:%s\n"%addr
				global eb
				offset = eb.convert_vma_to_offset(binname, addr);
				os.lseek(fd, offset,os.SEEK_SET);
				os.write(fd, pack("<i",0));

def translate_exported_symbol(binname):
	global link_type;
	global eb
	if(link_type == STATIC_LINKED):
		print "static binary needs no translation for exported symbol";
		return;
	if(use_local_hash != 1):
		print "there will be no local search table for exported symbol, so no translation\n";
		return;
	#if(transparent_call == 1):
	#	print "transparent call is enabled, so no need to translate exported symbol";
	#	return
	offset = eb.get_section_info(binname,".dynsym","offset");
	size = eb.get_section_info(binname,".dynsym","size");
	last = offset+size;
	cur = offset;
	fd = os.open(binname,os.O_RDWR)
	os.lseek(fd,offset,os.SEEK_SET);
	while(cur <last):
		os.lseek(fd,4,os.SEEK_CUR);
		objaddr = unpack("<i",os.read(fd,4))[0];
		if(objaddr == 0):
			os.lseek(fd,8,os.SEEK_CUR);
			cur+=16;
			continue;
		else:
			os.lseek(fd,4,os.SEEK_CUR);
			objtype = unpack("<b",os.read(fd,1))[0];
			if(objtype == 0x12 or objtype == 0x22):
				#WEAK or GLOBAL FUNC
				#WEAK: 0x20; GLOBAL:0x10
				#FUNC: 0x02
				# 0x12 = WEAK|FUNC ; 0x22 = GLOBAL|FUNC
				#do translation here
				global mytext_base;
				objaddr = "%x"%objaddr;
				objoffset = get_mapping_offset(objaddr);
				new_addr = mytext_base+int(objoffset,16);
				print "in dynsym, old address: %s"%objaddr;
				print "in dynsym, new address: %x"%new_addr;
				os.lseek(fd,-9,os.SEEK_CUR);
				os.write(fd,pack("<i",new_addr));
				os.lseek(fd,8,os.SEEK_CUR);
			else:
				os.lseek(fd,3,os.SEEK_CUR);
		cur+=16;
	
def check_runtime_reloc(orig_bin):
	pa = re.compile(r"^[0-9a-fA-F]+$");
	global eb
	text_off_begin = eb.get_section_info(orig_bin, ".text","offset");
	text_off_end = text_off_begin + eb.get_section_info(orig_bin, ".text","size");
	
	cmd = "readelf -r "+orig_bin + " | awk '{print $1}'";
	print "cmd: %s"%cmd
	with os.popen(cmd) as file:
		for line in file:
			_m = pa.match(line);
			if(_m != None):
				offset = int(_m.group(0),16);
				#print "relocation offset: %x"%offset
				if((offset >= text_off_begin) and (offset <= text_off_end)):
					print "this elf has runtime relocation!";
					fd_rr = os.open("../runtime_relocation.txt",os.O_CREAT|os.O_APPEND);
					os.write(fd_rr, orig_bin);
					os.close(fd_rr);
					return 1;

	print "this elf does not have runtime relocation!";
	return 0;
def test_main(orig_path):
	#orig_path = "/usr/bin/lyx"
	global global_binname;
	global lookup_routines
	global config_file;
	global client_file;

	orig_bin = os.path.basename(orig_path);
	global_binname = orig_bin;	

	cmd = "mkdir -p "+target_dir
	os.system(cmd);

	cmd = "mkdir -p "+target_dir+"/"+orig_bin
	os.system(cmd)

	if(debug_mode !=1):
		cmd = "rm -rf "+target_dir+"/"+orig_bin+'/*'
		os.system(cmd)

	cmd = "cp "+orig_path +" "+ target_dir+"/" + orig_bin + '/' + orig_bin;
	os.system(cmd)
	cmd = "cp "+"	dump2asm.pl \
			bin_translate.pl \
			get_eh_icf_address.pl \
			CfiBinAnalyz.pm  \
			asm_utility/* " \
			+ config_file \
			+ " " \
			+target_dir+"/"+orig_bin
	os.system(cmd);
	if(profile_file != None):
		cmd = "cp "+profile_file+" "+target_dir+"/"+orig_bin
		os.system(cmd)

	if(client_file != None):
		cmd = "cp "+client_file+" "+target_dir+"/"+orig_bin
		os.system(cmd)
		#copy related files
		client_related_file_dir = os.path.splitext(client_file)[0]
		cmd = "cp "+client_related_file_dir+"/* "+target_dir+"/"+orig_bin
		os.system(cmd)

	config_file_base = os.path.basename(config_file)
	cmd = "mv "+target_dir+"/"+orig_bin+"/"+config_file_base+" "+target_dir+"/"+orig_bin+"/config";
	os.system(cmd);

	modified_bin_0 = "./" + orig_bin + "_modified_0"
	modified_bin_1 = "./" + orig_bin + "_modified_1"
	modified_bin_2 = "./" + orig_bin + "_modified_2"
	binname = "./"+orig_bin + "_final"

	eb.set_binname(binname)

	os.chdir(target_dir+"/"+orig_bin);
	#the existence of stat means translation success!
	cmd = "rm -f ./stat";
	os.system(cmd);

	lookup_routines = hash_tables(orig_bin, "./htable_info.cfg", 0);

	
	#check if there is runtime relocation
	if(check_runtime_reloc(orig_bin) == 1):
		exit(1);


	#cmd1 = "objdump -d " + orig_bin + ">log"
	#os.system(cmd1);


	#global debug_mode;
	#global client_file;
	if(debug_mode !=1):
	#if debug mode is 1, then on need to generate the asm file
		cmd = "rm -f ./generated_asm.s myrodata.s analysis_done"
		os.system(cmd)

		#if((elf_type == ET_DYN) and (bin_type == "RTLD")):
		#	print "no need to translate instruction for ld.so (currently)"
		#else:
		cmd2 = "./dump2asm.pl log ./"+orig_bin;
		os.system(cmd2);	
		if(os.path.exists("analysis_done") == False):
			print "there are errors in binary analysis, no notification from dump2asm.pl, abort";
			exit(1);

		if(client_file !=None):
			cmd2 = "ln -s ./bin_translate.pl bin_translate.pm"
			os.system(cmd2);
			cmd2 = "./"+os.path.basename(client_file)+" log ./"+orig_bin;
			os.system(cmd2);
		else:
			cmd2 = "./bin_translate.pl log ./"+orig_bin;
			os.system(cmd2);

		if(os.path.exists("./generated_asm.s") == False):
			print "there are errors in binary translation: no generated_asm.s, abort";
			exit(1);

		if(only_gen_asm==1):
			print "only_gen_asm is set, only generating assembly, and done\n";
			exit(0);

		attach_reference_monitor(orig_bin);

	cmd3 = "gcc -c generated_asm.s"
	os.system(cmd3);
	
	eb.extract_data("./generated_asm.o",".text","./generated_input")

	cmd4 = "objcopy --add-section .mytext=generated_input "+orig_bin + " " + modified_bin_0;
	os.system(cmd4); 
	#global eb
	eb.modify_section_info(modified_bin_0,".mytext","align",0x00001000)
	cmd = "objcopy " + modified_bin_0 + " " + modified_bin_1;
	os.system(cmd)

	#generating instruction mapping
	mytext_start = eb.get_section_info(modified_bin_1,".mytext","offset");
	print "mytext_start is %lx"%mytext_start
	segment_base = get_new_segment_base_addr(modified_bin_1);
	mytext_addr = segment_base + (mytext_start & 0x00000fff)
	print "mytext_addr is %lx"%mytext_addr
	mytext_addr = "%lx"%mytext_addr
	#generate_mapping("./generated_asm.o",mytext_addr,"./mapping.s");
	generate_insn_mapping("./generated_asm.o",mytext_addr,"mapping.s");
	#cmd = "gcc -c mapping.s"
	#os.system(cmd)
	
		
	lookup_routines.set_mytext_base(int(mytext_addr,16))
	lookup_routines.generate_data();

	eb.extract_data("./mapping.o",".text","./mapping_input")	
	cmd = "objcopy --add-section .func_orig=mapping_input "+modified_bin_1 + " " + modified_bin_2
	os.system(cmd)
	eb.modify_section_info(modified_bin_2,".func_orig","align",0x00001000)

	if(use_local_hash == 1):
		eb.extract_data("./local_mapping.o",".text","./local_mapping_input")
		cmd = "objcopy --add-section .func_local=local_mapping_input "+modified_bin_2 + " " + modified_bin_2
		os.system(cmd)
		eb.modify_section_info(modified_bin_2,".func_local","align",0x00001000)

	eb.extract_data("./ret_mapping.o",".text","./ret_mapping_input")
	cmd = "objcopy --add-section .ret_orig=ret_mapping_input "+modified_bin_2 + " " + modified_bin_2
	os.system(cmd)
	eb.modify_section_info(modified_bin_2,".ret_orig","align",0x00001000)

	if(use_local_hash == 1):
		eb.extract_data("./ret_local_mapping.o",".text","./ret_local_mapping_input")
		cmd = "objcopy --add-section .ret_local=ret_local_mapping_input "+modified_bin_2 + " " + modified_bin_2
		os.system(cmd)
		eb.modify_section_info(modified_bin_2,".ret_local","align",0x00001000)

	if(enforce_plt == 1):
		eb.extract_data("./plt_mapping.o",".text","./plt_mapping_input")
		cmd = "objcopy --add-section .plt_data=plt_mapping_input "+modified_bin_2 + " " + modified_bin_2
		os.system(cmd)
		eb.modify_section_info(modified_bin_2,".plt_data","align",0x00001000)

	eb.compile_inject_data(lookup_routines.table_list, modified_bin_2)
	#lookup_routines.compile_inject_data(modified_bin_2)

	cmd = "objcopy " + modified_bin_2 + " " + binname;
	os.system(cmd)

	modify_orig_elf(binname);
	modify_entry_point(orig_bin, binname);

	#let the ld.so know that this is a translated binary
	add_signature_in_elf_header(binname);

	#mark_got_jmp_slot_zero(binname);


	translate_exported_symbol(binname);
	#notify that translation is done
	cmd = "echo '0'>./stat";
	os.system(cmd);

	special_handling_ld_so(binname);

	#cmd = 'rm -f log generated_asm.* *.s *.o *_input *_modified_* static_symbols';
	#os.system(cmd);
	aa="""
	#modify the entry point
	global eb
	entry_addr = eb.get_elfhdr_info(orig_bin, "Entry point address:")
	entry_offset = get_mapping_offset(entry_addr);
	entry_addr = int(entry_addr, 16);
	entry_offset = int(entry_offset, 16);


	global start_of_mytext
	if(start_of_mytext != None):
		new_entry_addr = entry_offset + start_of_mytext
		print "start of mytext is %lx"%start_of_mytext
		print "new entry point addr is %lx"%new_entry_addr
	else:
		print "start of mytext is None, abort!"
		return
	print "entry point offset is %lx"%entry_offset
	eb.modify_elfhdr_info(binname, "entrypoint", new_entry_addr)"""
	#update_callback_func(orig_bin, binname, get_main_from_start, get_main_offset);
	#update_callback_func(orig_bin, binname, get_libc_csu_init_from_start, get_libc_csu_init_offset);
	#update_callback_func(orig_bin, binname, get_libc_csu_fini_from_start, get_libc_csu_fini_offset);



#get_callback_from_start: return the original entry point of a callback function
#get_callback_offset: return the (absolute)offset of the location where the callback function is taken
def update_callback_func(orig_bin, binname, get_callback_from_start, get_callback_offset):
	global mytext_base
	global eb
	entry_addr = eb.get_elfhdr_info(orig_bin, "Entry point address:")
	entry_offset = get_mapping_offset(entry_addr);
	entry_addr = int(entry_addr, 16);
	entry_offset = int(entry_offset, 16);

	 
	entry_addr = "%x"%entry_addr
	entry_offset = eb.convert_vma_to_offset(binname, entry_addr)
	
	callback_addr = get_callback_from_start(binname, entry_offset)
	callback_addr = "%x"%callback_addr
	callback_offset = get_mapping_offset(callback_addr)
	callback_offset = int(callback_offset, 16)
	print "callback offset from section start is %x"%callback_offset
	mytext_offset = eb.get_section_info(binname, ".mytext", 'offset')
	print "start of .mytext is %x"%mytext_offset
	callback_offset = mytext_offset + callback_offset
	print "offset of callback is %x"%callback_offset
	callback_addr = mytext_base + (callback_offset - mytext_offset)
	print "callback address is %x"%callback_addr
	
	entry_addr = eb.get_elfhdr_info(binname, "Entry point address:")
	entry_offset = eb.convert_vma_to_offset(binname, entry_addr)
	fd = os.open(binname,os.O_RDWR)

	callback_taken_offset = get_callback_offset(binname, entry_offset)

	os.lseek(fd, callback_taken_offset,os.SEEK_SET)
	os.write(fd, pack("<i",callback_addr))
	os.close(fd);
	#get and modify the address of main function
	#step 1: get the address of main function
	#offset = 0x08060ede
	#offset = "%x"%offset
	#print "converted offset %s"%offset
	#global eb
	#myoffset = eb.convert_vma_to_offset(binname, str(offset))

	#print "offset is %lx"%myoffset
	#myvma = convert_offset_to_vma(binname, '0172c0')
	#print "vma is %lx"%myvma
	#main_addr = get_main_from_start(binname, entry_addr)
	#print "main function is at address: %lx"%main_addr
	#print "main offset is %lx"%main_offset
def relocate_interp(binname):
	#relocate the .interp section to the end of data segment
	global eb
	interp_mem_addr = eb.get_section_info(binname,".interp", "addr")
	
	if(interp_mem_addr == None):
		return None;

	interp_addr = eb.get_section_info(binname,".interp", "offset")
	interp_size = eb.get_section_info(binname,".interp", "size")
	print "interp addr:%d"%interp_addr

	
	#now get the PHDR information
	phdr_num = eb.get_elfhdr_info(binname, "Number of program headers:");
	phdr_size = eb.get_elfhdr_info(binname,"Size of program headers:");
	phdr_start = eb.get_elfhdr_info(binname,"Start of program headers:");

	#relocate interp to the new place
	fd = os.open(binname, os.O_RDWR);
	os.lseek(fd, interp_addr,os.SEEK_SET)
	buf = os.read(fd, interp_size);
	new_interp_addr = interp_addr + phdr_size #move it 32bytes afterwards
	os.lseek(fd, new_interp_addr, os.SEEK_SET)
	os.write(fd, buf);
	os.close(fd);


	#modify the interp offset
	offset_begin = phdr_start
	fd = os.open(binname, os.O_RDWR);
	os.lseek(fd, offset_begin, os.SEEK_SET)
	for size in xrange(0, phdr_num):
		os.lseek(fd, phdr_size, os.SEEK_CUR)
		phdr_type = unpack('<i',os.read(fd,4))[0];
		if phdr_type == 0x00000003: #phdr entry type: interp
			os.write(fd,pack('<i',new_interp_addr))
			print "modifying interp address to %lx"%new_interp_addr
	#modify the interp offset in section table
	eb.modify_section_info(binname, ".interp", "offset",new_interp_addr)
	os.close(fd);
	if(config_modify_interpreter == 1):
		offset = eb.get_section_info(binname, ".interp", "offset");
		fd = os.open(binname,os.O_RDWR);
		os.lseek(fd, offset, os.SEEK_CUR);
		if(use_far_jmp == 1):
			os.write(fd, "/lib/linux-ld.so.3\0");
		else:
			os.write(fd,"/lib/linux-ld.so.4\0");
		os.close(fd);

def extend_phdr(binname):
	#now get the PHDR information
	phdr_num = eb.get_elfhdr_info(binname, "Number of program headers:");
	phdr_size = eb.get_elfhdr_info(binname,"Size of program headers:");
	phdr_start = eb.get_elfhdr_info(binname,"Start of program headers:");


	#change phdr header count (increment by one)
	# offset: 0x32 (a fixed offset inside elf header)
	fd = os.open(binname, os.O_RDWR);
	os.lseek(fd, 44,os.SEEK_SET);
	num = unpack('<h',os.read(fd,2))[0];
	print num
	num = num+1;
	os.lseek(fd, 44, os.SEEK_SET);
	os.write(fd,pack('<h',num));
	os.close(fd);

	offset_begin = phdr_start + phdr_num*phdr_size
	#mytext_mem_addr: vma
	#mytext_addr: offset
	mytext_mem_addr =eb.get_section_info(binname, ".mytext", "addr");
	mytext_addr = eb.get_section_info(binname, ".mytext", "offset");
	mytext_size = eb.get_section_info(binname, ".mytext", "size");	
	func_orig_mem_addr =eb.get_section_info(binname, ".func_orig", "addr");
	func_orig_addr = eb.get_section_info(binname, ".func_orig", "offset");
	func_orig_size = eb.get_section_info(binname, ".func_orig", "size");
	func_local_addr = eb.get_section_info(binname, ".func_local", "offset");
	func_local_size = eb.get_section_info(binname, ".func_local", "size");	
	ret_orig_addr = eb.get_section_info(binname, ".ret_orig", "offset");
	ret_orig_size = eb.get_section_info(binname, ".ret_orig", "size");
	ret_local_addr = eb.get_section_info(binname, ".ret_local", "offset");
	ret_local_size = eb.get_section_info(binname, ".ret_local", "size");
	plt_data_addr = eb.get_section_info(binname, ".plt_data", "offset");
	plt_data_size = eb.get_section_info(binname, ".plt_data", "size");

	last_data_addr = None
	last_data_size = None

	if(lookup_routines.htable_num > 0):
		last_table_name = lookup_routines.get_last_table_name()
		last_data_addr = eb.get_section_info(binname,last_table_name , "offset")
		last_data_size = eb.get_section_info(binname,last_table_name , "size")
	else:
		if(enforce_plt == 1):
			last_data_addr = plt_data_addr
			last_data_size = plt_data_size
		else:
			if(use_local_hash ==1):
				last_data_addr = ret_local_addr
				last_data_size = ret_local_size
			else:
				last_data_addr = ret_orig_addr
				last_data_size = ret_orig_size

	print mytext_mem_addr;
	print mytext_addr;
	print mytext_size;

	#fill the new phdr entry with valid value
	type = phdr.PT_LOAD
	offset = mytext_addr
	global mytext_base
	segment_base = get_new_segment_base_addr(binname);
	mytext_base = segment_base + (0x00000fff & mytext_addr)

	global start_of_mytext 
	start_of_mytext = mytext_base


	paddr = mytext_base
	fsize = last_data_addr + last_data_size - mytext_addr # size of .mytext and .func_orig (plus alignment bytes in between)
	memsize = fsize 
	flags = 0x00000005 # EXEC|READ
	align = 0x00001000

	print "offset:%d"%offset_begin
	
	fd = os.open(binname, os.O_RDWR);
	os.lseek(fd, offset_begin, os.SEEK_SET);
	os.write(fd,pack('<i',type));
	os.write(fd,pack('<i',offset));
	os.write(fd,pack('<i',mytext_base));
	os.write(fd,pack('<i',paddr));
	os.write(fd,pack('<i',fsize));
	os.write(fd,pack('<i',memsize));
	os.write(fd,pack('<i',flags));
	os.write(fd,pack('<i',align));
	os.close(fd);

	#fill the section table with valid value
	print "mytext_base: %lx"%mytext_base
	eb.modify_section_info(binname, ".mytext", "addr", mytext_base);
	eb.modify_section_info(binname, ".mytext", "flags", 0x00000006);#flags: ALLOC|EXEC

	segment_base = get_new_segment_base_addr(binname);
	eb.modify_section_info(binname, ".func_orig", "addr", segment_base + func_orig_addr - (0xfffff000 & mytext_addr)) 
	eb.modify_section_info(binname, ".func_orig", "flags", 0x00000006);#flags: ALLOC|EXEC


	eb.modify_section_info(binname, ".ret_orig", "addr", mytext_base + ret_orig_addr - (0xfffff000 & mytext_addr)) 
	eb.modify_section_info(binname, ".ret_orig", "flags", 0x00000006);#flags: ALLOC|EXEC

	if(use_local_hash == 1):
		eb.modify_section_info(binname, ".func_local", "addr", mytext_base + func_local_addr - (0xfffff000 & mytext_addr)) 
		eb.modify_section_info(binname, ".func_local", "flags", 0x00000006);#flags: ALLOC|EXEC

		eb.modify_section_info(binname, ".ret_local", "addr", mytext_base + ret_local_addr - (0xfffff000 & mytext_addr)) 
		eb.modify_section_info(binname, ".ret_local", "flags", 0x00000006);#flags: ALLOC|EXEC

	if(enforce_plt == 1):
		eb.modify_section_info(binname, ".plt_data", "addr", mytext_base + plt_data_addr - (0xfffff000 & mytext_addr)) 
		eb.modify_section_info(binname, ".plt_data", "flags", 0x00000006);#flags: ALLOC|EXEC

	hlist = lookup_routines.table_list
	for h in hlist:
		sec_offset = eb.get_section_info(binname, h.get_secname(),"offset")
		eb.modify_section_info(binname, h.get_secname(), "addr", mytext_base + sec_offset - (0xfffff000 & mytext_addr))
		eb.modify_section_info(binname, h.get_secname(), "flags", 0x00000006);#flags: ALLOC|EXEC
		h.array = mytext_base + sec_offset - (0xfffff000 & mytext_addr)
		h.array_4 = mytext_base + sec_offset - (0xfffff000 & mytext_addr) +4

def patch_routines(binname):
	pattern = re.compile(r"^(?P<offset>[0-9a-fA-F]{1,8})\s+"
		"(?P<info>[0-9a-fA-F]{1,8})\s+"	
		"(?P<type>[^\s]+)\s+"
		"(?P<symvalue>[0-9a-fA-F]{1,8})\s+"
		"(?P<name>[^\n]+)$")
	fd = os.open(binname, os.O_RDWR)
	base = eb.get_section_info(binname,".mytext",'offset')
	for h in lookup_routines.table_list:
		h.setup_name_mapping()
		cmd = "readelf -W -r generated_asm.o|grep "+h.func_name
		with os.popen(cmd) as file:
			for line in file:
				#print line
				m = pattern.match(line)
				if(m!=None):
					name = m.group('name')
					if name in h.name_mapping:
						print "patching %s"%name
						print "value:%x"%h.name_mapping[name]
						offset = base + int(m.group('offset'),16)
						os.lseek(fd, offset, os.SEEK_SET)
						os.write(fd, pack('<i', h.name_mapping[name]))
	
def modify_orig_elf(binname):

	global eb

	relocate_interp(binname);

	#eb.add_dynamic_option(binname);

	#extend phdr and modify section info
	extend_phdr(binname);

	#patch .mytext to solve all the relocation entries
	patch_mytext(binname);

	patch_routines(binname);

	global use_segv;
	if(use_segv == 0):
		#fill original text section with "int 0x3"
		#if(bin_type =="RTLD" and elf_type == ET_DYN):
		#	print "do nothing for ld.so"
		#else:
		fill_section(binname,".text",0xcc);
		fill_section(binname,".init",0xcc);
		fill_section(binname,".fini",0xcc);
		fill_section(binname,"__libc_freeres_fn",0xcc);
		fill_section(binname,"__libc_thread_fre",0xcc);
	else:
		print "changing the original code to be readonly";
		eb.modify_phdr_info(binname, 0, phdr.PT_LOAD, phdr.p_flags, 0x00000004);


	#add a library dependency
	#name: ibc.so.6
	#step1: figure out the offset of libc.so.6 string
	#step2: add the offset by one
	#step3: add one option in dynamic section
	cmd = 'readelf -p .dynstr '+binname;
	pattern = re.compile(r"^\s*\[\s*(?P<offset>[0-9a-fA-F]{1,8})\s*\]\s+"
				"(?P<name>[^\n]+$)");
	
	found_libc=0;
	libc_offset=0;
	with os.popen(cmd) as file:
		for line in file:
			m = pattern.match(line);
			if(m!=None):
				strname = m.group('name');
				strname = strname.strip();
				if(strname == "libc.so.6"):
					found_libc=1;
					libc_offset=int(m.group('offset'), 16);
					break;
	if(found_libc == 0):
		print "does not find libc.so.6 in %s!"%binname;
		return
	libc_offset+=1;
	eb.add_dynamic_option(binname,0x00000001,libc_offset);

def fill_section(binname, secname, value):
	global eb
	v = pack('<B',value);
	if(eb.get_section_info(binname, secname, "offset") == None):
		return;
	sec_offset = eb.get_section_info(binname, secname, "offset");
	sec_size = eb.get_section_info(binname, secname, "size");
	print "filling section %s with value %lx"%(secname, value);
	print "%s section offset:%d"%(secname,sec_offset);
	print "%s section size:%d"%(secname, sec_size);
	fd = os.open(binname, os.O_RDWR);
	os.lseek(fd, sec_offset, os.SEEK_SET);
	for i in xrange(1,sec_size):
		os.write(fd,v);
	os.close(fd);

if __name__ == "__main__":
	main()



"""
def test():
	addr = eb.get_section_info("./ls2", ".interp", "offset")
	print "address is %d"%addr
"""

#test()

