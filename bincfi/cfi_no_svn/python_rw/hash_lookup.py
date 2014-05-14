#!/usr/bin/python
from __future__ import with_statement
from struct import *

import re
import math
import os
import sys

from elf_basic import *
class htable(object):
	TYPE_TRANSLATE	= "TRANSLATE"
	TYPE_CHECK	= "CHECK"
	def __init__(self,func_name, search_type, template_file, path, gbl_lkup_addr, input_data, output_data, output_asm, mytext_base,binname):
		self.func_name = func_name
		self.path = path
		self.search_type = search_type
		self.gbl_lkup_addr = gbl_lkup_addr
		self.mytext_base = mytext_base
		self.binname = binname

		self.template_file = path+'/'+template_file
		self.input_data = path+'/'+input_data
		self.output_asm = path+'/'+output_asm
		self.output_data = path+'/'+output_data
		
		
		self.insn_mapping = None
		self.insn_array = None
		self.name_mapping = None

		self.first_insn = None;
		self.last_insn = None;
		self.insn_mask = None;
		self.size = None;
		self.array = None;
		self.array_4 = None;
		pass;
	def setup_name_mapping(self):
		m = dict();
		if(self.search_type == "TRANSLATE"):
			m[self.func_name+'_insn_begin'] = self.first_insn;
			m[self.func_name+'_insn_end']	= self.last_insn;
			m[self.func_name+'_insn_mask']	= self.insn_mask;
			m[self.func_name+'_array']	= self.array;
			m[self.func_name+'_size']	= self.size;
			m[self.func_name+'_array_4']	= self.array_4;
		elif(self.search_type == "CHECK"):
			m[self.func_name+'_local_insn_begin'] = self.first_insn;
			m[self.func_name+'_local_insn_end']	= self.last_insn;
			m[self.func_name+'_local_insn_mask']	= self.insn_mask;
			m['local_'+self.func_name+'_array']	= self.array;
			m[self.func_name+'_local_size']	= self.size;

		self.name_mapping = m
		
	def generate_asm(self):
		print "generating hashtable for "+self.func_name
		cmd = "";
		if(self.search_type == "TRANSLATE"):
			cmd = 'cat '+self.template_file+'|sed \'s/\$insn/$'+self.func_name+'_insn/g\'| \
				sed \'s/binsearch/'+self.func_name+'_search/g\'|  \
				sed \'s/local_search/'+self.func_name+'_local_search/g\'|  \
				sed \'s/\$local/$'+self.func_name+'_local/g\'| \
				sed \'s/\$size/$'+self.func_name+'_size/g\'| \
				sed \'s/\$insn_mask/$'+self.func_name+'_insn_mask/g\'| \
				sed \'s/0x03000000/'+self.gbl_lkup_addr+'/g\'| \
				sed \'s/0x03000200/'+self.gbl_lkup_addr+'/g\'| \
				sed \'s/restore_and_jmp/'+self.func_name+'_restore_and_jmp/g\'| \
				sed \'s/array/'+self.func_name+'_array/g\' >'+self.output_asm
			print cmd
		elif(self.search_type == "CHECK"):
			cmd = 'cat '+self.template_file+'|sed \'s/binsearch/'+self.func_name+'_search/g\'|  \
				sed \'s/local_search/'+self.func_name+'_local_search/g\'|  \
				sed \'s/\$local/$'+self.func_name+'_local/g\'| \
				sed \'s/\$size/$'+self.func_name+'_local_size/g\'| \
				sed \'s/\$insn_mask/$'+self.func_name+'_local_insn_mask/g\'| \
				sed \'s/0x03000000/'+self.gbl_lkup_addr+'/g\'| \
				sed \'s/0x03000200/'+self.gbl_lkup_addr+'/g\'| \
				sed \'s/restore_and_jmp/'+self.func_name+'_restore_and_jmp/g\'| \
				sed \'s/local_array/local_'+self.func_name+'_array/g\' >'+self.output_asm
			print cmd

		os.system(cmd)

	def generate_mapping(self):
		pattern = re.compile(r"^\s*([0-9a-f]+)\s*$")
		insn_mapping = dict();
		count = 0;
		first_insn = 0x7fffffff;
		last_insn = -1;
		with open(self.input_data,"r") as fh:
			for line in fh.readlines():
				#print line
				m = pattern.match(line)
				if(m != None):
					#print m.group(1)
					value = int(m.group(1), 16);
					#value = m.group(1)
					addr = "%x"%value
					offset = translate_orig_addr_to_offset(self.binname, addr)
					if(offset == None):
						print "error, address:%x cannot be translated"%value
						exit(1)
					translated = int(offset,16) + self.mytext_base
					if(self.search_type == htable.TYPE_TRANSLATE):
						insn_mapping[value] = translated;
					elif(self.search_type == htable.TYPE_CHECK):
						insn_mapping[translated] = translated;
						value = translated
					if(value < first_insn):
						first_insn = value
					if(value > last_insn):
						last_insn = value

		count = len(insn_mapping)
		hash_size_log = int(math.log(count, 2));
		hash_log = int(hash_size_log);
		hash_log_f = math.log(count,2);
		if(hash_log_f - hash_log >0.5):
			hash_log +=2;
		else:
			hash_log+=1;
		insn_len = int(math.pow(2,hash_log))
		#global insn_mask
		_insn_mask = insn_len -1;

		self.table_size = insn_len
		self.first_insn = first_insn
		self.last_insn = last_insn
		self.insn_mask = _insn_mask
		self.size = len(insn_mapping)
		self.insn_mapping = insn_mapping
		print "total count:%d"%count
		print "first insn:%x"%self.first_insn
		print "last insn:%x"%self.last_insn
		print "insn mask:%x"%self.insn_mask

		print "hash log:%d"%hash_log
		print "hash log_f:%f"%hash_log_f
	
	def hash_0(self,key,first_insn, last_insn, len, shift):
		idx = (key - first_insn)% len;
		return idx

	def generate_hash_array(self,hash_func, shift):
		insn_mapping = self.insn_mapping
		insn_len = self.table_size
		_insn_mask = self.insn_mask
		first_insn = self.first_insn
		last_insn = self.last_insn

		collision = 0;
		total_collision = 0;
		longest_collision = 0;
		collision_array = [[0,0] for i in xrange(0,insn_len)]
		insn_array = [[0,0] for i in xrange(0,insn_len)]
		for key in insn_mapping.keys():
			idx = hash_func(key,first_insn, last_insn, insn_len, shift)
			#idx = (idx + idx>>5)% insn_len
			#print "0x%lx 0x%lx"%(key, insn_mapping[key]);
			#print "%d 0x%lx"%(idx, insn_mapping[key]);
			collision = 0;
			if(insn_array[idx][0] != 0):
				collision = 1;
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
		print "shift:%d\ttotal collision time is:%d"%(shift,total_collision)
		aveg_collision = float(total_collision)/float(self.size);
		print "shift:%d\ttotal collision rate is:%f"%(shift,aveg_collision)
		print "insn array len is %d"%insn_len
		print "insn mask is %lx"%_insn_mask
		print "longest collision: %d"%longest_collision
		#sorted_collision = collision_array.sort(key=lambda x: x[1], reverse=True)
		#print collision_array[0:5]
		print "\n";

		self.insn_array = insn_array
	
	def generate_output(self):
		insn_array = self.insn_array
		print "hash table size: %d"%self.table_size
		fd = os.open(self.output_data, os.O_CREAT|os.O_TRUNC|os.O_RDWR, 0644)
		os.write(fd, ".text\n")	
		if(self.search_type == "TRANSLATE"):
			for idx in xrange(0, self.table_size):
				string = ".long\t0x%lx\n.long\t0x%lx\n"%(insn_array[idx][0], insn_array[idx][1])
				os.write(fd,string);
		elif(self.search_type == "CHECK"):
			for idx in xrange(0, self.table_size):
				string = ".long\t0x%lx\n"%(insn_array[idx][0])
				os.write(fd,string);
		else:
			print "error generating output data in file %s"%self.output_data;
			exit(1);

	def generate_data(self):
		self.generate_mapping()
		self.generate_hash_array(self.hash_0,0);
		self.generate_output()

	def set_mytext_base(self,addr):
		self.mytext_base = addr;

	def get_secname(self):
		if(self.search_type == "TRANSLATE"):
			return '.'+self.func_name+"_orig";
		else:
			return '.'+self.func_name+"_local";
	
	
class hash_tables(object):
	
	def __init__(self, binname, htable_file,mytext_base):
		self.path = "."
		self.table_list = [];
		self.htable_num = 0;
		self.binname = binname
		self.mytext_base = mytext_base
		try:
			with open(htable_file,'r') as fh:
				p0 = re.compile(r"^#.*$");
				p = re.compile(r"^\s*(?P<func>[^,]+),(?P<type>[^,]+),(?P<template>[^,]+),(?P<input_data>[^,]+),(?P<output_asm>[^,]+),(?P<output_data>[^,]+),(?P<global_lookup>[^\n]+)\s*$")
				for line in fh:
					m0 = p0.match(line)
					if(m0!=None):
						continue
					m = p.match(line)
					print line
					if(m!=None):
						table = htable(m.group('func'), m.group('type'), m.group('template'), self.path, m.group('global_lookup'),m.group('input_data'),m.group('output_data'),m.group('output_asm'),mytext_base,binname)
						self.table_list.append(table)

					self.htable_num = len(self.table_list)
		except IOError:
			self.htable_num = 0;
			return

	def generate_asm(self):
		for h in self.table_list:
			h.generate_asm()
	def generate_data(self):
		for h in self.table_list:
			h.generate_data()
	def set_mytext_base(self,addr):
		for h in self.table_list:
			h.set_mytext_base(addr)
	def output_asm(self, filename):
		for h in self.table_list:
			cmd = "cat "+h.output_asm+">> "+filename
			os.system(cmd)
	def get_last_table_name(self):
		return self.table_list[-1].get_secname()

#binname = sys.argv[1]
#htables = hash_tables(binname,"./htable_info.cfg",0x0a000000)
#htables.generate_asm()
#htables.generate_data()
