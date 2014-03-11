#!/usr/bin/python
import re
import os
import sys
import math
def hash_0(idx,first_insn, last_insn, len, shift):
	idx = (idx )% len;
	return idx

def hash_1(idx,first_insn, last_insn, len, shift):
	idx = (idx + (idx>>shift))% len;
	return idx
def hash_2(idx,first_insn, last_insn, len, shift):
	idx = (idx ^ (idx>>shift))% len;
	return idx

def hash_3(idx,first_insn, last_insn, len, shift):
	idx = (idx + (idx>>shift) + last_insn/(idx+104383))% len;
	return idx

def hash_4(idx,first_insn, last_insn, len, shift):
	idx = (idx + (idx>>shift))% len;
	return idx

def construct_hash(insn_mapping, insn_len, _insn_mask, first_insn, last_insn, hash_func, shift):
	collision = 0;
	total_collision = 0;
	longest_collision = 0;
	collision_array = [[0,0] for i in xrange(0,insn_len)]
	insn_array = [[0,0] for i in xrange(0,insn_len)]
	for key in insn_mapping.keys():
		idx =  key - first_insn;
		idx = hash_func(idx,first_insn, last_insn, insn_len, shift)
		#idx = (idx + idx>>5)% insn_len
		#print "0x%lx 0x%lx"%(key, insn_mapping[key]);
		#print "%d 0x%lx"%(idx, insn_mapping[key]);
		collision = 0;
		if(insn_array[idx][0] != 0):
			collision_array[idx][0] = idx
			collision_array[idx][1] += 1;
			#print "collision idx:%d\tcollision:%d"%(idx,collision_array[idx][1])
			total_collision +=1;
			continue
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
			#if(successflag == 0):

			#	print "longest collision is:%d"%longest_collision
			#	print "too many collisions, abort";
			#	exit(1);
		else:
			insn_array[idx][0] = key
			insn_array[idx][1] = insn_mapping[key];
	print "shift:%d\ttotal collision time is:%d"%(shift,total_collision)
	aveg_collision = float(total_collision)/float(count);
	print "shift:%d\ttotal collision rate is:%f"%(shift,aveg_collision)
	print "insn array len is %d"%insn_len
	print "insn mask is %lx"%_insn_mask
	sorted_collision = collision_array.sort(key=lambda x: x[1], reverse=True)
	print collision_array[0:5]
	print "\n";

filename = sys.argv[1];
pattern = re.compile(r"^\s*([0-9a-f]+)\s*$")
insn_mapping = dict();
count = 0;
first_insn = 0x7fffffff;
last_insn = -1;
with open(filename,"r") as fh:
	for line in fh.readlines():
		#print line
		m = pattern.match(line)
		if(m != None):
			#print m.group(1)
			value = int(m.group(1), 16);
			if value in insn_mapping:
				continue;
			else:
				count+=1;
				insn_mapping[value] = 1;
				if(value < first_insn):
					first_insn = value
				elif(value > last_insn):
					last_insn = value


	print "total count:%d"%count

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

	print "hash log:%d"%hash_log
	print "hash log_f:%f"%hash_log_f
	construct_hash(insn_mapping, insn_len, _insn_mask, first_insn, last_insn, hash_0, 0)
	#for i in range(1,16):
	#	construct_hash(insn_mapping, insn_len, _insn_mask, first_insn, last_insn, hash_0, i)


