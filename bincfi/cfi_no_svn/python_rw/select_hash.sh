#!/bin/bash
find . -name icf_target_addr >/tmp/log
cat /tmp/log|while read a; do echo -en "$a\t"; python ./select_hash.py $a|grep "total collision rate is"|sed 's/shift:0\s*total collision rate is://g';  done
