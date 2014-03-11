#!/bin/bash
cat $1|grep "trying file="|sed 's/^\s*[0-9]\+:\s*trying file=//g'|sort|uniq
