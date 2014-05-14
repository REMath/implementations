frama-c.byte -cpp-command 'gcc -C -E -D_BSD_SOURCE -DDEBIAN -IEXT -I.' -taint-analysis -config-file '../../../default.cfg' *.c
