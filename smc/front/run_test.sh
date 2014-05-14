#!/bin/sh

sed -e 's# *\([^ ]\+\)\(.*\)$#./main.native\2 examples/\1#e' tests

