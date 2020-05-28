#!/bin/bash
../aiger/aigtoaig ../models/"$1".aig ../models/"$1".aag
cd ../src || exit
pypy3 ./bmc.py "$1" "$2" 0
