#!/bin/bash
../aiger/aigtoaig ../models/"$1".aig ../models/"$1".aag
cd ../src || exit
python3.8 ./bmc.py "$1" "$2" 0
