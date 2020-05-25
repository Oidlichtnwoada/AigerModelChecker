#!/bin/bash
../aiger/aigtoaig ../models/"$1".aig ../models/"$1".aag
cd ../src
python3.8 ./bmc.py "$1" 0 1
