#!/bin/bash
./update_minisat.sh
./aigtoaig ./part1/binary/"$1".aig ./part1/ascii/"$1".aag
python3.8 ./bmc.py "$1" "$2" 0
