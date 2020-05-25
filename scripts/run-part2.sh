#!/bin/bash
./update_minisat.sh
./aigtoaig ./part2/binary/"$1".aig ./part2/ascii/"$1".aag
python3.8 ./bmc.py "$1" 0 1
