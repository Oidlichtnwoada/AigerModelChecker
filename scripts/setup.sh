#!/bin/bash
sudo apt update && sudo apt install python3.8 python3.8-dev cython
cd ../picosat && ./configure && make clean && ./configure && make
cd ../aiger && ./configure && make clean && ./configure && make
cd ../minisat/core && make clean && make
cd ../simp && make clean && make
cd ../../src
cython ./bmc.py -3 --embed

