#!/bin/bash
sudo apt update && sudo apt install pypy3
cd ../picosat && ./configure && make clean && ./configure && make
cd ../aiger && ./configure && make clean && ./configure && make
cd ../minisat/core && make clean && make
cd ../simp && make clean && make
cd ../../minisat_proof && make clean && make
