#!/bin/bash
git submodule update --init --recursive
sudo apt update && sudo apt install pypy3 zlib1g-dev -y
cd ../picosat && ./configure && make clean && ./configure && make
cd ../aiger && ./configure && make clean && ./configure && make
cd ../minisat/core && make clean && make
cd ../simp && make clean && make
cd ../../minisat_proof && make clean && make
