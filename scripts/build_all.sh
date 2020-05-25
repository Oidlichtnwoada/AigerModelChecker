#!/bin/bash
cd ../picosat && ./configure && make clean && ./configure && make
cd ../aiger && ./configure && make clean && ./configure && make
cd ../minisat/core && make clean && make
cd ../simp && make clean && make
