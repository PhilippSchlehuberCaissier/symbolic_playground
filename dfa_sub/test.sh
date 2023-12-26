#!/bin/bash

rm out.dot.pdf
./cmake-build-debug/ltlf2dfa $1 2> out.dot
dot -Tpdf -O out.dot
evince out.dot.pdf
