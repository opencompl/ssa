#!/usr/bin/env sh
set -e
set -o xtrace
rm generated* || true # don't error if no files are removed
./llvm.py
cd ../../ && (rm generated * || true) && lake build ssaLLVMEnumerator
../../build/bin/ssaLLVMEnumertor
csvdiff generated-llvm-optimized-data.csv
