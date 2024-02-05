#!/usr/bin/env sh
set -e
set -o xtrace
rm generated* || true # don't error if no files are removed
./llvm.py
(cd ../../ && (rm generated* || true) && lake build ssaLLVMEnumerator)
../../.lake/build/bin/ssaLLVMEnumerator
diff generated-llvm-optimized-data.csv generated-ssa-llvm-semantics.csv
