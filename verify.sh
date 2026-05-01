#!/usr/bin/env bash
# verify.sh — canonical verification of the headline Maynard `M_{105} > 4`
# theorem against a fresh build.
#
# Usage:  ./verify.sh
#
# Does:
#   1. Clean rebuild (`make clean && make -j`).
#   2. `Print Assumptions Cert.maynard_M105_certified`.
#
# Expected output: only Rocq's standard `PrimInt63.*` / `Uint63Axioms.*`
# primitive-integer interface (the unavoidable footprint of any
# `vm_compute`-driven proof in modern Rocq). No project-specific axioms.
#
# Wall-clock: ~37 min on a multi-core machine, ~80 min sequential.

set -e
cd "$(dirname "$0")"

if [ ! -f Makefile ]; then
  coq_makefile -f _CoqProject -o Makefile
fi

echo "=== Clean rebuild ==="
make clean
make -j

echo
echo "=== Print Assumptions maynard_M105_certified ==="
coqtop -Q theories/S1 PrimeGapS1 \
  -l theories/S1/Cert.v -batch \
  -e 'Print Assumptions maynard_M105_certified.'

echo
echo "Verification complete."
