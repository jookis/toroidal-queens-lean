#!/bin/bash
# Trust checks after `lake build` (run from the repo root): prints the axioms of every theorem in scripts/theorems.txt
# (light libraries; --heavy adds the QueensLeanHeavy ones, which must be built first), then runs scripts/leankit.py:
# no sorry/admit/native_decide/axiom/unsafe in the sources, only propext, Classical.choice, Quot.sound in the axioms,
# every theorem of the main files printed, the spec's sanity boards recomputed by an independent Python version.
# The last line is "leankit: PASS" or "leankit: FAIL (k problems)"; exit status follows it.
set -o pipefail; cd "$(dirname "$0")/.." || exit 1; O=.lake/checks; mkdir -p $O
HEAVY=0; [ "$1" = --heavy ] && HEAVY=1
{ echo "import QueensLean"; echo "import SecondLean"; [ $HEAVY = 1 ] && echo "import QueensLeanHeavy"
  grep -v '^#' scripts/theorems.txt | awk -v h=$HEAVY 'NF==1 {print "#print axioms " $1} NF==2 && $1=="heavy" && h==1 {print "#print axioms " $2}'
} > $O/Axioms.lean
echo "printing axioms of $(grep -c '^#print' $O/Axioms.lean) theorems"
lake env lean $O/Axioms.lean > $O/axioms.out 2>&1 || { tail -20 $O/axioms.out; echo "leankit: FAIL (axioms file did not compile)"; exit 1; }
python3 scripts/leankit.py all scripts/leankit.cfg
