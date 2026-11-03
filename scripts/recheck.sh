#!/bin/bash
# Independent re-checks of a built copy of this repo (run from the repo root after `lake build`):
#   scripts/recheck.sh leanchecker   Lean's kernel replays every module of QueensLean and SecondLean from the .olean
#                                    files (import-only roots skipped: their modules are checked one by one)
#   scripts/recheck.sh nanoda        lean4export writes every light theorem of scripts/theorems.txt with everything it
#                                    uses; nanoda, an independent type checker in Rust, checks the export with only
#                                    propext, Classical.choice, Quot.sound permitted
# Binaries: leanchecker, leanexport and nanoda_bin from the toolchain's bin folder (override with LEANCHECKER,
# LEANEXPORT, NANODA). Memory: a few GB per module; nanoda on all light theorems at once about 20 GB.
cd "$(dirname "$0")/.." || exit 1; B=$(lean --print-prefix)/bin; O=.lake/checks; mkdir -p $O; fails=0
LC=${LEANCHECKER:-$B/leanchecker}; LX=${LEANEXPORT:-$B/leanexport}; ND=${NANODA:-$B/nanoda_bin}
mods() { find $1 -name '*.lean' | sed 's#/#.#g; s#\.lean$##' | sort; }
onlyimports() { ! grep -qvE '^(import |--|/-|-/|[[:space:]]*$)' "$(echo $1 | tr . /).lean"; }
case "$1" in
leanchecker)
  for m in $(mods QueensLean) $(mods SecondLean); do
    onlyimports $m && { echo "skip $m (only imports)"; continue; }
    if lake env $LC $m > $O/lc.out 2>&1; then echo "ok   $m"; else echo "FAIL $m: $(tail -2 $O/lc.out | tr '\n' ' ')"; fails=$((fails+1)); fi
  done;;
nanoda)
  names=$(grep -v '^#' scripts/theorems.txt | awk 'NF==1 {print $1}' | tr '\n' ' ')
  lake env $LX QueensLean SecondLean -- $names > $O/light.ndjson || { echo "FAIL export"; exit 1; }
  python3 -c "import json,sys; print(json.dumps({'export_file_path': sys.argv[1], 'use_stdin': False, 'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'], 'unpermitted_axiom_hard_error': False, 'nat_extension': True, 'string_extension': True, 'print_success_message': True}))" $O/light.ndjson > $O/nanoda.json
  $ND $O/nanoda.json | tee $O/nanoda.out; grep -q "no typechecker errors" $O/nanoda.out || fails=1;;
*) echo "usage: scripts/recheck.sh leanchecker|nanoda"; exit 2;;
esac
echo "recheck $1: $([ $fails = 0 ] && echo PASS || echo "FAIL ($fails)")"; [ $fails = 0 ]
