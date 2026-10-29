#!/bin/sh
# Reproduce the real-world comparison.  Needs: lake build done at the repo root, GHC 9.14.1, Python 3.
# Source files come from upstream/ (fetched from leanprover/lean4 at f72c35b3, see RESULTS.md); src/ is
# generated from them by adapt.py.  Quiet machine recommended; REPS=5 runs per variant, interleaved.
set -e
cd "$(dirname "$0")"
python3 adapt.py
python3 run.py build "$@"          # records OK / EMIT / GHC failures in out/status.json
python3 verify.py                  # decode packed answers and compare with upstream's expected output
REPS=${REPS:-5} python3 run.py bench "$@"
python3 report.py
