#!/bin/sh
# Build the examples (writes build/Examples.hs), compile with GHC, check results.
set -e
cd "$(dirname "$0")/.."
lake build Examples
mkdir -p build/o
(cd tests && ghc -O2 -i../runtime -i../build -outputdir ../build/o -o ../build/t Main.hs >/dev/null)
out=$(build/t)
expected="2432902008176640000
50000005000000
111"
[ "$out" = "$expected" ] && echo "ok" || { echo "FAIL"; echo "$out"; exit 1; }
