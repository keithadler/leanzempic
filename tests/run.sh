#!/bin/sh
# Build the examples (writes build/Examples.hs), compile with GHC in both Nat modes, check results.
# Needs lake and ghc on PATH; if Lean's bundled clang shadows the system one, GHC's C step fails.
set -e
cd "$(dirname "$0")/.."
lake build Examples
expected="2432902008176640000
50000005000000
111"
for m in natural word; do
  mkdir -p build/o-$m
  (cd tests && ghc -O2 -i../runtime -i../runtime/$m -i../build -outputdir ../build/o-$m -o ../build/t-$m Main.hs >/dev/null)
  out=$(build/t-$m)
  [ "$out" = "$expected" ] && echo "ok $m" || { echo "FAIL $m"; echo "$out"; exit 1; }
done
