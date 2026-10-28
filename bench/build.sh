#!/bin/sh
# usage: bench/build.sh natural|word  -> build/hsbench-<mode>
# (run with the system PATH, not Lean's bundled clang)
set -e
cd "$(dirname "$0")"
m=$1
mkdir -p ../build/ob-$m
ghc -O2 -i../runtime -i../runtime/$m -i../build -outputdir ../build/ob-$m -rtsopts "-with-rtsopts=-A128m" -o ../build/hsbench-$m Main.hs >/dev/null
