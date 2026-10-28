#!/bin/sh
# usage: bench/build.sh Main|FusionMain|AutoMain  -> build/<name>
# Run with the system PATH, not Lean's bundled clang (GHC's C step needs system headers).
set -e
cd "$(dirname "$0")"
mkdir -p ../build/ob
ghc -O2 -i../runtime -i../build -outputdir ../build/ob -rtsopts "-with-rtsopts=-A128m" \
  -o ../build/$1 $1.hs >/dev/null
