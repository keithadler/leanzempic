#!/bin/sh
# usage: bench/build.sh Main|FusionMain|ArraysMain|...  [output name]  -> build/<name>
# ZEMPIC_RTS overrides the RTS options baked in (default -A128m).
# Run with the system PATH, not Lean's bundled clang (GHC's C step needs system headers).
set -e
cd "$(dirname "$0")"
mkdir -p ../build/ob
ghc -O2 -i../runtime -i../build -outputdir ../build/ob -rtsopts "-with-rtsopts=${ZEMPIC_RTS:--A128m}" \
  -o ../build/${2:-$1} $1.hs >/dev/null
