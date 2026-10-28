#!/bin/sh
# Build every example, compile the generated Haskell (auto mode), compare with Lean-native values.
# Needs lake and ghc on PATH; if Lean's bundled clang shadows the system one, GHC's C step fails.
set -e
cd "$(dirname "$0")/.."
lake build Examples bench fusion autofusion >/dev/null
mkdir -p build/o
ghc_() { (cd "$1" && ghc -O2 -i../runtime -i../build -outputdir ../build/o -o ../build/$2 $3 >/dev/null); }

ghc_ tests t Main.hs
expected="2432902008176640000
50000005000000
111
15511210043330985984000000"
out=$(build/t)
[ "$out" = "$expected" ] && echo "ok examples (incl. exact fallback: 25! is $(echo "$out" | tail -1))" || { echo "FAIL examples"; echo "$out"; exit 1; }

ghc_ bench FusionMain FusionMain.hs
ghc_ bench AutoMain AutoMain.hs
want=$(.lake/build/bin/fusion lean 100000)
for w in lean fused; do
  got=$(build/FusionMain $w 100000)
  [ "$got" = "$want" ] && echo "ok fusion $w" || { echo "FAIL fusion $w: $got vs $want"; exit 1; }
done
want=$(.lake/build/bin/autofusion 100000)
got=$(build/AutoMain 100000)
[ "$got" = "$want" ] && echo "ok autofusion" || { echo "FAIL autofusion: $got vs $want"; exit 1; }
grep -q zMap build/AutoFusion/Fast.hs && grep -q zFoldl build/AutoFusion/Fast.hs && echo "ok autofusion rewrote the pipeline"
