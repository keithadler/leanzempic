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

# Fusion pipeline: Lean-native value must match Haskell value in both modes.
lake build fusion >/dev/null
want=$(.lake/build/bin/fusion lean 100000)
for m in natural word; do
  mkdir -p build/of-$m
  (cd bench && ghc -O2 -i../runtime -i../runtime/$m -i../build -outputdir ../build/of-$m -o ../build/fusion-$m FusionMain.hs >/dev/null)
  for w in lean fused; do
    got=$(build/fusion-$m $w 100000)
    [ "$got" = "$want" ] && echo "ok fusion $m $w" || { echo "FAIL fusion $m $w: $got vs $want"; exit 1; }
  done
done

# Auto-fusion: plain Lean list code + `set_option zempic.fuse true`.
lake build autofusion >/dev/null
want=$(.lake/build/bin/autofusion 100000)
for m in natural word; do
  mkdir -p build/oa-$m
  (cd bench && ghc -O2 -i../runtime -i../runtime/$m -i../build -outputdir ../build/oa-$m -o ../build/auto-$m AutoMain.hs >/dev/null)
  got=$(build/auto-$m 100000)
  [ "$got" = "$want" ] && echo "ok autofusion $m" || { echo "FAIL autofusion $m: $got vs $want"; exit 1; }
done
grep -q "zMap" build/AutoFusion.hs && grep -q "zFoldl" build/AutoFusion.hs && echo "ok autofusion rewrote the pipeline"
