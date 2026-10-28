#!/bin/sh
# Build every example, compile the generated Haskell (auto mode), compare with Lean-native values.
# Needs lake and ghc on PATH; if Lean's bundled clang shadows the system one, GHC's C step fails.
set -e
cd "$(dirname "$0")/.."
lake build Examples bench fusion autofusion combinators combinators-plain structs ints arrays arrays2 >/dev/null
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

# Every fusible combinator: plain Lean, rewritten Lean and Haskell must agree, test by test.
ghc_ bench CombMain CombMain.hs
for i in 0 1 2 3 4 5 6; do
  want=$(.lake/build/bin/combinators-plain 100000 $i)
  for got in "$(.lake/build/bin/combinators 100000 $i)" "$(build/CombMain 100000 $i)"; do
    [ "$got" = "$want" ] || { echo "FAIL combinators t$((i+1)): $got vs $want"; exit 1; }
  done
done
echo "ok combinators (length sum take append foldr any all zip, plain = rewritten = Haskell)"

# Structures, nested structures, an enum, a recursive tree and Option: Lean and Haskell agree.
ghc_ bench StructsMain StructsMain.hs
for n in 1000 100000; do
  [ "$(.lake/build/bin/structs $n)" = "$(build/StructsMain $n)" ] || { echo "FAIL structs n=$n"; exit 1; }
done
echo "ok structs (record loop, nested record, enum, tree, Option)"

# Fixed-width integers and Char: wrapping, shifts past the width, division by zero, conversions.
ghc_ bench IntsMain IntsMain.hs
for n in 1000 123457; do
  [ "$(.lake/build/bin/ints $n)" = "$(build/IntsMain $n)" ] || { echo "FAIL ints n=$n"; exit 1; }
done
echo "ok ints (UInt8/16/32/64, USize, Char)"

# Arrays: sieve, in-place prefix sums, map/fold, swaps, stack, and the list/array conversions.
ghc_ bench ArraysMain ArraysMain.hs
ghc_ bench Arrays2Main Arrays2Main.hs
for n in 1000 100000; do
  [ "$(.lake/build/bin/arrays $n)" = "$(build/ArraysMain $n)" ] || { echo "FAIL arrays n=$n"; exit 1; }
done
for n in 10 1000 20000; do
  [ "$(.lake/build/bin/arrays2 $n)" = "$(build/Arrays2Main $n)" ] || { echo "FAIL arrays2 n=$n"; exit 1; }
done
echo "ok arrays (persistent Baker arrays match Lean)"
