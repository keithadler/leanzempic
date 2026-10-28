#!/bin/sh
# Build every example, compile the generated Haskell (auto mode), compare with Lean-native values.
# Needs lake and ghc on PATH; if Lean's bundled clang shadows the system one, GHC's C step fails.
set -e
cd "$(dirname "$0")/.."
# Equal and non-empty: two failed builds must not look like agreement.
eq() { [ -n "$1" ] && [ "$1" = "$2" ]; }
lake build Examples bench fusion autofusion combinators combinators-plain structs ints arrays arrays2 strings generics aliasing stralias >/dev/null
mkdir -p build/o
ghc_() { (cd "$1" && ghc -O2 -i../runtime -i../build -outputdir ../build/o -o ../build/$2 $3 >/dev/null); }

ghc_ tests t Main.hs
expected="2432902008176640000
50000005000000
111
15511210043330985984000000"
out=$(build/t)
eq "$out" "$expected" && echo "ok examples (incl. exact fallback: 25! is $(echo "$out" | tail -1))" || { echo "FAIL examples"; echo "$out"; exit 1; }

ghc_ bench FusionMain FusionMain.hs
ghc_ bench AutoMain AutoMain.hs
want=$(.lake/build/bin/fusion lean 100000)
for w in lean fused; do
  got=$(build/FusionMain $w 100000)
  eq "$got" "$want" && echo "ok fusion $w" || { echo "FAIL fusion $w: $got vs $want"; exit 1; }
done
want=$(.lake/build/bin/autofusion 100000)
got=$(build/AutoMain 100000)
eq "$got" "$want" && echo "ok autofusion" || { echo "FAIL autofusion: $got vs $want"; exit 1; }
grep -q zMap build/AutoFusion/Fast.hs && grep -q zFoldl build/AutoFusion/Fast.hs && echo "ok autofusion rewrote the pipeline"

# Every fusible combinator: plain Lean, rewritten Lean and Haskell must agree, test by test.
ghc_ bench CombMain CombMain.hs
for i in 0 1 2 3 4 5 6; do
  want=$(.lake/build/bin/combinators-plain 100000 $i)
  for got in "$(.lake/build/bin/combinators 100000 $i)" "$(build/CombMain 100000 $i)"; do
    eq "$got" "$want" || { echo "FAIL combinators t$((i+1)): $got vs $want"; exit 1; }
  done
done
echo "ok combinators (length sum take append foldr any all zip, plain = rewritten = Haskell)"

# Structures, nested structures, an enum, a recursive tree and Option: Lean and Haskell agree.
ghc_ bench StructsMain StructsMain.hs
for n in 1000 100000; do
  eq "$(.lake/build/bin/structs $n)" "$(build/StructsMain $n)" || { echo "FAIL structs n=$n"; exit 1; }
done
echo "ok structs (record loop, nested record, enum, tree, Option)"

# Fixed-width integers and Char: wrapping, shifts past the width, division by zero, conversions.
ghc_ bench IntsMain IntsMain.hs
for n in 1000 123457; do
  eq "$(.lake/build/bin/ints $n)" "$(build/IntsMain $n)" || { echo "FAIL ints n=$n"; exit 1; }
done
echo "ok ints (UInt8/16/32/64, USize, Char)"

# Arrays: sieve, in-place prefix sums, map/fold, swaps, stack, and the list/array conversions.
ghc_ bench ArraysMain ArraysMain.hs
ghc_ bench Arrays2Main Arrays2Main.hs
for n in 1000 100000; do
  eq "$(.lake/build/bin/arrays $n)" "$(build/ArraysMain $n)" || { echo "FAIL arrays n=$n"; exit 1; }
done
for n in 10 1000 20000; do
  eq "$(.lake/build/bin/arrays2 $n)" "$(build/Arrays2Main $n)" || { echo "FAIL arrays2 n=$n"; exit 1; }
done
echo "ok arrays (persistent Baker arrays match Lean)"

# Strings: push, append, decimals, comparison, list conversion, non-ASCII byte sizes.
ghc_ bench StringsMain StringsMain.hs
for n in 10 1000 20000; do
  eq "$(.lake/build/bin/strings $n)" "$(build/StringsMain $n)" || { echo "FAIL strings n=$n"; exit 1; }
done
echo "ok strings (shared UTF-8 buffer matches Lean, incl. non-ASCII)"

# Generic data (Pair, Box, Option, MProd) through out-of-line generic functions at several types.
ghc_ bench GenericsMain GenericsMain.hs
for n in 10 1000 20000; do
  eq "$(.lake/build/bin/generics $n)" "$(build/GenericsMain $n)" || { echo "FAIL generics n=$n"; exit 1; }
done
echo "ok generics (polymorphic data keeps one layout across instantiations)"

# Core plugin spike: Lean writes a stub and an s-expression; the plugin injects real Core;
# -dcore-lint checks it; the answers must match the Haskell route's.
if command -v cabal >/dev/null 2>&1; then
  lake build CoreSpike >/dev/null
  (cd plugin && cabal build --offline >/dev/null)
  DB=$PWD/plugin/dist-newstyle/packagedb/ghc-9.14.1
  rm -rf build/oc; mkdir -p build/oc
  ghc --make -O2 -dcore-lint -package-db "$DB" -plugin-package zempic-plugin -fplugin=Zempic.Plugin \
    -fplugin-opt=Zempic.Plugin:build/CoreSpike.zc -iruntime -ibuild -ispike -outputdir build/oc \
    -o build/corespike spike/CoreSpikeMain.hs >/dev/null
  got="$(build/corespike fact 20) $(build/corespike sum 10000000) $(build/corespike collatz 27)"
  [ "$got" = "2432902008176640000 50000005000000 111" ] && echo "ok core plugin (injected Core passes Core Lint, answers match)" \
    || { echo "FAIL core plugin: $got"; exit 1; }
fi

# Ownership analysis: in-place array updates must never change a program's meaning. These programs
# update arrays while other references to them are live; every sharing pattern must match Lean.
ghc_ bench AliasingMain AliasingMain.hs
for n in 0 1 2 3 10 11 1000 4097; do
  eq "$(.lake/build/bin/aliasing $n)" "$(build/AliasingMain $n)" || { echo "FAIL aliasing n=$n"; exit 1; }
done
grep -q "arrSetU\|arrPushU" build/Aliasing/Fast.hs || { echo "FAIL: analysis chose no in-place update"; exit 1; }
echo "ok aliasing (ownership analysis keeps shared arrays intact)"

# String buffer sharing: pushing to an old version, appending a string to itself, literals,
# growth across the starting capacity with multi-byte characters, snapshots, comparisons.
ghc_ bench StrAliasMain StrAliasMain.hs
for n in 0 1 5 17 59 1000 123457; do
  eq "$(.lake/build/bin/stralias $n)" "$(build/StrAliasMain $n)" || { echo "FAIL stralias n=$n"; exit 1; }
done
echo "ok string aliasing (versions sharing a buffer never disturb each other)"

# Model-based randomized tests of the runtime (arrays, strings, integers, Nat fast path vs exact).
mkdir -p build/pt
ghc -O1 -iruntime -outputdir build/pt tests/PropTests.hs -o build/proptests >/dev/null
for seed in 1 2 3 4 5 6 7 8; do
  out=$(build/proptests $seed 3 2>&1)
  case "$out" in *"all properties held"*) ;; *) echo "FAIL proptests seed $seed"; echo "$out" | head -8; exit 1;; esac
done
echo "ok proptests (8 seeds of random operation sequences against pure models)"

# Differential fuzzing: random Lean programs must give the same answers under Lean and leanzempic.
# (A short run here; run more seeds with `python3 tools/fuzz.py FIRST COUNT FUNCTIONS`.)
if command -v python3 >/dev/null 2>&1; then
  python3 tools/fuzz.py 1 4 8 >/tmp/fuzz.out 2>&1 || { cat /tmp/fuzz.out; echo "FAIL fuzz"; exit 1; }
  echo "ok fuzz ($(tail -1 /tmp/fuzz.out))"
fi
