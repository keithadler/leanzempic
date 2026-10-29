# Real-world comparison: leanzempic vs Lean's C backend

Five well-known third-party Lean 4 programs (plus one bonus), taken unmodified from the Lean compiler's own
benchmark suite, compiled both ways and timed. Includes the failures.

## Method

* **Source:** `https://github.com/leanprover/lean4`, tag `v4.29.1` (this repo's `lean-toolchain`), commit
  `f72c35b3f637c8c6571d353742168ab66cc22c00`, directory `tests/bench/`. Files fetched with curl from
  raw.githubusercontent.com into `upstream/` (treated as data, each read before compiling), with their
  `.lean.args` / `.lean.expected.out` files. Nothing else was downloaded.
* **Adapters:** leanzempic cannot compile `IO`, `Task` or `main`. `adapt.py` keeps everything before
  upstream's `main` verbatim and appends a pure `entry : Nat -> Nat` that computes the same values and packs
  them into one Nat (base 2^40 digits). The same `src/<name>.lean` feeds both sides: native Lean gets a tiny
  `main` that prints `entry n`. `verify.py` decodes the packed answer at upstream's own argument and checks it
  against upstream's `expected.out` (all OK; nat_repr has no upstream expected file). Adapter changes per program:
  * binarytrees: `Task.spawn` replaced by a direct call (single-threaded; native upstream is parallel).
  * deriv: the `IO` `nest`/`deriv` chain replaced by a pure fold of the per-step counts.
  * qsort: IO loops replaced by pure loops that count sorted arrays; `set_option pp.all true` removed.
  * unionfind, nat_repr: only the `main` plumbing.
  * const_fold: depth fixed at 15 and the work repeated `n` times with a different leaf seed. Reason: native
    Lean overflows its 8 MB stack above depth 16 (even 64 MB at depth 20), and depth 15 runs in about 5 ms, so
    a single tree cannot be timed. `n=1` reproduces upstream's answer. This changes the workload; it is a
    repetition of upstream's, not upstream's.
* **Native:** `lean -c` then `leanc -O3` (Lean's own clang), as `garden/perf.py` does.
* **leanzempic default:** no fusion, `ghc -O2 -with-rtsopts=-A128m`. **Recommended:** `set_option zempic.fuse true`
  before the definitions, `-A256m -O1g` (exactly what `docs/refresh_chart.py` builds).
* **Timing:** `python3 run.py bench`: 5 runs of each variant, interleaved (native, default, recommended, repeat),
  best wall seconds reported, with the CPU time (user+sys) of the best-CPU run and peak resident set from
  `/usr/bin/time -l` (maximum over the 5 runs). Sizes chosen so native Lean takes 0.6 to 1.6 s. Outputs of all
  5 runs of all three variants were compared: identical.
* **Machine:** Apple M3, macOS 27.2, GHC 9.14.1, Lean 4.29.1. The machine was NOT quiet: load average was 4.7
  to 7.2 (WindowServer, Chrome, Claude app) for the whole session. The spread within 5 runs was small (usually
  under 2%; per-run times are in `out/results.json`, not committed), so the ratios are stable, but absolute times
  carry some interference. No other benchmark was running.

## Results

| program | n | native wall s (CPU) | default wall s (CPU), ratio | recommended wall s (CPU), ratio | peak MB native / default / recommended | output identical |
|---|---|---|---|---|---|---|
| [binarytrees](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/binarytrees.lean) | 19 | 1.20 (1.19) | 0.88 (0.86), 0.73x | 0.87 (0.84), 0.72x | 35 / 174 / 292 | yes |
| [const_fold](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/const_fold.lean) | 500 | 1.30 (1.29) | 1.32 (1.32), 1.02x | 1.31 (1.29), 1.01x | 8 / 167 / 323 | yes |
| [deriv](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/deriv.lean) | 10 | 0.64 (0.62) | 0.75 (0.73), 1.17x | 0.69 (0.66), 1.08x | 549 / 569 / 785 | yes |
| [qsort](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/qsort.lean) | 300 | 0.79 (0.78) | 2.24 (2.21), 2.84x | 2.23 (2.21), 2.82x | 3 / 138 / 268 | yes |
| [unionfind](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/unionfind.lean) | 3000000 | 1.55 (1.54) | 1.82 (1.80), 1.17x | 1.80 (1.79), 1.16x | 134 / 390 / 759 | yes |
| [nat_repr](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/nat_repr.lean) | 10000 | 1.06 (1.05) | 1.35 (1.33), 1.27x | 1.37 (1.35), 1.29x | 3 / 164 / 321 | yes |

Update (2026-10-29): after the narrow-integer array work on branch `agent-perf2`, `qsort` is 1.58x (default) and 1.61x (recommended) of native instead of 2.84x and 2.82x; see `BENCH.md`. The other rows are unchanged within noise. The table above is the earlier measurement.

load averages at the start of each program's runs (1/5/15 min): binarytrees 4.7/4.8/6.7; const_fold 5.7/5.1/6.8; deriv 5.5/5.0/6.7; qsort 5.6/5.1/6.7; unionfind 5.2/5.1/6.6; nat_repr 7.2/5.5/6.8


Ratios are wall time of leanzempic over native Lean, so below 1.00x means leanzempic is faster. CPU time
tracks wall time everywhere (single-threaded on both sides).

## The failure (fixed)

**rbmap** and **rbmap_checkpoint** originally did not compile: GHC rejected `ZC_Tree_leaf -> v326_x2` ("Couldn't
match expected type 'Any' with actual type 'ZNat'"). Real cause: not a missing box in the specialization, but
`hsVariant` (the copy of a recursive function with a literal argument fixed, `z_fold_..._ux_x_0`) bound the fixed
parameter as a `ZNat` while still recording the parameter's declared type, `Any` (upstream's `fold` is
polymorphic in the accumulator), so uses of it skipped the `zo` cast. Fixed in `Zempic/Emit.lean`; the garden
program `variant_poly_const` reproduces it. Both now pass. Timings with the fix (best of 5, interleaved; machine
loaded, load average about 10, so absolute times are inflated and ratios approximate):

| program | n | native s | default s, ratio | recommended s, ratio |
|---|---|---|---|---|
| rbmap | 2000000 | 1.22 | 0.51, 0.42x | 0.51, 0.42x |
| rbmap_checkpoint | 2000000 | 1.45 | 1.11, 0.77x | 1.00, 0.69x |

Outputs identical across native, default and recommended. rbmap matches upstream's expected output at its own
argument (10000); rbmap_checkpoint has no upstream expected file, so `verify.py` checks it against upstream's own
`main` run natively at `100000 10` ("10001 10000").

Also not attempted (and not committed): `liasolver` (needs `Lean.AssocList`/`Std.HashMap`/iterators imports and reads a file),
`binarytrees` in its upstream parallel form, and the `IO`-based benchmarks, because there is no `IO`.

## Analysis

* **Wins: binarytrees (0.72x to 0.73x).** Allocation-heavy, pure, no arrays: GHC's bump allocator and copying
  collector beat Lean's allocator plus reference counting. Cost: peak memory 174 MB (292 MB recommended) against
  Lean's 35 MB. (Checked it is not an artifact: GHC could have floated `check (make d)` out of the loop, but the
  run time and ~150 M node allocations per second show every tree is built.)
* **Ties: const_fold (1.01x to 1.02x), deriv (1.08x to 1.17x), unionfind (1.16x to 1.17x).** Expression-tree rewriting,
  symbolic differentiation (Int and String) and a state-monad loop over an array land within 20% of native. Recommended
  settings help only deriv (1.17x to 1.08x); they never help much here because these programs have no list
  pipelines for fusion to remove. Memory is 1x to 20x higher than native (const_fold 8 MB vs 167 MB, mostly the
  allocation area).
* **Losses: nat_repr (1.27x to 1.29x), qsort (2.8x).** nat_repr is `Nat.repr` plus `String.length` in a
  tight loop, so string building is slower than Lean's. The recommended settings are marginally worse (1.29x).
* **Biggest loser, qsort (2.84x default, 2.82x recommended; native 0.79 s, 3 MB; leanzempic 2.24 s, 138 MB).**
  The README predicts this ("in-place arrays at scale"). Looking at the generated Haskell
  (`out/qsort/default/Out/Fast.hs`) and a run with `+RTS -s`:
  * 5.28 GB allocated in the heap, GC time under 0.01 s, so it is all mutator time, not collection.
  * Splitting the program with probes: generating the arrays costs 0.76 GB and about 2x native (0.12 s vs
    0.05 s CPU); the sort itself is about 3.8 GB, 1.96 s vs 0.70 s CPU, so the sort kernel is almost the
    whole loss.
  * The inner loop `partitionAux` calls `arrGetD erased (zo inst) arr (u32ToNat i)` per element and
    `arrSwapU` per swap: every element read goes through an `Any`-typed array, a `Word32` to `ZNat` conversion
    for the index, a re-boxed `Inhabited` default, and the `unsafeDupablePerformIO` wrapper; the partition result
    is returned as an allocated pair (`zPair`). Lean's C code does the same with an in-register UInt32,
    a tagged-scalar array slot and an unboxed in-place swap (no allocation). About 38 bytes are allocated per
    partition step, none by native Lean.
  * Fusion cannot help (there is no list), and a larger allocation area does not remove the per-access cost.
  This is a diagnosis from reading the generated code and the allocation counts; I did not try a fix (for
  example, an unboxed Word32 array path like the existing `arrGetDW`/`aPushUW` ones for Word32 arrays).

Summary: of 6 programs that compile, leanzempic is faster on 1, within 20% on 3, 27% to 29% slower on 1 and
2.8x slower on 1; 1 program of 7 tried does not compile (rbmap, plus its sibling rbmap_checkpoint). Peak memory
is higher on all six (46x on qsort, 21x on const_fold, 1.04x on deriv, default settings).
It is not a general win on real-world code; it is a win on allocation-heavy pure code, roughly neutral on
tree and monad code, and a loss on array-sorting and string-heavy loops.

## Reproduce

```sh
lake build
bench/realworld/run.sh            # adapt, build, verify, bench (about 5 minutes), print the table
```

Files: `upstream/` (fetched, unmodified), `src/` (generated by `adapt.py`), `run.py` (build and bench),
`verify.py`, `report.py`, `sizes.json` (n per program). `out/` (binaries, generated Haskell, raw results) is
git-ignored.
