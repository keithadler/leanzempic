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

Update (2026-10-29, branch `agent-cf`): `const_fold` retires 19.7 G instructions instead of 26.5 G (native 16.5 G, so 1.19x instead of 1.59x); `unionfind` 29.0 G instead of 31.2 G; the other rows are within 1% in instructions. The reason `const_fold` was high: its packed answer overflows `Word` at the last multiply, so auto mode runs the whole word version (10.5 G) and then the exact one; see `BENCH.md`, section "const_fold".

Update (2026-10-29): after the narrow-integer array work on branch `agent-perf2`, `qsort` is 1.58x (default) and 1.61x (recommended) of native instead of 2.84x and 2.82x; see `BENCH.md`. The other rows are unchanged within noise. The table above is the earlier measurement.

Update (2026-10-29, hoisted buffers and typed pairs): `qsort` retires 14.7 G instructions against native's 15.1 G (was 22.0 G) and runs in 0.89 s against 0.80 s (was 1.29 s); unionfind 1.35 s against native 1.54 s; the other rows are unchanged in instructions. See `BENCH.md`.

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

Update (2026-10-29, commit fa71371, all seven programs remeasured together, best of 3; this replaces the tables above):

| program | n | native wall s (CPU) | default wall s (CPU), ratio | recommended wall s (CPU), ratio | peak MB native / default / recommended | output identical |
|---|---|---|---|---|---|---|
| [binarytrees](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/binarytrees.lean) | 19 | 1.19 (1.18) | 0.87 (0.85), 0.73x | 0.87 (0.85), 0.73x | 35 / 174 / 292 | yes |
| [const_fold](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/const_fold.lean) | 500 | 1.29 (1.29) | 1.09 (1.09), 0.84x | 1.09 (1.08), 0.84x | 8 / 167 / 323 | yes |
| [deriv](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/deriv.lean) | 10 | 0.62 (0.60) | 0.71 (0.70), 1.15x | 0.65 (0.63), 1.05x | 549 / 569 / 785 | yes |
| [qsort](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/qsort.lean) | 300 | 0.79 (0.79) | 0.90 (0.88), 1.14x | 0.90 (0.88), 1.14x | 3 / 138 / 268 | yes |
| [rbmap](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/rbmap.lean) | 2000000 | 0.97 (0.96) | 0.38 (0.36), 0.39x | 0.36 (0.34), 0.37x | 95 / 237 / 365 | yes |
| [rbmap_checkpoint](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/rbmap_checkpoint.lean) | 2000000 | 1.04 (1.03) | 0.66 (0.64), 0.63x | 0.60 (0.58), 0.58x | 366 / 514 / 653 | yes |
| [unionfind](https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/unionfind.lean) | 3000000 | 1.52 (1.51) | 1.37 (1.35), 0.90x | 1.32 (1.30), 0.87x | 134 / 370 / 757 | yes |

load averages at the start of each program's runs (1/5/15 min): binarytrees 2.6/4.3/7.5; const_fold 2.5/4.2/7.4; deriv 2.4/4.1/7.3; qsort 2.4/4.1/7.3; rbmap 2.5/4.1/7.2; rbmap_checkpoint 2.4/4.0/7.2; unionfind 2.3/3.9/7.1

instructions retired (billions), the minimization target; ratio is against native Lean:

| program | native | default, ratio | recommended, ratio |
|---|---|---|---|
| binarytrees | 19.65 | 11.62, 0.59x | 11.43, 0.58x |
| const_fold | 16.54 | 19.60, 1.18x | 19.43, 1.18x |
| deriv | 10.60 | 9.34, 0.88x | 8.34, 0.79x |
| qsort | 15.11 | 14.56, 0.96x | 14.61, 0.97x |
| rbmap | 22.32 | 6.39, 0.29x | 6.08, 0.27x |
| rbmap_checkpoint | 22.38 | 10.41, 0.46x | 9.08, 0.41x |
| unionfind | 35.86 | 27.32, 0.76x | 26.05, 0.73x |

Update (2026-10-29, branch `agent-mem`, peak memory): the memory columns above are unchanged, because the defaults are
unchanged (`-A128m` default, `-A256m -O1g` recommended). The diagnosis: peak resident is the allocation area `-A`
plus live data plus, under `-O1g`, promoted garbage that is not collected before 1 GB. `qsort` has 0.06 MB live and
peaks at 268 MB = 256 MB + 12 MB; `deriv` has nearly everything live and no smaller `-A` is free for it. A smaller area
costs instructions only where live data is large, so there is no single value that keeps all seven programs
within 3%. New opt-in preset `ZEMPIC_RTS=lowmem` in `tools/zghc` (`-A64m -O1g`), recommended build, best of 3
(`bench/realworld/rts.py`):

| program | peak MB, recommended | peak MB, lowmem | instructions retired (G), recommended | instructions (G), lowmem |
|---|---|---|---|---|
| binarytrees | 292 | 109 | 11.48 | 11.55 (+0.6%) |
| const_fold | 323 | 89 | 19.46 | 20.04 (+3.0%) |
| deriv | 785 | 505 | 8.36 | 9.68 (+15.8%) |
| qsort | 268 | 73 | 14.66 | 14.55 (-0.8%) |
| rbmap | 365 | 167 | 6.11 | 6.00 (-1.8%) |
| rbmap_checkpoint | 653 | 445 | 9.11 | 9.01 (-1.1%) |
| unionfind | 757 | 570 | 26.06 | 26.66 (+2.3%) |

Native peak MB for reference: 35, 8, 549, 3, 95, 366, 134. With `lowmem` the ratio to native is 3.1x, 11x, 0.92x,
24x, 1.8x, 1.2x and 4.3x (recommended: 8.3x, 40x, 1.4x, 89x, 3.8x, 1.8x and 5.6x). `deriv` is why it is not the
default. List fusion as a default and `-A256m -O1g` as a default were also evaluated over 23 garden programs and
rejected; the data, and every RTS option tried (`-O`, `-F`, `-n`, `-xn`, `-c`, `-G3`, `-H`), is in `BENCH.md`,
"Peak memory".
