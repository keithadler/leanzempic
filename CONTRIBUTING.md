# Contributing

Thanks for looking. leanzempic is a one-person project; small, well-tested changes are the easiest
to review.

## Setup

* Lean 4.29.1 (the version in `lean-toolchain`; elan installs it), GHC 9.14.1, Cabal, Python 3.
* Build and test everything: `PATH=...:$HOME/.elan/bin sh tests/run.sh` (see the README for the
  `PATH` caveat about Lean's bundled clang, or use `tools/zghc`).

## Ground rules

1. **A change that touches generated code needs a test that compares with native Lean.** Add a
   program under `examples/`, a driver under `bench/`, and a check in `tests/run.sh`. Comparisons go
   through `eq`, which rejects empty output (twice a failed build looked like a pass).
2. **Show that the test can fail.** For anything that guards a safety property (ownership, buffer
   sharing, integer semantics), break the code on purpose and confirm the tests catch it.
3. **Measure before optimizing.** Several planned optimizations turned out unnecessary after a
   micro-benchmark showed where the time really went. Put the numbers in `BENCH.md`, including losses.
4. **Lean code style:** no `sorry`, every definition documented, lines at most 100 characters, clean
   `lint` (Lean Studio's `style_check`, `lint`, `lean_linter`), and `verify` (Tenet) passing.
5. **Do not edit generated regions** of the runtime by hand; change `tools/gen_runtime.py` and rerun it.
6. **No claims without evidence.** If a result was not measured or tested, say so.

## The garden, and building the way CI does

* **Add a garden program for every new language feature.** `garden/programs.py` holds small Lean
  programs defining `entry : Nat → Nat`; `python3 garden/run.py [name ...]` compares each with native
  Lean. The garden found a crash that appeared only under GHC optimization, so test at `-O1` or
  higher (`GARDEN_OPT=-O1`), never only `-O0`.
* **Build the Cabal package before you push a runtime change:** `cd runtime && cabal build`. It uses
  Haskell2010 (CI builds it that way), which rejects code that a direct `ghc` run accepts, such as a
  local helper with an inferred constraint that needs a type signature.
* **Mirror CI locally:** `GARDEN_SET=ci GARDEN_OPT=-O1 GARDEN_FUSE=1 sh tests/run.sh`.
* **Run one benchmark at a time.** `garden/perf.py` compiles with GHC and Lean's C compiler and
  caps each run at 20 seconds; do not run several sweeps at once on a laptop.

## Adding support for a Lean constant

See "Developing" in the README (add a row to `prims`, implement it in the runtime, test it).

## Reporting a bug

Include the Lean version, the `#zempic` command, the smallest program that shows it, and whether
`set_option zempic.own false` changes the result (it narrows the cause quickly). A wrong answer is
more important than a crash, and a crash is more important than slowness.
