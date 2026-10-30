# Changelog

All notable changes. The project follows semantic versioning once it has a release; until then
everything is pre-release (`0.1.0`).

## Unreleased

* Hoisted buffers now cover `Nat` (word mode), `USize` and `Bool` arrays, arrays inside the `MProd`/`Prod` state of
  `for` and `while` loops, arrays that reach a join point as a parameter, the copies of a loop fixed to literals, and
  functions without a loop that read or update the array in place at three or more places (`qsortAux`). Instructions
  retired against `main`: `qsort` 14.63 G to 11.43 G (-21.8%; native Lean's C 15.1 G), chart rows Sieve (Bool array)
  3.10 G to 1.71 G, Prefix sums (Nat array) 2.96 G to 1.58 G, Reverse by swaps 0.52 G to 0.49 G, Shared-array
  insertion sort 0.53 G to 0.26 G; the other real-world programs and rows change by at most 0.1%. See `BENCH.md`.
* The scan is tested: 22 deliberate edits of it were tried against the new `hoist_*` garden programs (`Nat`, `USize`
  and `Bool` variants of the old ones, and `hoist_cell_*` for arrays in loop-state cells and join points); nine give a
  wrong answer, three make a loop stop hoisting, which the new `tools/hoist_count.py --check` (in `tests/run.sh`)
  reports, and ten cannot change an answer (second lines of defense, dead code, a performance guard); see
  `SOUNDNESS.md`. New property tests `arrHoisted` for `Word` buffers and `arrHoistedBool`; six deliberate bugs in the
  new runtime functions were all detected.
* Garden: 219 programs (64 new), 52 run in CI; with fusion on (`GARDEN_FUSE=1`) all 219 agree. The README and `BENCH.md`
  said 109 for the fusion run and 36 for the CI subset; both were out of date.
* Hoisted buffers: the emitter's scan is now covered by tests that fail when it is wrong. Eleven deliberate
  edits to `hoistWalk` and `hoistPlan` were tried; six are killed by new garden programs (`hoist_push_*`,
  `hoist_pop_*`, `hoist_persist_*`, `hoist_join_*`, `hoist_twice_*`, with `hoist_shared_*`) and five cannot
  change an answer (a second line of defense, dead code, or a performance guard); see `SOUNDNESS.md`. Also
  found: `hoist_set_*`, `hoist_shared_*` and `hoist_escape_*` built their arrays with `map`, which keeps a boxed
  buffer, so the hoisted loops never ran on them; they now build by pushes and run hoisted. The garden is
  155 programs (22 new) and 48 run in CI.
* Peak memory diagnosed and an opt-in low-memory preset: `ZEMPIC_RTS=lowmem` in `tools/zghc` (`-A64m -O1g`)
  cuts peak resident memory on the seven real-world programs by 25% to 73% (for example `qsort` 268 MB to
  73 MB, `const_fold` 323 MB to 89 MB) with instructions retired within 3.0% on six of them and +15.8% on
  `deriv`. The defaults are unchanged: no smaller `-A` keeps all seven within 3%, and making list fusion or
  `-A256m -O1g` the default regresses garden programs (`list_mergesort` +9%, `closures` +15%,
  `float_math` +20%). New `bench/realworld/rts.py` sweeps RTS options over the built programs. See `BENCH.md`,
  "Peak memory".

## 0.1.0-rc3 (2026-10-29)

* The exact (`Natural`) path inlines its small-operand cases (`natAdd/Sub/Mul/Div/Mod/Eq/Lt/Le` match
  `NS` and keep the big-number work out of line) instead of calling `naturalAdd` and friends, and generated
  modules carry `-fworker-wrapper-cbv` (strict arguments arrive evaluated and tagged) unless a function
  signature mentions a fixed-width integer, where it defeats SpecConstr's unboxing (qsort +15%).
  `const_fold` 26.5 G to 19.7 G instructions retired (1.59x to 1.19x of native's 16.5 G), `unionfind` 31.2 G
  to 29.0 G; the other real-world programs are unchanged within 1%. New property test `natExactBig`.
  Cause of the 1.59x: `const_fold`'s packed answer exceeds 2^64, so the whole word run (10.5 G) is thrown
  away at the last multiply and the exact run repeats it; see `BENCH.md`.
* Loops over an unshared `UInt8/16/32/64` array resolve its buffer once (hoisted buffers) and a pair has the
  Haskell type of its components, so GHC returns pairs unboxed. `qsort` from 22.0 G to 14.7 G instructions
  retired (native 15.1 G), 1.29 s to 0.89 s; unionfind 29.8 G to 26.1 G. See `BENCH.md` and `SOUNDNESS.md`.
* Array reads and writes of a `Nat` (word mode) or `USize` element are done with no box (`arrUGetW`,
  `arrPushUW`, `arrUSetBUW`, ...), `Array.range` fills a word buffer in one pass, swaps and
  append/extract element moves no longer box, and the in-place primitives take unboxed arguments.
  The reads, pushes and writes keep their common case (a live word buffer) in line and use `runRW#` and
  `Word#` end to end; the index arguments of `aGet`/`aSet`/`aSwap`/`aSetU`/`aSwapU` are strict.
  Merged with the Prefix-sums and `array_misc` work: `array_funcs` allocation 485 MB to 321 MB (3.9x to
  2.5x of Lean's C backend), Prefix sums 1308 MB to 508 MB (3.6x to 1.7x), `array_misc` 115 MB to 0.7 MB.
  New garden program `array_word_paths`. Details and the failures along the way are in `BENCH.md`.
* `UInt8/16/32/64` and `Char` array elements are read, pushed and written in place with no box
  (`arrGetD32`, `arrUGet32`, `arrPushU32`, `arrSetU32`, ... and the 8, 16, 64 bit versions), swaps on arrays of
  a known word-like element type exchange in line (`arrSwapU32`, ...), bounds checks are one unsigned
  comparison, and buffers grow with a block copy. The real-world `qsort` (Lean's own benchmark) goes from
  2.83x to 1.58x of Lean's C backend and from 5283 MB to 1835 MB allocated. New garden program
  `array_narrow_paths`; new property test `arrNarrow`. Details, and what did not help, are in `BENCH.md`.
* `Array.map`'s placeholder write is skipped when the next write overwrites it (array map/filter/fold 5.3x to 3.9x).
* Unrolled variants use `INLINABLE`, so `string_pos` builds at `-O2`; known issue below is fixed.

## 0.1.0-rc2 (2026-10-29)

Bounded undo chains and lazy copies for shared arrays. Shared-array insertion sort: 18x (rc1) to 6.9x slower
than Lean's C backend. Garden is 109 programs (3 new).

### Known issue
* `string_pos` (garden) exceeds 6 GB of GHC heap at `-O2` (INLINE pragmas on the unrolled `opaqueFix` chain);
  it builds at `-O1`, which is what CI uses. Not fixed in this release.

### Changed
* Persistent arrays bound their undo chain: once a buffer carries as many undo records as the array has
  elements, the next write copies the buffer instead. A long-lived old version (the shared array a loop
  was started from) no longer pins millions of records, which was most of the cost of mutating a shared
  array in a loop (insertion sort of a shared array: 18x slower than Lean's C backend, now about 10x).
  The version a copy was taken from is marked so the in-place variants fall back to the persistent path.

### Added (arrays)
* Lazy copies for shared arrays. When a shared array is passed to a function that updates its parameter
  (directly or through other calls), the compiler hands over a lazy copy (`arrShare`): it reads through to
  the original and copies the buffer on its first write, which is what Lean's reference counts do. The
  callee then updates in place. A function that never writes costs nothing. Insertion sort of a shared
  array: 18x slower than Lean's C backend before, now about 8x.

### Added
* The Haskell backend: `#zempic f g to "x.hs"` prints Lean's mono-phase LCNF as Haskell shaped like
  GHC Core, with a Core-notation dump.
* Auto mode: a `Word` fast path with an exact `Natural` fallback on overflow; `word`, `exact` and
  `core` modes.
* Types: `Nat`, `Bool`, `UInt8` to `UInt64`, `USize`, `Char`, user structures, enums, trees,
  `Option`, generic data (as polymorphic Haskell types), `List`, `Prod`, `Array`, `String`.
* List fusion: `Zempic.Fuse` combinators and the `zempic.fuse` pass for ordinary list code
  (`map filter foldl foldr range length sum take append zip any all`).
* Arrays as Baker persistent arrays, with an ownership analysis (`Zempic/Own.lean`) that updates
  them in place where provably safe (`zempic.own`).
* Strings as a shared UTF-8 buffer.
* The Haskell runtime as a Cabal package (`runtime/zempic-runtime.cabal`) and `tools/zghc`.
* A check for the supported Lean version (4.29.x) and for mistyped modes, with proofs.
* Tests: 16 checks comparing with native Lean, model-based randomized tests of the runtime, a
  differential fuzzer, and mutation checks of the riskiest components. CI on macOS and Linux.
* Machine-checked facts (Tenet-verified): name mangling is injective, the `coerce` laws, the
  version and mode checks.
* An AES-256 benchmark from a proved development (`bench/aes`, checked against OpenSSL).
* A GHC Core plugin spike (`plugin/`), which showed no speedup and is not part of the product.

### Added since the first draft
* `Int` (as `Integer`), `Float` (as `Double`), `ByteArray`, `Thunk`, `Array.set`, `mixHash`, `Nat.log2`,
  `Nat.pred`, `ofNatLT`, and the string position API (`get`, `next`, `prev`, `atEnd`, `extract`,
  `set`, `pushn`, `posOf`, `offsetOfPos`, `hash`), which makes `foldl`, `map`, `splitOn`, `trim`,
  `replace` and `String.Slice` compile from Lean's own definitions.
* `garden/`: 106 small programs, one per language feature, checked against native Lean
  (`garden/run.py`, part of `tests/run.sh`), and `garden/perf.py` for timing them.

### Faster
* A swap on a persistent array is one version with one undo record (was two chained sets): an
  insertion sort on a shared array went from 0.535 s to 0.170 s.
* Strings read a character with one strict read and `appendWith` is inlined: `string_build` 0.116 s to
  0.080 s, `string_chars` 0.454 s to 0.345 s.
* Documented `-with-rtsopts='-A256m -O1g'`: 25 to 40% on list and array programs.

### Fusion
* Documented and measured: `set_option zempic.fuse true` before the definitions gives 2x to 5x on list
  pipelines (all 106 garden programs agree with it on). One program got slower (list merge sort).
* Every generated module carries `-fno-float-in`, avoiding a GHC 9.14.1 panic in the Float Inwards pass.

### Ergonomics
* `#zempic` warns when the compiled code has Lean's own list loops and `zempic.fuse` is off.
* `tools/zghc` defaults to `-A256m -O1g` (override with `ZEMPIC_RTS`).

### Tooling
* CI runs a 36-program subset of the garden at `-O1` (the full 106 take about 15 CPU-minutes and
  exceeded the runner). `GARDEN_OPT` and `GARDEN_SET` select the level and the set.

### Fixed
* A structure with one relevant field (`String.Pos`) was declared as a boxed constructor while the
  compiled code builds it as the bare field. GHC's worker/wrapper trusted the declared type and the
  program crashed at `-O1` and above (not at `-O0`).
* A primitive called with more arguments than its arity was missing parentheses around the
  saturated call.
* A type parameter used by no field is given kind `Type`, so `T Any` typechecks.

### Changed
* A self-recursive call whose `Nat` argument is a literal up to `zempic.unroll` (default 16) is
  specialized per count and unrolled, with branches on known numbers dropped; bodies over 60
  bindings (counting callees) are left alone, and each function gets at most 64 copies.
* Structure fields whose type is a reducible alias (`abbrev Byte := UInt8`) now use the aliased
  type instead of `Any`.
* The ownership analysis tracks constructor-cell nesting to depth 12 (was 3), so loops with many
  mutable variables get in-place array updates.

### Known limitations
See the README: no `IO` or `FloatArray`; arrays are slower than
Lean's at large sizes; the ownership analysis is tested, not proved; Lean 4.29.x only; not thread safe.
