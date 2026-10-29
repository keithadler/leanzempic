# Changelog

All notable changes. The project follows semantic versioning once it has a release; until then
everything is pre-release (`0.1.0`).

## Unreleased (0.1.0)

First complete version.

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
