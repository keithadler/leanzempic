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
* A GHC Core plugin spike (`plugin/`), which showed no speedup and is not part of the product.

### Changed
* The ownership analysis tracks constructor-cell nesting to depth 12 (was 3), so loops with many
  mutable variables get in-place array updates.

### Known limitations
See the README: no `IO`, `Float`, `Int`, `ByteArray` or string-position API; arrays are slower than
Lean's at large sizes; the ownership analysis is tested, not proved; Lean 4.29.x only; not thread safe.
