# Core plugin spike

A GHC plugin that builds Core directly from Lean's compiled terms, instead of printing Haskell
for GHC to parse. This is a feasibility spike, 2026-10-28, GHC 9.14.1.

## What it does

`#zempic f g to "x.hs" mode core` writes two files:

* `x.hs`, a stub: each function is `f :: Word -> Word` with the right type and a dummy body, plus
  `p_natAdd = natAdd` bindings for the runtime primitives it calls.
* `x.zc`, an s-expression per function: `(fn name (params) code)`, with `let`, `case` on `Bool`,
  `ret`, and calls.

The plugin (`plugin/Zempic/Plugin.hs`) runs first in the Core pipeline, reads the `.zc`, builds
`Case`, `Var`, `Lit` and `App` nodes, and replaces the stubs' right-hand sides. A Lean `let` becomes
a Core `case` that binds the evaluated value, which is exactly Lean's strict evaluation.

Scope: the `Nat`/`Bool` subset, with recursion. `tests/run.sh` builds `examples/CoreSpike.lean` this
way (factorial, a sum loop, Collatz), compiles it with `-dcore-lint`, and checks the answers.

## What GHC 9.14 allows (verified)

* A Core plugin can replace a module's bindings wholesale. The Core passes Core Lint, which also
  runs after every later optimization pass, so it stays well-typed through the simplifier.
* A plugin must come from a package. Loading it from an include path fails ("Could not find
  module"). Cabal builds it offline (it needs only `base`, `ghc`, `containers`); then
  `-package-db .../packagedb/ghc-9.14.1 -plugin-package zempic-plugin -fplugin=Zempic.Plugin`.
* The plugin runs on every module of a `--make` build, so it must ignore modules without its stubs.
* The `ghc` library moved things: `GHC.Plugins` no longer has `lookupId`, and `lookupOrigIO` is
  gone. The workable trick is to bind each primitive in the stub (`p_natAdd = natAdd`) and read the
  imported `Id` off that binding's right-hand side.
* New data types still need a Haskell declaration, so the stub is not going away: Core cannot
  introduce a `TyCon`.

## What it bought: nothing measurable

| | Core plugin | Haskell source route |
|---|---|---|
| sum loop, 2e8 iterations | 0.176 s | 0.182 s |
| optimized Core | worker `$wz_sumTo` over unboxed `Word#` | the same |
| compile time (tiny module) | 1.28 s | 0.92 s |

GHC reaches the same optimized Core from either input, so the speed is identical. The plugin is
slower to compile a small module because loading the `ghc` library as a plugin costs more than the
front end it skips. It might win on very large generated modules; that was not measured.

## Experiment: would demand hints help? No.

The one thing a plugin could add that Haskell source cannot is stronger demand (strictness)
information on `Id`s. To test whether any number could move, I did not write the hint machinery
first. I measured the best case a perfect signature could reach, by making the hot array and string
primitives `INLINE` with strict arguments by hand:

| Loop (best of 3) | Before | With the best-case hints | Lean |
|---|---|---|---|
| sieve, 5e6 | 0.36 s, 1.40 GB | **0.28 s, 1.20 GB** | 0.10 s |
| prefix sums, 3e6 | 0.30 s | 0.29 s | 0.04 s |
| map and fold, 3e6 | 0.31 s | 0.29 s | 0.05 s |
| reverse with swaps, 2e6 | 0.14 s | 0.13 s | 0.04 s |
| push characters, 1e7 | 0.18 s, 1.71 GB | 0.17 s, 1.71 GB | 0.05 s |
| append decimals, 3e6 | 0.50 s, 3.86 GB | 0.49 s, 3.86 GB | 0.12 s |

The cost is structural. A bare Haskell loop calling the persistent array's `aSet` 5,000,000 times
allocates 112 bytes per call (the mutable cell, the new version, the undo record), the same figure
as the generated sieve. No signature removes that. The only visible gain, 20% on the sieve, came
from a runtime change that needs no plugin, so I kept that (inline plus strict arguments on
`arrSet`, `arrGetD`, `arrPush`, `arrUSet`) and dropped the string change, which did nothing.

## Recommendation

The Haskell source route is the product. Leave the plugin as a spike. Reasons to revisit it would
be new ones, such as a very large generated module where GHC's front end is the compile-time
bottleneck (not measured), or a Core feature Haskell cannot express. The performance gaps that
remain (arrays, strings, closure-heavy code) are allocation and ownership problems, not
information GHC is missing.
