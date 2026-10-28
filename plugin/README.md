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

## Recommendation

Do not build the rest of this yet. The case for a plugin would be things Haskell source cannot
say, not things it already says well:

* Attach strictness, arity and unfolding information to `Id`s directly. Lean is strict, so every
  argument is known strict. But GHC's own demand analysis already finds this in every benchmark
  here (loops allocate 61 KB), so the gain is unproven.
* Join points as real `JoinId`s. GHC already turns tail-called local functions into joins.
* Typed casts for the `Any` values with a plugin-provenance coercion instead of `unsafeCoerce`.
  Same cost at run time.

A better next experiment than finishing the printer: use a plugin only to set demand signatures on
a benchmark GHC currently does not unbox (the array and string loops), and measure. If that moves
a number, the plugin earns its place; if not, the Haskell route is the product.
