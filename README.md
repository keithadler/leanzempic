# leanzempic 🙂

A Haskell backend for Lean 4. It prints Lean's compiled terms (LCNF, mono
phase) as Haskell shaped like GHC Core, so GHC's optimizer decides the
execution order and the code generator.

Licensed under Apache-2.0. Status: v0.1, private, early. Checked with Lean Studio (`check_file`, `style_check`, `project_health`).

## Why

Lean's C backend is slow next to OCaml and Haskell on many programs. Two
reasons: reference counting on every value, and no fusion or deforestation
across function boundaries. GHC has strictness analysis, worker/wrapper,
case-of-case, and foldr/build fusion. leanzempic hands it Lean programs in a
form it can use.

## How it works

LCNF is already erased, in A-normal form, with explicit join points and Lean's
strict evaluation order. The printer keeps that structure:

| LCNF | Emitted |
|---|---|
| `let x := v` | strict binding (`let !x = v`, a `case` in Core) |
| `jp j x := ...` | local function in tail position (GHC makes it a join point) |
| `cases` | `case` on a generated `data` type, or `Bool` |
| structure `proj` | single-constructor `case` |

Two outputs per run: a compilable `.hs` module, and a `.core` text dump in
Core notation for reading. GHC cannot ingest Core text, so real Core injection
(a GHC plugin) is on the roadmap.

## Use

```lean
import Zempic
#zempic fact sumL to "build/Out.hs"
```

Compile with `ghc -O2 -iruntime -ibuild`, then `import Out`. See `tests/run.sh` for the full loop.

## Fusion

```lean
import Zempic
def pipe (n : Nat) : Nat :=
  Zempic.Fuse.foldl (· + ·) 0 (Zempic.Fuse.filter (· % 3 != 0)
    (Zempic.Fuse.map (fun x => x * x % 1000) (Zempic.Fuse.range n)))
```

Or skip the rewrite: put `set_option zempic.fuse true` at the top of the file and write
ordinary `List.range n |>.map f |>.filter p |>.foldl g 0`. A compiler pass
(`Zempic/AutoFuse.lean`, installed with `@[cpass]`) swaps `List.map`/`filter`/`foldl`/`range`
for the `Zempic.Fuse` calls just before Lean specializes them. It is off by default
because the rewritten code runs slower in native Lean (closure calls, 0.59 s vs 0.38 s in
`BENCH.md`), so enable it only in files that target Haskell.

The `Zempic.Fuse` functions are normal Lean functions (still run and prove in Lean). The Haskell backend
swaps them for GHC's fusible `map`/`filter`/`foldl'`/`build`, and the three stages
become one loop with no lists. 9x faster than Lean's own version in word mode.

## Exact Nat, at word speed (auto mode, the default)

`#zempic` writes three files: `Out.hs` (wrapper), `Out/Fast.hs` (Nat as 64-bit `Word`, any
overflow throws) and `Out/Exact.hs` (Nat as `Natural`). A call runs the fast version; if it
overflows, the same pure call reruns on the exact one. Results are always exact (25! and 3000!
both check out) and the common case runs at word speed.

* The wrapper covers functions whose arguments and result are only `Nat`/`Bool`. Others are
  left to import from `Out.Fast` / `Out.Exact` directly.
* Worst case a call that overflows late does the work twice.
* Other modes: `#zempic f to "x.hs" mode word` (fast only, aborts on overflow) or `mode exact`.

`Nat`, `Bool` and user inductives (structures, enums, trees, `Option`) are typed, with strict typed
fields so GHC unboxes them in loops; lists, pairs, functions and builtin types are still `Any`.

## Proved

Checked by Lean Studio and re-checked by Tenet, an independent kernel (142 of 142 declarations,
only `propext`, `Classical.choice`, `Quot.sound`):

* `Zempic.mangle_injective`: two different Lean names never get the same Haskell name.
* `Zempic.Proofs.mangleV1_not_injective`: the v0.1 encoding did not have this property.
  `foo._lam` and `foo_.lam` both became `foo___lam`. Trying to prove injectivity found it;
  the new encoding is a prefix code (a `_` always means a dot, a `'` always starts an escape).
* `Zempic.Proofs.coerce_*`: typed code gets no casts, and `Any` casts are exactly `zo`/`zu`.

Not proved: that the emitted Haskell means what the Lean did (the traversals are `partial`, so
proofs see them as opaque), and that the Word fast path agrees with `Nat` (that is Haskell code,
checked by tests, not by Lean).

## Not yet

* Unboxed list elements and pair components (they are `Any`), and typed values across the auto-mode wrapper (it covers only `Nat`/`Bool` signatures, so a structure-typed function is used from `Out.Fast`/`Out.Exact` directly).
* Fixed-width ints, `String`/`Array` ops, `IO`, `Float`, `Thunk`/`Task`.
  Unsupported constants are listed in a compile error, never silently dropped.
* More fusible combinators. Mapped (by hand or by `zempic.fuse`): `map`, `filter`, `foldl`, `foldr`, `range`, `length`, `sum` (Nat), `take`, `append`, `zip`, `any`, `all`. Not mapped: `reverse`, `filterMap`, `join`, `zipWith`, `Array`, `for` loops. `zip` fuses on its first list only.
* Benchmarks beyond three loops. See `BENCH.md` for what is and is not measured.

## Lean Studio

Every module is checked with Lean Studio's `check_file`/`build`. Next: use
`verify` (Tenet) on the Lean side and `profile` to compare Lean-native and GHC
timings per declaration.

## Support

leanzempic is free software under Apache-2.0, built and maintained by one person. If it saves you
time or you just want to see the work continue, donations in Ethereum are welcome and appreciated:

```
0x88adFCaa8FFaC62618b34F87FBede6394C829B1e
```

ETH on Ethereum mainnet. Nothing is expected, and the project stays free either way. Bug reports,
benchmarks on your own code and pull requests help just as much.
