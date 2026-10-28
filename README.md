# leanzempic 🙂

A Haskell backend for Lean 4. It prints Lean's compiled terms (LCNF, mono
phase) as Haskell shaped like GHC Core, so GHC's optimizer decides the
execution order and the code generator.

Licensed under Apache-2.0. Status: v0.1, private, early.

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

Compile with `ghc -O2 -iruntime -ibuild`. See `tests/run.sh` for the full loop.

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

## Nat modes

Pick one by include path when compiling the generated module:

* `-iruntime/natural`: exact, Nat is `Natural`. Same semantics as Lean, slower.
* `-iruntime/word`: Nat is `Word`; results above 2^64-1 abort with an error, never wrap. Fast (see `BENCH.md`).

`Nat` and `Bool` are typed in signatures; other values are still `Any` (free casts).

## Not yet

* Types beyond `Nat`/`Bool`, so GHC cannot unbox structures or list elements yet.
* Fixed-width ints, `String`/`Array` ops, `IO`, `Float`, `Thunk`/`Task`.
  Unsupported constants are listed in a compile error, never silently dropped.
* More fusible combinators. Only `map`, `filter`, `foldl`, `range` are mapped (by hand or by `zempic.fuse`); `length`, `sum`, `zip`, `take`, `append`, `foldr`, `any`/`all` are not, and `Array`/`for` loops are untouched.
* Benchmarks beyond three loops. See `BENCH.md` for what is and is not measured.

## Lean Studio

Every module is checked with Lean Studio's `check_file`/`build`. Next: use
`verify` (Tenet) on the Lean side and `profile` to compare Lean-native and GHC
timings per declaration.
