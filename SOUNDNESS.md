# Soundness of the ownership analysis

`Zempic/Own.lean` decides when an array operation may update in place. A wrong "yes" makes the
program compute a different answer, silently. This document states exactly what is claimed, why it
should hold, and how it was tested. It is an argument and a test record, **not a machine-checked
proof**. The analysis is not covered by Lean theorems (see "What is not proved" in the README).

## The claim

If the analysis marks an operation `op a ...` as in place, then in every execution of the generated
program, at the moment `op` runs:

1. `a` is referenced by nothing else that can be read later (no other variable, no data structure,
   no closure, no other call frame), and
2. `a` itself is not read after `op`.

Under (1) and (2) updating `a`'s buffer is indistinguishable from creating a new array.

## Why it should hold

The analysis tracks, for each variable, one of `top` (nothing known), `own` (a uniquely held array)
or `con` (a uniquely held constructor cell with known field ownership). Ownership is created in three
ways only:

* a **fresh array** (`mkEmpty`, `replicate`, `mk`, `toArray`) is `own`;
* the **result of an in-place update** of an `own` array is `own` (the same buffer, still unique);
* a **constructor cell** is `con` only if built from owned parts that were handed over.

It is destroyed conservatively. Every use of a variable that is not a recognized read
(`size`, `get`, `uget`, `toList`, ...) removes it from the environment: passing it to an unknown
function, storing it in a constructor, applying it, capturing it in a closure, or using it as a
partial application. A variable used again after an operation is never handed over (`later` check).
Handing a variable to a callee transfers ownership only if it appears once among the arguments and
is dead afterwards.

Across functions, a parameter is `own` only if **every** call site passes an owned, dead value
(summaries are met over all call sites). Roots (called from outside), functions used as values and
partial applications get `top` parameters. Join-point parameters work the same way over all jumps.
The fixpoint starts optimistic and the final pass is the one whose decisions are used, so the result
is consistent with the final summaries.

## Defence in depth

The analysis can be wrong; these limit the damage:

* Each in-place primitive checks that its array is the live version of its buffer and otherwise
  performs the persistent operation. This catches a stale array but **not** two live owners of one
  array.
* Modules with in-place updates are compiled with `-fno-cse -fno-full-laziness`, so GHC cannot merge
  two array constructions into one object or float one out to top level, which would manufacture
  two owners.
* Persistent operations are always correct, so any imprecision costs speed, not correctness.
* `set_option zempic.own false` turns the analysis off entirely.

## Assumptions the claim depends on

* **Single thread of use.** Arrays are mutable buffers behind `unsafeDupablePerformIO`; two threads
  using one array concurrently are not supported.
* **GHC does not duplicate work or reorder effects of the primitives.** The in-place primitives are
  `NOINLINE`, the module is compiled without CSE or full laziness, and every `let` is strict. A
  future GHC optimization that duplicated an application of an in-place primitive would break this.
* **LCNF variables are unique within a function.** (They are not unique across functions; results
  are keyed by function and variable. A bare-variable key once caused a real bug.)
* **Lean's compiler preserves the aliasing the analysis sees.** The analysis runs on the mono-phase
  LCNF that is actually emitted, so later Lean passes cannot reorder it.

## Testing

* `examples/Aliasing.lean`: 15 programs that update arrays while other references are live (reads
  after updates, a function called by one caller that keeps the array and one that does not,
  identical constructions, closures, structures, lists, nested arrays, join points merging old and
  new versions, loops that keep a snapshot). Each is compared with native Lean at 8 sizes.
* **Mutation testing of the analysis.** Five deliberate bugs, four detected:

  | Deliberate bug | Detected |
  |---|---|
  | in-place update ignores later uses of the array | yes |
  | ownership handed over though the caller still uses it | yes |
  | partial application keeps ownership of its arguments | yes |
  | constructor application keeps ownership of the stored array | yes |
  | closure capture ignored for a local function (`.fun` node) | **no** |

  The last guards a case Lean's compiler never produces here (closures are lambda-lifted into
  partial applications, covered by another rule), so no test reaches it. It stays as defence.
* `tests/PropTests.hs`: random operation sequences on persistent and in-place arrays, including
  in-place operations applied to stale versions, compared with a list model at every step.
* `tools/fuzz.py`: random Lean programs with loops, forks and snapshots, compared with Lean. It is a
  broad net and not a sharp one: of three deliberate bugs it caught two, each in only a few percent
  of seeds, and missed "ownership handed over though the caller still uses it" entirely. The targeted
  tests catch all three.

## Known imprecision (safe, but costs speed)

* Tracking of nested constructor cells stops at depth 12; beyond that an array is treated as shared.
* Two arrays built by the same expression are one array after Lean's CSE and are never updated in place.
* A fork inside a loop body makes the loop-carried array shared for the whole loop.
* Some read patterns (for example `getD` combined with a size test in the same loop body) make one
  update persistent that could have been in place.

## What would make this stronger

* Prove the analysis sound in Lean against a small formal semantics of LCNF with reference counts.
  This is the real fix and is substantial work.
* Run the generated programs under a dynamic checker that counts references, and compare with the
  static verdicts.
* Differential fuzzing: generate random Lean programs that use arrays, and compare Lean against the
  Haskell output.

Until then, treat in-place array updates as the one part of leanzempic whose correctness rests on
testing rather than on construction, and keep `zempic.own false` in mind when debugging a wrong result.
