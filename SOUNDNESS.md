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

* a **fresh array** (`mkEmpty`, `replicate`, `range`, `mk`, `toArray`) is `own`;
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
  array. A version that a buffer copy was taken from (the persistent operations copy a buffer once it
  carries as many undo records as the array has elements) is marked, and the in-place primitives treat
  it as stale too.
* Modules with in-place updates are compiled with `-fno-cse -fno-full-laziness`, so GHC cannot merge
  two array constructions into one object or float one out to top level, which would manufacture
  two owners.
* Persistent operations are always correct, so any imprecision costs speed, not correctness.
* `set_option zempic.own false` turns the analysis off entirely.

## Typed element access

The ownership claim above is about aliasing. A separate, narrower claim covers the `W` primitives
(`arrUGetW`, `arrPushUW`, `arrUSetBUW`, ...), which read and write a `Word` element (`Nat` in word mode,
`USize`) with no box:

* The emitter picks a `W` primitive only when the element is a `Word` by the type of a value it can
  see: the declared type of a read outside `Array.mapMUnsafe`, the Haskell type of the value being
  written, or, for a read inside `Array.mapMUnsafe` (where the view as `NonScalar` hides the element
  type), a later use of the read as an argument that a primitive takes as `Nat`/`USize`. Lean's type
  checker makes the last two sound: such a use means the value is a `Nat` there.
* A `Word` write into a buffer of another element type (a `UInt8` array that `Array.map` turns into
  `Nat`s) first makes the buffer boxed, as the generic path does. `array_word_paths` checks it, and a
  deliberate bug (skipping that step) is caught.
* `Array.range` is a fresh array and is `own`.
* The `W` push and set primitives (`arrPushUW`, `arrSetUW`, `arrUSetUW`) and the `Word` readers are
  `INLINE`, not `NOINLINE` like the generic in-place primitives: the fast path (a live word buffer) must
  be visible to GHC to stay unboxed. The assumption "GHC does not duplicate or reorder them" therefore
  rests on the same things as for `arrSet`: strict `let`s, `-fno-cse -fno-full-laziness`, and
  `runRW#`/`unsafeDupablePerformIO` for the effect. Every path that is not the fast one is a `NOINLINE`
  function. The garden, the aliasing tests and the property tests (including stale and lazily shared
  versions) pass with it.

### Narrow integer elements

`UInt8`, `UInt16`, `UInt32`, `UInt64` (and `Char`, a `UInt32`) elements get the same treatment as `Word` ones:
`arrGetD32`, `arrGetI32`, `arrUGet32`, `arrPushU32`, `arrSetU32`, `arrUSetU32` and the 8, 16 and 64 bit
versions, and `arrSwapU{8,16,32,64,W}` for swaps.

* The emitter picks a narrow primitive only from the Haskell type it sees: the type of a read, or of the value
  written. It never does inside `Array.mapMUnsafe` (the view as `NonScalar` hides the element type), where the
  generic, deoptimizing write is used as before. A swap carries no element, so its variant is chosen from the
  array's element type; it is a speed choice only, because every swap variant falls back to the generic
  `aSwapU` unless the live buffer is of exactly its kind.
* Each in-line fast path matches a live buffer of its own kind. Everything else (a boxed buffer, an old
  version, a lazy handle, a buffer that is not the sole owner) goes to a `NOINLINE` function that uses the
  generic boxed operations, so ownership and persistence are decided in the same place as before.
* Bounds are one unsigned comparison of the index against the length, so a negative or huge `Int` is out of
  range. A `Word` index is passed as it is (`arrIx`); in exact mode, where `Nat` is a `Natural`, it is clamped
  first, because a `Natural` of 2^64 would otherwise wrap to 0. The property tests read at -1, `minBound`,
  `maxBound`, 2^63, 2^64 and 2^70, in both modes.
* The default of a read (`idxErr32` etc., the shared error value of `a[i]` with a proof) is never forced
  unless the index is out of range; the slow path takes it boxed and lazily. A first version forced it on the
  slow path and failed the new garden program; the property tests now read in range with a default that
  throws.
* `growRaw`/`growBoxed` copy a buffer with `copyMutableByteArray#`/`copyMutableArray#` and clear the tail. A
  deliberate bug in the copy length crashes the property tests.

## Hoisted buffers

A loop may resolve an array's buffer once instead of at every access (`Zempic.Arr`, "Hoisted buffers";
`Emit.hoistPlan`). The raw accesses assume that the array's node (`Direct buffer count`) does not change while
the loop runs. The claim and why it should hold:

* The emitter hoists parameter `P` of a self-recursive function only if: `P` is `Array e` with `e` of 8, 16, 32 or
  64 bits; the function is not `Array.mapMUnsafe`; at least one in-place update of `P` or of the result of such an
  update is marked in place by the analysis (so `P` is `own` at entry: the analysis gives a parameter that
  ownership only if every call passes an owned, dead array); and every use of `P` and of those results is a read,
  an in-place same-length update (`swap`, `set`, `uset`) marked in place, or a use after which no variable that
  is that array is live (passed on, stored, returned, jumped with). A `push`, `pop` or persistent update is the
  third kind, so it ends the raw accesses on that path; the next step goes back through the wrapper, which looks
  again. A closure that captures the array, or a `cases` on it, disables hoisting for the function.
* Owned means no other reference exists, so no other code can reroot or copy the buffer, create a lazy handle on
  it (`aShare`) or mark it stale (count -1) while the loop runs; and the loop itself only reads and updates in
  place, which leave the node unchanged.
* The wrapper checks at run time that the node is `Direct` of the expected kind with count >= 0. A lazy handle, an
  old version, the source of a copy and a boxed buffer all fail the check and run the ordinary code, so a wrong
  static verdict is caught for those states. It is not caught if two live owners share a live buffer, as for the
  ordinary in-place primitives.
* Only the in-place primitives are replaced by raw ones. A persistent operation on the array stays persistent.

Testing: `tests/PropTests.hs` `arrHoisted` (all four widths): raw reads, sets and swaps against a list model at
indices -1, length, `maxBound`, `minBound` and in range; a default that must not be forced in range; a lazy handle,
an old version, the version a copy was taken from (one of 401 along a chain with copies) and a boxed buffer must
not be hoisted. Five deliberate bugs in the runtime were all detected: hoisting ignores the stale mark, swap
bound off by one, read without a range check, write without a range check (crash), hoisting a lazy handle.

Garden programs for the emitter's scan (`hoist_*`, UInt8/16/32/64 unless noted). Each one builds its array by
pushes and starts its loops at a value that is not a literal. Both matter: an array made by `map` keeps its
source's boxed buffer, so the wrapper's check fails and the hoisted loop never runs (the older `hoist_set_*`,
`hoist_shared_*` and `hoist_escape_*` built their arrays that way and ran the ordinary code only, which was found
by counting calls of the hoisted workers; they now push), and the unroller runs the first 16 iterations of a
loop with a literal start on the ordinary code, after which the array is a lazy handle and the check fails.
`hoist_qsort_*`, `hoist_set_*`, `hoist_shared_*` and `hoist_escape_*` (UInt8, UInt32) cover the loops that
should hoist; the others are loops that look hoistable (they update in place) and also do one thing that must
end the raw accesses, and each must run as the ordinary code:

* `hoist_push_*`: push, then read the new last element and an index that exists only after the push; push in
  one branch of an `if`.
* `hoist_pop_*`: pop, then read just past the new end (must give the default).
* `hoist_persist_*`: a persistent update of an array that is read afterwards, directly and through a helper.
* `hoist_fnarg_*` (UInt8, UInt64): the helper is a function value.
* `hoist_closure_*` (UInt8, UInt64): a closure captures the array, then it is updated.
* `hoist_join_*` (UInt8, UInt64): the array reaches a join point as a free variable and as the argument its
  parameter takes, and the parameter is updated while the array is read.
* `hoist_twice_*` (UInt8): the loop hands the same array on as two of its parameters.
* `hoist_misc_*` (UInt8, UInt32): append, extract and swap in the loop. `hoist_match_*` (UInt8): the array is
  taken apart with a pattern.

Mutation testing of the scan (`Emit.hoistWalk`, `hoistPlan`), 11 deliberate edits, each built and run against
every `hoist_*` program, then reverted. Killed (a program gives a wrong answer):

| Mutation | Killed by |
|---|---|
| `push` treated as length-preserving (listed with the in-place updates) | `hoist_push_*`, `hoist_shared_*` (stale buffer and length after the push) |
| the in-place requirement dropped (a persistent update joins the aliases) | `hoist_persist_*`, `hoist_match_*` (a raw read of the old version sees the new value) |
| `pop` treated as length-preserving | `hoist_pop_*` |
| a jump that hands the array on no longer ends the raw accesses | `hoist_join_*` |
| the `ok` flag ignored (all of the refusals at once) | `hoist_join_*` |
| the array allowed twice in one call (`both a a`) | `hoist_twice_*` |

Survived, and why they cannot be observed:

* A call that receives the array, or a call of a function value with it (`g a`), no longer ends the raw accesses.
  Not observable: the call site makes the array a lazy handle (`arrShare`) whenever the array is used again
  after the call, and a lazy handle copies on its first write, so the callee cannot change the buffer the
  worker reads; and when the call is the array's last use, nothing reads it afterwards. After such a call the
  analysis also cannot mark a later update of that array in place, so no raw write follows. The check is a
  second line of defense behind the call-site sharing.
* A closure that captures the array (`.fun`) no longer disables hoisting. Not reachable: local functions are
  lambda-lifted before the emitter runs, so a capture is a partial application of a lifted function (a call
  that receives the array, the case above), and no garden program emits a local function. The `.fun` branch
  of `hoistWalk` is dead code kept for the other pipeline stages.
* A `cases` on the array no longer disables hoisting, and the `proj` check. Not reachable: a pattern on an
  array compiles to `Array.toList`, a read (`hoist_match_*`); `Array` has no constructor case or projection in
  the code that reaches the emitter. Dead guards.
* The `loops` requirement dropped. A function without a self-call hoisted anyway is correct and only wastes
  the wrapper; the guard is a performance one, so no output can differ.

The earlier note here that two emitter mutations (`push` as length-preserving, and the in-place requirement
dropped) went undetected is superseded: the first was not caught because the old garden programs never ran a
hoisted loop at all, and no old program pushed in a loop whose array stayed hoistable. Both are now killed.

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
