/-
Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.

List combinators that leanzempic maps onto GHC's fusible `map`/`filter`/`foldl'`/`enumFromTo`.
They are ordinary Lean definitions (so the program still runs, and proves, in Lean), marked
`@[noinline]` so the compiler keeps the call by name and the Haskell backend can replace it.
Writing a pipeline with these lets GHC fuse it into one loop with no intermediate lists.

One semantic difference: Lean builds each intermediate list eagerly; the Haskell side may
never build it. Results are identical for total functions; a `panic!`/divergence inside a
stage may happen in a different order or not at all.
-/
namespace Zempic.Fuse

/-- List map. Replaced by GHC's fusible `map` in the Haskell backend. -/
@[noinline] def map (f : α → β) (xs : List α) : List β := List.map f xs
/-- List filter. Replaced by GHC's fusible `filter`. -/
@[noinline] def filter (p : α → Bool) (xs : List α) : List α := List.filter p xs
/-- Left fold. Replaced by GHC's strict, fusible `foldl'`. -/
@[noinline] def foldl (f : β → α → β) (init : β) (xs : List α) : β := List.foldl f init xs
/-- `[0, n)`. Replaced by an explicit `build` so GHC can fuse it. -/
@[noinline] def range (n : Nat) : List Nat := List.range n

/-- List length. Replaced by GHC's `length`. -/
@[noinline] def length (xs : List α) : Nat := List.length xs
/-- Sum of a list of naturals. Replaced by a strict fused sum. -/
@[noinline] def sum (xs : List Nat) : Nat := List.foldl (· + ·) 0 xs
/-- The first `n` elements. Replaced by GHC's fusible `take`. -/
@[noinline] def take (n : Nat) (xs : List α) : List α := List.take n xs
/-- Concatenation. Replaced by GHC's fusible `(++)`. -/
@[noinline] def append (xs ys : List α) : List α := List.append xs ys
/-- Right fold. Replaced by GHC's `foldr`, the base case of its fusion rules. -/
@[noinline] def foldr (f : α → β → β) (init : β) (xs : List α) : β := List.foldr f init xs
/-- Does some element satisfy `p`? Replaced by GHC's fusible `any`. -/
@[noinline] def any (p : α → Bool) (xs : List α) : Bool := List.any xs p
/-- Do all elements satisfy `p`? Replaced by GHC's fusible `all`. -/
@[noinline] def all (p : α → Bool) (xs : List α) : Bool := List.all xs p
/-- Pair up elements. Replaced by GHC's fusible `zip`. -/
@[noinline] def zip (xs : List α) (ys : List β) : List (α × β) := List.zip xs ys

end Zempic.Fuse
