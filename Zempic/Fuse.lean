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

@[noinline] def map (f : α → β) (xs : List α) : List β := List.map f xs
@[noinline] def filter (p : α → Bool) (xs : List α) : List α := List.filter p xs
@[noinline] def foldl (f : β → α → β) (init : β) (xs : List α) : β := List.foldl f init xs
@[noinline] def range (n : Nat) : List Nat := List.range n

end Zempic.Fuse
