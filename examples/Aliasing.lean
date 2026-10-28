import Zempic

/-- Updates `a` and also `b`, so `a` must stay intact. -/
def shared (n : Nat) : Nat :=
  let a := Array.replicate (n + 2) 1
  let b := a.set! 0 10
  let c := a.set! 1 20
  a[0]! + a[1]! + b[0]! + b[1]! + c[0]! + c[1]!

/-- Builds a fresh array each call. -/
@[noinline] def mk (k : Nat) : Array Nat := ((Array.mkEmpty 4).push k).push (k + 1)

/-- Two identical constructions must not be one array. -/
def twice (n : Nat) : Nat :=
  let x := mk n
  let y := mk n
  let x2 := x.push 99
  y.size * 1000 + x2.size * 100 + y[0]! + x2[2]!

/-- Updates its argument. -/
@[noinline] def bump (a : Array Nat) : Array Nat := a.set! 0 99

/-- The caller keeps using `a` after `bump`. -/
def cow (n : Nat) : Nat :=
  let a := Array.replicate (n + 2) 1
  let b := bump a
  a[0]! * 1000 + b[0]!

/-- One call passes a dead array, the other a live one. -/
def mixedCallers (n : Nat) : Nat :=
  let a := Array.replicate (n + 2) 1
  let b := bump a
  let c := bump (Array.replicate (n + 2) 5)
  a[0]! * 10000 + b[0]! * 100 + c[0]! + c[1]!

/-- A structure that still holds the array after a projection. -/
structure Hold where
  /-- The array. -/
  arr : Array Nat
  /-- A number. -/
  k : Nat

/-- Two updates through the same structure. -/
def hold (n : Nat) : Nat :=
  let h : Hold := ⟨Array.replicate (n + 2) 2, 3⟩
  let a := h.arr.set! 0 7
  let b := h.arr.set! 1 8
  h.arr[0]! + a[0]! * 10 + b[1]! * 100 + h.k + a[1]! + b[0]!

/-- A closure captures the array and is called twice. -/
def closure (n : Nat) : Nat :=
  let a := Array.replicate (n + 3) 1
  let f := fun (i : Nat) => a.set! i 5
  (f 0)[0]! + (f 1)[0]! * 10 + (f 1)[1]! * 100 + a[0]! * 1000 + a[1]!

/-- The array is stored twice in a list, one copy updated. -/
def inList (n : Nat) : Nat :=
  let a := Array.replicate (n + 2) 1
  let l := [a, a.set! 0 9, a]
  l.foldl (fun t x => t * 7 + x[0]!) 0

/-- Arrays holding arrays. -/
def nested (n : Nat) : Nat :=
  let inner := Array.replicate (n + 2) 1
  let outer := #[inner, inner]
  let outer2 := outer.set! 0 (inner.set! 0 9)
  outer2[0]![0]! * 100 + outer2[1]![0]! * 10 + inner[0]!

/-- A function that returns its argument. -/
@[noinline] def ident (a : Array Nat) : Array Nat := a

/-- Pushing to the result of `ident` while the original lives. -/
def identity (n : Nat) : Nat :=
  let a := Array.replicate (n + 2) 4
  let b := ident a
  let c := b.push 1
  a.size * 100 + c.size * 10 + b.size

/-- One branch updates, the other passes the array on; then it is used and updated again. -/
def branches (n : Nat) : Nat :=
  let a := Array.replicate (n + 2) 1
  let b := if n % 2 == 0 then a.set! 0 5 else a
  let c := b.set! 1 6
  a[0]! * 1000 + a[1]! * 100 + b[0]! * 10 + c[1]!

/-- A loop that keeps an old version and keeps updating. -/
def keepOld (n : Nat) : Nat := Id.run do
  let mut a := Array.replicate 8 0
  let mut old := a
  for i in [0:n] do
    if i % 5 == 0 then old := a
    a := a.set! (i % 8) (i + 1)
  return a[0]! + a[3]! * 10 + old[0]! * 100 + old[3]! * 1000 + a.size + old.size

/-- Swapping within an array that is also stored elsewhere. -/
def swapShared (n : Nat) : Nat :=
  let a := (Array.range (n + 4))
  let b := a.swapIfInBounds 0 3
  let c := b.swapIfInBounds 1 2
  a[0]! * 1000 + b[0]! * 100 + c[1]! * 10 + c[0]!

/-- Calls a function value; kept out of line so the closure really exists. -/
@[noinline] def callIt (f : Nat → Nat) (i : Nat) : Nat := f i

/-- A closure captures the array, then the array is updated while the closure lives. -/
def captureThenSet (n : Nat) : Nat :=
  let a := Array.replicate (n + 3) 1
  let f := fun (i : Nat) => a[i]!
  let b := a.set! 0 9
  callIt f 0 * 100 + b[0]! * 10 + callIt f 1

/-- Reads the array out of a structure; out of line so the compiler cannot see through it. -/
@[noinline] def holdArr (h : Hold) : Array Nat := h.arr

/-- The array is stored in a structure, then updated while the structure lives. -/
def storedThenSet (n : Nat) : Nat :=
  let a := Array.replicate (n + 3) 2
  let h : Hold := ⟨a, 5⟩
  let b := a.set! 0 9
  (holdArr h)[0]! * 100 + b[0]! * 10 + h.k

/-- The array reaches a join point that is also reached with the old version. -/
def joined (n : Nat) : Nat :=
  let a := Array.replicate (n + 3) 3
  let b := if n % 2 == 0 then a else a.set! 0 8
  let c := b.set! 1 7
  a[1]! * 100 + c[0]! * 10 + c[1]!

/-- Print one test or all of them. -/
def main (args : List String) : IO Unit := do
  let n := (args.headD "10").toNat!
  let fs := [shared, twice, cow, mixedCallers, hold, closure, inList, nested, identity, branches,
    keepOld, swapShared, captureThenSet, storedThenSet, joined]
  match args[1]? with
  | some i => IO.println ((fs[i.toNat!]!) n)
  | none => for f in fs do IO.println (f n)

#zempic shared twice cow mixedCallers hold closure inList nested identity branches keepOld
  swapShared captureThenSet storedThenSet joined to "build/Aliasing.hs"
