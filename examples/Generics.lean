import Zempic

/-- A generic pair of values. -/
structure Pair (α β : Type) where
  /-- First component. -/
  fst : α
  /-- Second component. -/
  snd : β

/-- A generic function, kept out of line so it is compiled once for all types. -/
@[noinline] def Pair.swap {α β : Type} (p : Pair α β) : Pair β α := ⟨p.snd, p.fst⟩

/-- Another generic function: replace the first component. -/
@[noinline] def Pair.withFst {α β γ : Type} (p : Pair α β) (c : γ) : Pair γ β :=
  ⟨c, p.snd⟩

/-- A generic tree. -/
inductive Box (α : Type)
  /-- Nothing. -/
  | empty
  /-- A value with two children. -/
  | node (l : Box α) (v : α) (r : Box α)

/-- Insert into a box tree ordered by a key function. -/
@[noinline] def Box.insertBy {α : Type} (key : α → Nat) (t : Box α) (x : α) : Box α :=
  match t with
  | .empty => .node .empty x .empty
  | .node l v r =>
    if key x < key v then .node (l.insertBy key x) v r
    else .node l v (r.insertBy key x)

/-- Sum of keys. -/
@[noinline] def Box.sumBy {α : Type} (key : α → Nat) : Box α → Nat
  | .empty => 0
  | .node l v r => l.sumBy key + key v + r.sumBy key

/-- Swap pairs of different types through the one generic function. -/
def swaps (n : Nat) : Nat := Id.run do
  let mut t := 0
  for i in [0:n] do
    let a : Pair UInt8 Nat := ⟨i.toUInt8, i⟩
    let b : Pair Bool UInt32 := ⟨i % 2 == 0, i.toUInt32⟩
    let c : Pair Nat Nat := ⟨i, i + 1⟩
    t := t + a.swap.fst + a.swap.snd.toNat + b.swap.fst.toNat + (if b.swap.snd then 1 else 0)
      + c.swap.fst + c.swap.snd + (a.withFst i.toUInt16).fst.toNat
  return t

/-- Generic data in a list, an array and an Option. -/
def containers (n : Nat) : Nat :=
  let ps := (List.range n).map fun i => (⟨i, i.toUInt8⟩ : Pair Nat UInt8)
  let arr := ps.toArray.map Pair.swap
  let o : Option (Pair UInt32 Nat) := if n > 3 then some ⟨7, n⟩ else none
  ps.foldl (fun a p => a + p.fst + p.snd.toNat) 0 + arr.foldl (fun a p => a + p.fst.toNat) 0 +
    (match o with | some p => p.fst.toNat + p.snd | none => 0)

/-- A tree of pairs, keyed by the pair's second part. -/
def trees (n : Nat) : Nat := Id.run do
  let mut t : Box (Pair Nat UInt16) := .empty
  for i in [0:n] do
    t := t.insertBy (fun p => p.snd.toNat) ⟨i, (i * 31 % 1009).toUInt16⟩
  let mut u : Box Nat := .empty
  for i in [0:n] do
    u := u.insertBy id (i * 7919 % 10007)
  return t.sumBy (fun p => p.fst + p.snd.toNat) + u.sumBy id

/-- A loop with three mutable variables of different types. -/
def threeVars (n : Nat) : Nat := Id.run do
  let mut a : UInt8 := 3
  let mut b : UInt32 := 5
  let mut c : Nat := 0
  let mut d : Bool := false
  for _ in [0:n] do
    a := a * 7 + 1
    b := b ^^^ (b <<< 3) + a.toUInt32
    d := !d
    c := c + (b % 10).toNat + (if d then 1 else 0)
  return c + a.toNat + b.toNat

/-- Print one test or all of them. -/
def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  let fs := [swaps, containers, trees, threeVars]
  match args[1]? with
  | some i => IO.println ((fs[i.toNat!]!) n)
  | none => for f in fs do IO.println (f n)

#zempic swaps containers trees threeVars to "build/Generics.hs"
