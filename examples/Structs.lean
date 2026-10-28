import Zempic

/-- Running statistics, the state of a fold. -/
structure Stats where
  /-- Running total. -/
  sum : Nat
  /-- How many values. -/
  cnt : Nat
  /-- Largest value. -/
  mx : Nat

/-- Fold one value into the statistics. -/
def step (a : Stats) (x : Nat) : Stats :=
  { sum := a.sum + x, cnt := a.cnt + 1, mx := if x > a.mx then x else a.mx }

/-- Run `step` over `n` pseudo-random values. -/
def statsLoop (i n : Nat) (a : Stats) : Stats :=
  if i ≥ n then a else statsLoop (i + 1) n (step a (i * i % 1000))

/-- One number from the final statistics. -/
def stats (n : Nat) : Nat :=
  let a := statsLoop 0 n ⟨0, 0, 0⟩
  a.sum + a.cnt + a.mx

/-- A point; a pair of points is a nested structure. -/
structure Pt where
  /-- Horizontal coordinate. -/
  x : Nat
  /-- Vertical coordinate. -/
  y : Nat

/-- A segment between two points. -/
structure Seg where
  /-- First endpoint. -/
  a : Pt
  /-- Second endpoint. -/
  b : Pt

/-- Walk a segment's endpoints toward each other. -/
def walk (s : Seg) (k : Nat) : Seg :=
  match k with
  | 0 => s
  | k + 1 => walk { a := ⟨s.a.x + 1, s.a.y + 2⟩, b := ⟨s.b.x + 3, s.b.y + 1⟩ } k

/-- One number from a walked segment. -/
def segTest (n : Nat) : Nat :=
  let s := walk ⟨⟨1, 2⟩, ⟨3, 4⟩⟩ n
  s.a.x + s.a.y * 3 + s.b.x * 5 + s.b.y * 7

/-- An enumeration. -/
inductive Color
  /-- Red. -/
  | red
  /-- Green. -/
  | green
  /-- Blue. -/
  | blue

/-- Pick a color from a number. -/
def pick (n : Nat) : Color :=
  if n % 3 == 0 then .red else if n % 3 == 1 then .green else .blue

/-- Weight of a color. -/
def weight : Color → Nat
  | .red => 1
  | .green => 10
  | .blue => 100

/-- Sum of weights over `n` numbers. -/
def colorTest (n : Nat) : Nat := Id.run do
  let mut t := 0
  for i in [0:n] do
    t := t + weight (pick i)
  return t

/-- A binary search tree of naturals. -/
inductive Tree
  /-- The empty tree. -/
  | leaf
  /-- A value with a left and a right subtree. -/
  | node (l : Tree) (v : Nat) (r : Tree)

/-- Insert into the tree. -/
def Tree.insert (t : Tree) (x : Nat) : Tree :=
  match t with
  | .leaf => .node .leaf x .leaf
  | .node l v r =>
    if x < v then .node (l.insert x) v r
    else if x > v then .node l v (r.insert x)
    else t

/-- Sum of the tree. -/
def Tree.total : Tree → Nat
  | .leaf => 0
  | .node l v r => l.total + v + r.total

/-- Build a tree from `n` pseudo-random values. -/
def build (i n : Nat) (t : Tree) : Tree :=
  if i ≥ n then t else build (i + 1) n (t.insert (i * 7919 % 10007))

/-- The tree's total. -/
def treeTest (n : Nat) : Nat := (build 0 n .leaf).total

/-- An optional lookup. -/
def find (xs : List Nat) (p : Nat → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x :: rest => if p x then some x else find rest p

/-- Use `Option` results. -/
def optTest (n : Nat) : Nat :=
  match find (List.range n) (fun x => x * x > n * 3) with
  | some v => v
  | none => 0

/-- Print one test or all of them. -/
def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  let fs := [stats, segTest, colorTest, treeTest, optTest]
  match args[1]? with
  | some i => IO.println ((fs[i.toNat!]!) n)
  | none => for f in fs do IO.println (f n)

#zempic stats segTest colorTest treeTest optTest to "build/Structs.hs"
