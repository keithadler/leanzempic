import Zempic

/-- Lists and arrays back and forth, append, extract, reverse, contains. -/
def mixed (n : Nat) : Nat :=
  let a := (List.range n).toArray
  let b := a ++ #[1, 2, 3]
  let c := b.extract 1 (n / 2)
  let d := c.reverse
  (if d.contains 5 then 1 else 0) + d.toList.length + b.size + (d.foldr (· + ·) 0)

/-- Any, all, filter and zip on arrays. -/
def preds (n : Nat) : Nat :=
  let a := Array.range n
  (if a.any (· == n - 1) then 1 else 0) + (if a.all (· < n) then 1 else 0) +
    (a.filter (· % 3 == 0)).size + (a.zip a).size + (a.mapIdx fun i x => i + x).foldl (· + ·) 0

/-- Print one test or all of them. -/
def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  let fs := [mixed, preds]
  match args[1]? with
  | some i => IO.println ((fs[i.toNat!]!) n)
  | none => for f in fs do IO.println (f n)

#zempic mixed preds to "build/Arrays2.hs"
