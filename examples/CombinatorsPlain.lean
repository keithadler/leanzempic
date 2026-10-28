import Zempic

set_option zempic.fuse false

/-- Elements divisible by 3. -/
def t1 (n : Nat) : Nat := ((List.range n).filter (· % 3 == 0)).length

/-- Sum of a mapped range. -/
def t2 (n : Nat) : Nat := ((List.range n).map (· % 7)).sum

/-- Zip two different mapped ranges, multiply the pairs, fold. -/
def t3 (n : Nat) : Nat :=
  (((List.range n).map (· * 3)).zip ((List.range (n + 1)).map (· + 1))).map
    (fun p => p.1 * p.2 % 1000) |>.foldl (· + ·) 0

/-- Take half of a range, fold from the right. -/
def t4 (n : Nat) : Nat := ((List.range n).take (n / 2)).foldr (fun a b => (a + b) % 1000003) 0

/-- Short-circuiting any and all, over different lists (equal lists would be shared). -/
def t5 (n : Nat) : Nat :=
  if (List.range n).any (· == n - 1) && (List.range (n + 1)).all (· ≤ n) then 1 else 0

/-- Append two different ranges and count. -/
def t6 (n : Nat) : Nat := ((List.range n) ++ (List.range (n + 1))).length

/-- Everything together, as one number. -/
def all (n : Nat) : Nat := t1 n + t2 n + t3 n + t4 n + t5 n + t6 n

/-- Print every result and the total, one per line; or only test `i` given a second argument. -/
def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  let fs := [t1, t2, t3, t4, t5, t6, all]
  match args[1]? with
  | some i => IO.println ((fs[i.toNat!]!) n)
  | none => for f in fs do IO.println (f n)

