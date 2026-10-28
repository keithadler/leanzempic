import Zempic

/-- Push to the same old string twice: neither result may disturb the other. -/
def forks (n : Nat) : Nat :=
  let s1 := "ab".push (Char.ofNat (97 + n % 26))
  let s2 := s1.push 'c'
  let s3 := s1.push 'd'
  let s4 := s2.push 'e'
  s2.length * 1000 + s3.length * 100 + s4.length * 10 +
    (s2.toList.map Char.toNat).foldl (· + ·) 0 + (s3.toList.map Char.toNat).foldl (· * 3 + ·) 0

/-- Append a string to itself, and to an old version of itself. -/
def selfAppend (n : Nat) : Nat :=
  let s := toString (n + 12345)
  let t := s ++ s
  let u := s ++ "-" ++ s
  let v := t ++ s
  (t.length * 10 + u.length) * 100 + (v.toList.map Char.toNat).foldl (· + ·) 0 +
    (if t == s ++ s then 1 else 0) + (if u < t then 7 else 0)

/-- A literal used in several places and extended in each. -/
def literal (n : Nat) : Nat :=
  let t := "abc"
  let a := t.push 'x'
  let b := t.push 'y'
  let c := t ++ toString n
  a.length * 1000 + b.length * 100 + c.length * 10 + t.length +
    (a.toList.getLast!.toNat) + (b.toList.getLast!.toNat) + (c.toList.getLast!.toNat)

/-- Cross the 16-byte starting capacity from several versions, with multi-byte characters. -/
def growth (n : Nat) : Nat := Id.run do
  let mut s := ""
  let mut snaps : Array String := #[]
  for i in [0:n % 60 + 40] do
    let code := if i % 7 == 0 then 0x2200 + i else if i % 5 == 0 then 0xE9 else 97 + i % 26
    s := s.push (Char.ofNat code)
    if i % 9 == 0 then snaps := snaps.push s
  let mut t := 0
  for x in snaps do
    let y := x.push 'z'
    t := t + x.length * 3 + y.utf8ByteSize + (y.toList.map Char.toNat).foldl (· + ·) 0
  return t + s.length + s.utf8ByteSize

/-- A loop that keeps a snapshot, then keeps pushing. -/
def snapshot (n : Nat) : Nat := Id.run do
  let mut s := "start"
  let mut old := s
  for i in [0:n % 50 + 20] do
    if i == 7 then old := s
    s := s.push (Char.ofNat (65 + i % 26))
  return s.length * 1000 + old.length * 10 + (s == old ++ "x" |> fun b => if b then 1 else 0) +
    (old.toList.map Char.toNat).foldl (· + ·) 0

/-- Ordering and equality across versions that share a buffer. -/
def sharedCompare (n : Nat) : Nat :=
  let a := toString n ++ "mid"
  let b := a.push 'a'
  let c := a.push 'b'
  (if b < c then 1 else 0) + (if c < b then 10 else 0) + (if a < b then 100 else 0) +
    (if b == a.push 'a' then 1000 else 0) + (if b == c then 10000 else 0)

/-- Print one test or all of them. -/
def main (args : List String) : IO Unit := do
  let n := (args.headD "10").toNat!
  let fs := [forks, selfAppend, literal, growth, snapshot, sharedCompare]
  match args[1]? with
  | some i => IO.println ((fs[i.toNat!]!) n)
  | none => for f in fs do IO.println (f n)

#zempic forks selfAppend literal growth snapshot sharedCompare to "build/StringAliasing.hs"
