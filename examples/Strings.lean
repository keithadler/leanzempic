import Zempic

/-- Build a string by pushing characters. -/
def pushed (n : Nat) : Nat := Id.run do
  let mut s := ""
  for i in [0:n] do
    s := s.push (Char.ofNat (97 + i % 26))
  return s.length * 3 + s.utf8ByteSize

/-- Append the decimal text of each number. -/
def decimals (n : Nat) : Nat := Id.run do
  let mut s := ""
  for i in [0:n] do
    s := s ++ toString i ++ ","
  return s.length

/-- Equality and ordering of strings. -/
def compares (n : Nat) : Nat := Id.run do
  let mut t := 0
  for i in [0:n] do
    let a := toString i
    let b := toString (n - i)
    if a == b then t := t + 1
    if a < b then t := t + 10
    if a ≤ b then t := t + 100
  return t

/-- Strings to character lists and back. -/
def lists (n : Nat) : Nat :=
  let s := toString (n * 12345)
  let cs := s.toList
  let r := String.ofList cs.reverse
  cs.length + (cs.map Char.toNat).foldl (· + ·) 0 + r.length + (if r == s then 1 else 0)

/-- Characters of non-ASCII text have more bytes than characters. -/
def unicode (n : Nat) : Nat :=
  let s := "héllo wörld ∀x, ∃y"
  s.length * n + s.utf8ByteSize + (s ++ s).length

/-- Print one test or all of them. -/
def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  let fs := [pushed, decimals, compares, lists, unicode]
  match args[1]? with
  | some i => IO.println ((fs[i.toNat!]!) n)
  | none => for f in fs do IO.println (f n)

#zempic pushed decimals compares lists unicode to "build/Strings.hs"
