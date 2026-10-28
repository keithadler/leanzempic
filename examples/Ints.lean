import Zempic

/-- 64-bit FNV-1a-style hash of the numbers below `n`. -/
def fnv (n : Nat) : Nat := Id.run do
  let mut h : UInt64 := 14695981039346656037
  for i in [0:n] do
    h := (h ^^^ i.toUInt64) * 1099511628211
    h := (h <<< 3) ||| (h >>> 61)
  return h.toNat

/-- Wrapping 8-bit arithmetic. -/
def bytes (n : Nat) : Nat := Id.run do
  let mut a : UInt8 := 1
  let mut t : Nat := 0
  for i in [0:n] do
    a := a * 31 + i.toUInt8
    t := t + (a / 3).toNat + (a % 7).toNat
  return t

/-- xorshift32, a classic 32-bit generator. -/
def xorshift (n : Nat) : Nat := Id.run do
  let mut x : UInt32 := 2463534242
  let mut t : Nat := 0
  for _ in [0:n] do
    x := x ^^^ (x <<< 13)
    x := x ^^^ (x >>> 17)
    x := x ^^^ (x <<< 5)
    t := t + (x % 1000).toNat
  return t

/-- Conversions between widths, with truncation. -/
def convs (n : Nat) : Nat := Id.run do
  let mut t : Nat := 0
  for i in [0:n] do
    let a := i.toUInt32 * 2654435761
    t := t + a.toUInt16.toNat + a.toUInt8.toNat + (a.toUInt64 >>> 7).toNat % 100 +
      a.toUSize.toNat % 10
  return t

/-- Shifts by amounts at and above the width, and division by zero. -/
def edges (n : Nat) : Nat :=
  let a : UInt8 := n.toUInt8
  let b : UInt16 := n.toUInt16
  (a <<< 9).toNat + (a >>> 17).toNat + (a / 0).toNat + (a % 0).toNat +
    (b <<< 20).toNat + (b / (n.toUInt16 - n.toUInt16)).toNat + (0 - b).toNat

/-- Characters as 32-bit values. -/
def chars (n : Nat) : Nat := Id.run do
  let mut t : Nat := 0
  for i in [0:n] do
    let c := Char.ofNat (97 + i % 26)
    t := t + c.toNat + (if c.isAlpha then 1 else 0) + (if c.isDigit then 100 else 0)
  return t

/-- Print one test or all of them. -/
def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  let fs := [fnv, bytes, xorshift, convs, edges, chars]
  match args[1]? with
  | some i => IO.println ((fs[i.toNat!]!) n)
  | none => for f in fs do IO.println (f n)

#zempic fnv bytes xorshift convs edges chars to "build/Ints.hs"
