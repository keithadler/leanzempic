import Zempic

/-- Count primes below `n` with a sieve of Eratosthenes. -/
def sieve (n : Nat) : Nat := Id.run do
  let mut isP : Array Bool := Array.replicate (n + 1) true
  let mut count := 0
  for i in [2:n + 1] do
    if isP[i]! then
      count := count + 1
      let mut j := i * i
      while j ≤ n do
        isP := isP.set! j false
        j := j + i
  return count

/-- Build an array by pushing, then prefixSum-sum it in place. -/
def prefixSum (n : Nat) : Nat := Id.run do
  let mut a : Array Nat := #[]
  for i in [0:n] do
    a := a.push (i % 17)
  for i in [1:n] do
    a := a.set! i (a[i]! + a[i - 1]!)
  return a[n - 1]! + a.size

/-- Map and fold over an array. -/
def mapFold (n : Nat) : Nat :=
  let a := (Array.range n).map (fun x => x * 3 % 11)
  a.foldl (· + ·) 0 + a.size

/-- Reverse in place with swaps and take a weighted checksum. -/
def rev (n : Nat) : Nat := Id.run do
  let mut a := Array.range n
  let mut i := 0
  let mut j := n - 1
  while i < j do
    a := a.swapIfInBounds i j
    i := i + 1
    j := j - 1
  let mut t := 0
  for k in [0:n] do
    t := (t + a[k]! * (k % 7 + 1)) % 1000003
  return t

/-- Use the array as a stack. -/
def stack (n : Nat) : Nat := Id.run do
  let mut s : Array Nat := #[]
  let mut t := 0
  for i in [0:n] do
    if i % 3 == 2 then
      t := t + s.back?.getD 0
      s := s.pop
    else
      s := s.push i
  return t + s.size

/-- Print one test or all of them. -/
def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  let fs := [sieve, prefixSum, mapFold, rev, stack]
  match args[1]? with
  | some i => IO.println ((fs[i.toNat!]!) n)
  | none => for f in fs do IO.println (f n)

#zempic sieve prefixSum mapFold rev stack to "build/Arrays.hs"
