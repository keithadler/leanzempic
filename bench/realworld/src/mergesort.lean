open List.MergeSort.Internal


-- ADAPTER (pure): upstream (tests/bench/mergeSort/Bench.lean) sorts four lists of length i*10^5 with
-- `List.MergeSort.Internal.mergeSortTR₂`, one of them filled by `IO.rand 0 1000`.  Here n is the length and
-- the random list uses a fixed LCG (IO.rand does not exist in pure code).  The result counts lists whose
-- length survived and that came out ordered, packed with the length of the last one.
def lcgList (n : Nat) : List Nat := Id.run do
  let mut seed : Nat := 12345
  let mut l : List Nat := []
  for _ in [0:n] do
    seed := (seed * 1103515245 + 12345) % 2147483648
    l := (seed / 65536 % 1001) :: l
  return l

def sortedOk : List Nat → Bool
  | a :: (b :: t) => decide (a ≤ b) && sortedOk (b :: t)
  | _ => true

def entry (n : Nat) : Nat :=
  let i₁ := (List.range' 1 n).reverse
  let i₂ := List.range n
  let i₃ := lcgList n
  let i₄ := (List.range (n / 1000)).flatMap (fun k => (k * 1000 + 1) :: (k * 1000) :: List.range' (k * 1000 + 2) 998)
  let o₁ := mergeSortTR₂ i₁
  let o₂ := mergeSortTR₂ i₂
  let o₃ := mergeSortTR₂ i₃
  let o₄ := mergeSortTR₂ i₄
  let ok := (if o₁.length == n && sortedOk o₁ then 1 else 0) + (if o₂.length == n && sortedOk o₂ then 1 else 0)
          + (if o₃.length == n && sortedOk o₃ then 1 else 0) + (if o₄.length == i₄.length && sortedOk o₄ then 1 else 0)
  ok * 1099511627776 + o₄.length
