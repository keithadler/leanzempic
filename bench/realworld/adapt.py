#!/usr/bin/env python3
"""Build src/<name>.lean from upstream/<name>.lean: keep everything before the program's `main`
(verbatim), then append a pure `entry : Nat -> Nat` adapter.  leanzempic cannot compile `IO`, so the
adapter replaces `main`'s printing/Task/forM plumbing with pure code that computes the SAME values and packs
them into one Nat (base 2^40 digits).  `python3 adapt.py` regenerates src/."""
import os, re
D = os.path.dirname(os.path.abspath(__file__))
CUT = {  # name -> regex of the line where upstream's IO section starts
 "binarytrees": r"^-- generate many trees", "const_fold": r"^open Expr\n\nunsafe def main",
 "deriv": r"^nestAux|^def nestAux", "qsort": r"^def main", "rbmap": r"^def main", "unionfind": r"^def main",
 "rbmap_checkpoint": r"^def main", "nat_repr": r"^def main",
 "rbmap_fbip": r"^def main", "qsort_core": r"^def main", "mergesort": r"^def main",
}
ADAPT = {
"binarytrees": """
-- ADAPTER (pure): same computation as upstream main; Task.spawn replaced by a direct call.
def pack (acc v : Nat) : Nat := acc * 1099511627776 + v

partial def depthLoop (d m acc : Nat) : Nat :=
  if d ≤ m then
    let n := 2 ^ (m - d + minN)
    depthLoop (d+2) m (pack acc (sumT (.ofNat d) (.ofNat n) 0).toNat)
  else acc

def entry (n : Nat) : Nat :=
  let maxN := Nat.max (minN + 2) n
  let stretchN := maxN + 1
  let c := check (make $ UInt32.ofNat stretchN)
  let long := make $ UInt32.ofNat maxN
  let acc := depthLoop minN maxN (pack 0 c.toNat)
  pack acc (check long).toNat
""",
"const_fold": """
open Expr

-- ADAPTER (pure): upstream main prints "v1 v2" for ONE tree of depth n (default 15).  Native Lean overflows
-- its 8 MB stack above depth 16 (non-tail recursion down a 2^n right spine), so to get a measurable run the
-- depth stays at 15 and the work is repeated `reps` times with a different leaf seed each time (so no
-- repetition can be shared).  reps=1 reproduces upstream's answer.
def entry (reps : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 0
  for r in [0:reps] do
    let e  := mkExpr 15 (1 + r)
    a := a + eval e
    b := b + eval (constFolding (reassoc e))
  return a * 1099511627776 + b
""",
"deriv": """
-- ADAPTER (pure): upstream's `nest deriv n f` in IO printed each step's count; here the counts are folded.
def derivP (acc : Nat) (f : Expr) : Nat × Expr :=
  let d := d "x" f
  (acc * 1099511627776 + (count d).toNat, d)

def nestP : Nat → Nat → Expr → Nat
  | 0,       acc, _ => acc
  | n+1,     acc, x => let (acc', x') := derivP acc x; nestP n acc' x'

end Expr

open Expr

def entry (n : Nat) : Nat :=
  nestP n 0 (pow (Var "x") (Var "x"))
""",
"qsort": """
-- ADAPTER (pure): upstream main loops n*n times in IO and throws if unsorted; here the loops are
-- pure and count the arrays that came out sorted.
def isSorted (a : Array Elem) : Bool := Id.run do
  for i in [0:a.size - 1] do
    if !(a[i]! <= a[i+1]!) then return false
  return true

def entry (n : Nat) : Nat := Id.run do
  let mut ok := 0
  for _ in [0:n] do
    for i in [0:n] do
      let xs := mkRandomArray i (UInt32.ofNat i) Array.empty
      let xs := qsort xs (fun a b => a < b)
      if isSorted xs then ok := ok + 1
  return ok
""",
"rbmap": """
-- ADAPTER (pure): upstream main prints the count of true values.
def entry (n : Nat) : Nat :=
  fold (fun _ v r => if v then r + 1 else r) (mkMap n) 0
""",
"rbmap_checkpoint": """
-- ADAPTER (pure): upstream main prints "<myLen> <v>"; freq fixed at 10 as in rbmap_checkpoint.lean.args.
def entry (n : Nat) : Nat :=
  let mList := mkMap n 10
  let v := fold (fun _ v r => if v then r + 1 else r) mList.head! 0
  myLen mList 0 * 1099511627776 + v
""",
"nat_repr": """
-- ADAPTER (pure): same loops as upstream main; the sum is the result.
def entry (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in *...n do
    for j in *...i do
      s := s + j.repr.length
  return s
""",
"rbmap_fbip": """
-- ADAPTER (pure): upstream main prints the count of true values (n comes from argv upstream).
def entry (n : Nat) : Nat :=
  fold (fun _ v r => if v then r + 1 else r) (mkMap n) 0
""",
"qsort_core": """
-- ADAPTER (pure): upstream (tests/bench/qsort/Main.lean) builds 4000000 elements, runs core `Array.qsort`
-- and prints the size.  Here n is the length; the result packs size, first and last element.
def entry (n : Nat) : Nat :=
  let a := mkRandomArray n 0 (Array.mkEmpty n)
  let s := a.qsort (· < ·)
  (s.size * 4294967296 + s[0]!.toNat) * 4294967296 + s[s.size - 1]!.toNat
""",
"mergesort": """
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
""",
"unionfind": """
-- ADAPTER (pure): upstream main prints "ok <v>"; here v (or 0 on Error) is the result.
def entry (n : Nat) : Nat :=
  match run (test n) with
  | (Except.ok v, _) => v
  | (Except.error _, _) => 0
""",
}
os.makedirs(f"{D}/src", exist_ok=True)
for name, rx in CUT.items():
    s = open(f"{D}/upstream/{name}.lean").read()
    m = re.search(rx, s, re.M)
    assert m, name
    head = s[:m.start()]
    if name == "deriv":
        # keep nestAux/nest/deriv out; also upstream `end Expr` follows them, which ADAPT re-emits
        pass
    if name == "qsort": head = head.replace("set_option pp.all true\n", "")
    open(f"{D}/src/{name}.lean", "w").write(head + ADAPT[name])
print("wrote src/")
