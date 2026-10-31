set_option linter.unusedVariables false

abbrev Elem := UInt32

def badRand (seed : Elem) : Elem :=
seed * 1664525 + 1013904223

def mkRandomArray : Nat → Elem → Array Elem → Array Elem
| 0,   seed, as => as
| i+1, seed, as => mkRandomArray i (badRand seed) (as.push seed)


-- ADAPTER (pure): upstream (tests/bench/qsort/Main.lean) builds 4000000 elements, runs core `Array.qsort`
-- and prints the size.  Here n is the length; the result packs size, first and last element.
def entry (n : Nat) : Nat :=
  let a := mkRandomArray n 0 (Array.mkEmpty n)
  let s := a.qsort (· < ·)
  (s.size * 4294967296 + s[0]!.toNat) * 4294967296 + s[s.size - 1]!.toNat
