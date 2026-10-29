inductive Tree
  | nil
  | node (l r : Tree)
instance : Inhabited Tree := ⟨.nil⟩

-- This function has an extra argument to suppress the
-- common sub-expression elimination optimization
partial def make' (n d : UInt32) : Tree :=
  if d = 0 then .node .nil .nil
  else .node (make' n (d - 1)) (make' (n + 1) (d - 1))

-- build a tree
def make (d : UInt32) := make' d d

def check : Tree → UInt32
  | .nil => 0
  | .node l r => 1 + check l + check r

def minN := 4

def out (s : String) (n : Nat) (t : UInt32) : IO Unit :=
  IO.println s!"{s} of depth {n}\t check: {t}"

-- allocate and check lots of trees
partial def sumT (d i t : UInt32) : UInt32 :=
  if i = 0 then t
  else
    let a := check (make d)
    sumT d (i-1) (t + a)


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
