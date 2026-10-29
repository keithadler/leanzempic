# name -> Lean source defining `entry : Nat → Nat` (a checksum of some computation on n).
P = {}
def add(name, src): P[name] = src.strip("\n")

add("int_arith", '''
def step (acc : Int) (i : Nat) : Int :=
  let x : Int := (i : Int) - 7
  (acc * 3 + x * x - x / 2 + x % 5) % 100003
def entry (n : Nat) : Nat :=
  let r := (List.range (n + 1)).foldl step (-5)
  r.natAbs + (r.toNat) + (Int.emod r 7).toNat
''')
add("float_math", '''
def entry (n : Nat) : Nat :=
  let rec go (i : Nat) (acc : Float) (fuel : Nat) : Float :=
    match fuel with
    | 0 => acc
    | f + 1 => go (i + 1) (acc + Float.sqrt (i.toFloat) * 1.5) f
  (go 0 0.0 (n + 1)).floor.toUInt64.toNat
''')
add("string_split", '''
def entry (n : Nat) : Nat :=
  let s := String.intercalate "," ((List.range (n + 1)).map toString)
  let parts := s.splitOn ","
  parts.foldl (fun acc p => acc + p.length * 3 + p.toNat!) 0
''')
add("string_chars", '''
def entry (n : Nat) : Nat :=
  let s := String.join ((List.range (n + 1)).map fun i => s!"a{i}b ")
  s.foldl (fun acc c => acc + (if c.isDigit then 1 else if c.isAlpha then 7 else 0) + c.toNat % 3) 0
''')
add("string_pos", '''
def entry (n : Nat) : Nat :=
  let s := String.join ((List.range (n + 1)).map fun i => toString (i * i))
  (s.drop 2).length + (s.take 5).length + (s.front.toNat) + (s.endPos.offset.byteIdx)
''')
add("list_mergesort", '''
def gen (n : Nat) : List Nat := (List.range (n + 1)).map fun i => (i * 7919 + 13) % 1009
def entry (n : Nat) : Nat :=
  let s := (gen n).mergeSort
  s.foldl (fun acc x => (acc * 31 + x) % 1000003) 0
''')
add("array_qsort", '''
def entry (n : Nat) : Nat :=
  let a := ((List.range (n + 1)).map fun i => (i * 7919 + 13) % 1009).toArray
  let s := a.qsort (· < ·)
  s.foldl (fun acc x => (acc * 31 + x) % 1000003) 0
''')
add("hashmap", '''
import Std.Data.HashMap
def entry (n : Nat) : Nat :=
  let m : Std.HashMap Nat Nat := (List.range (n + 1)).foldl (fun m i => m.insert (i % 17) (m.getD (i % 17) 0 + i)) {}
  m.fold (fun acc k v => acc + k * 3 + v) 0 + m.size
''')
add("option_chain", '''
def f (x : Nat) : Option Nat := if x % 3 == 0 then none else some (x * 2)
def entry (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc i => acc + ((f i).bind f |>.map (· + 1) |>.getD 1000)) 0
''')
add("except_monad", '''
def check (x : Nat) : Except String Nat :=
  if x > 1000 then throw "big" else pure (x + 1)
def run (n : Nat) : Except String Nat := do
  let mut acc := 0
  for i in [0:n+1] do
    acc := acc + (← check (i * 40))
  return acc
def entry (n : Nat) : Nat :=
  match run n with
  | .ok v => v
  | .error e => e.length + 77
''')
add("state_monad", '''
def tick (i : Nat) : StateM Nat Unit := modify fun s => (s * 3 + i) % 100003
def run (n : Nat) : StateM Nat Unit := do
  for i in [0:n+1] do tick i
def entry (n : Nat) : Nat := ((run n).run 1).2
''')
add("struct_update", '''
structure P where
  x : Nat
  y : Nat
  tag : Bool
structure Q where
  p : P
  count : Nat
def stepQ (q : Q) (i : Nat) : Q :=
  { q with p := { q.p with x := q.p.x + i, tag := !q.p.tag }, count := q.count + 1 }
def entry (n : Nat) : Nat :=
  let q := (List.range (n + 1)).foldl stepQ ⟨⟨0, 5, true⟩, 0⟩
  q.p.x + q.p.y + q.count + (if q.p.tag then 1 else 0)
''')
add("mutual_rec", '''
mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end
def entry (n : Nat) : Nat := (List.range (n + 1)).foldl (fun acc i => acc + (if isEven i then i else 1)) 0
''')
add("typeclass", '''
class Shape (α : Type) where
  area : α → Nat
  name : α → Nat
structure Sq where s : Nat
structure Rect where (w h : Nat)
instance : Shape Sq := ⟨fun x => x.s * x.s, fun _ => 1⟩
instance : Shape Rect := ⟨fun r => r.w * r.h, fun _ => 2⟩
def total {α} [Shape α] (xs : List α) : Nat := xs.foldl (fun acc x => acc + Shape.area x + Shape.name x) 0
def entry (n : Nat) : Nat :=
  total ((List.range (n + 1)).map fun i => Sq.mk i) + total ((List.range (n + 1)).map fun i => Rect.mk i (i + 1))
''')
add("expr_tree", '''
inductive E where
  | num : Nat → E
  | add : E → E → E
  | mul : E → E → E
  | neg : E → E
def build : Nat → E
  | 0 => .num 3
  | n + 1 => if n % 3 == 0 then .add (build n) (.num n) else if n % 3 == 1 then .mul (build n) (.num 2) else .neg (build n)
def eval : E → Int
  | .num k => k
  | .add a b => eval a + eval b
  | .mul a b => (eval a * eval b) % 1000003
  | .neg a => - eval a
def entry (n : Nat) : Nat := (eval (build n)).natAbs
''')
add("fin_arith", '''
def entry (n : Nat) : Nat :=
  let m := n + 3
  let rec go (i : Nat) (acc : Fin 97) (fuel : Nat) : Fin 97 :=
    match fuel with
    | 0 => acc
    | f + 1 => go (i + 1) (acc * 3 + Fin.ofNat 97 i) f
  (go 0 0 m).val
''')
add("bitvec", '''
def entry (n : Nat) : Nat :=
  let rec go (i : Nat) (acc : BitVec 32) (fuel : Nat) : BitVec 32 :=
    match fuel with
    | 0 => acc
    | f + 1 => go (i + 1) ((acc <<< 3) ^^^ (acc >>> 5) + BitVec.ofNat 32 i) f
  (go 0 1 (n + 1)).toNat
''')
add("char_ops", '''
def entry (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc i =>
    let c := Char.ofNat (65 + i % 26)
    acc + c.toNat + (if c.isUpper then 1 else 0) + c.toLower.toNat) 0
''')
add("for_loop_ctl", '''
def entry (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n+1] do
    if i % 7 == 3 then continue
    if acc > 50000 then break
    acc := acc + i * i
  return acc
''')
add("while_loop", '''
def entry (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut acc := 1
  while i < n + 1 do
    acc := (acc * 5 + i) % 1000003
    i := i + 1
  return acc
''')
add("matrix_mul", '''
def mk (n : Nat) (s : Nat) : Array (Array Nat) :=
  Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => (i.val * s + j.val) % 10
def mul (a b : Array (Array Nat)) : Array (Array Nat) :=
  a.map fun row => (List.range b.size).toArray.map fun j =>
    (List.range row.size).foldl (fun acc k => acc + row[k]! * b[k]![j]!) 0
def entry (n : Nat) : Nat :=
  let m := n % 12 + 2
  let c := mul (mk m 3) (mk m 5)
  c.foldl (fun acc row => row.foldl (· + ·) acc) 0
''')
add("list_funcs", '''
def entry (n : Nat) : Nat :=
  let xs := List.range (n + 1)
  let ys := xs.zipWith (· * ·) (xs.reverse)
  let zs := ys.filterMap fun y => if y % 2 == 0 then some (y / 2) else none
  (zs.take 10).foldl (· + ·) 0 + (xs.drop 3).length + (xs.find? (· > 4)).getD 0
    + (xs.foldr (fun x acc => (acc * 3 + x) % 9973) 1)
''')
add("bignum", '''
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n
def digitSum (k : Nat) : Nat := (toString k).foldl (fun a c => a + (c.toNat - 48)) 0
def entry (n : Nat) : Nat := digitSum (fact (n * 4 + 5))
''')
add("gcd_pow", '''
def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1
  let mut b := b % m
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then r := r * b % m
    b := b * b % m
    e := e / 2
  return r
def entry (n : Nat) : Nat := powMod (n + 2) (n * 1000 + 17) 1000003 + Nat.gcd (n * 12) 18 + 2 ^ (n % 20)
''')
add("uint64_hash", '''
def fnv (s : List UInt8) : UInt64 := s.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037
def entry (n : Nat) : Nat :=
  (fnv ((List.range (n + 1)).map fun i => i.toUInt8)).toNat % 1000000007
''')
add("bytearray", '''
def entry (n : Nat) : Nat := Id.run do
  let mut b := ByteArray.empty
  for i in [0:n+1] do b := b.push (i * 7).toUInt8
  let mut s := 0
  for i in [0:b.size] do s := s + (b.get! i).toNat
  return s + b.size
''')
add("tuples", '''
def swap3 (t : Nat × Nat × Nat) : Nat × Nat × Nat := (t.2.2, t.1, t.2.1)
def entry (n : Nat) : Nat :=
  let (a, b, c) := (List.range (n + 1)).foldl (fun t i => let (x, y, z) := swap3 t; (x + i, y * 2 % 1009, z + 1)) (1, 2, 3)
  a + b + c
''')
add("sum_type", '''
def classify (i : Nat) : Sum Nat String := if i % 2 == 0 then .inl i else .inr (toString i)
def entry (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc i => match classify i with | .inl k => acc + k | .inr s => acc + s.length) 0
''')
add("string_build", '''
def entry (n : Nat) : Nat :=
  let s := (List.range (n + 1)).foldl (fun s i => s ++ toString i ++ ";") ""
  s.length + (String.intercalate "-" ["a", "bb", "ccc"]).length + (repr n).pretty.length
''')
add("closures", '''
def mkAdders (n : Nat) : List (Nat → Nat) := (List.range (n + 1)).map fun i => fun x => x * 2 + i
def entry (n : Nat) : Nat := (mkAdders n).foldl (fun acc f => f acc % 100003) 7
''')
add("higher_order", '''
def compose (f g : Nat → Nat) : Nat → Nat := fun x => f (g x)
def twice (f : Nat → Nat) := compose f f
def entry (n : Nat) : Nat := (twice (twice (· + 3))) n + (compose (· * 2) (· + 1)) n
''')
add("wf_recursion", '''
def collatz (n : Nat) (fuel : Nat := 1000) : Nat :=
  if n ≤ 1 then 0 else match fuel with
    | 0 => 0
    | f + 1 => 1 + collatz (if n % 2 == 0 then n / 2 else 3 * n + 1) f
def euclid (a b : Nat) : Nat := if h : b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)
def entry (n : Nat) : Nat := collatz (n + 7) + euclid (n * 6 + 12) 18
''')
add("array_funcs", '''
def entry (n : Nat) : Nat :=
  let a := (Array.range (n + 1)).map (· * 3)
  let b := a.filter (· % 2 == 0)
  let c := (a.zip b).map fun (x, y) => x + y
  (a.foldl (· + ·) 0) + b.size + c.size + (if a.any (· > 20) then 1 else 0) + (if a.all (· < 100000) then 2 else 0)
    + (if a.contains 9 then 4 else 0) + a.reverse.size + (a.extract 1 4).size + (a ++ b).size
''')
add("array_word_paths", '''
def entry (n : Nat) : Nat :=
  let a := Array.range (n + 1)
  let b := a.map (fun x => x % 2 == 0)
  let c := a.map (fun x => (x, x + 1))
  let d := a.map (· + 5)
  -- distinct capacities: two identical `Array.mkEmpty 4` are merged by Lean's CSE, and the buffer
  -- kind of the first would then also serve the other element type
  let u8 : Array UInt8 := Id.run do
    let mut r := Array.mkEmpty 5
    for x in [0:n + 1] do r := r.push x.toUInt8
    return r
  let e := u8.map (fun x => x + 250)
  let v := u8.map (fun x => x.toNat * 1000)
  let usz := a.map (fun x => x.toUSize * 3)
  let f := (a ++ d).extract 1 (n / 2 + 2)
  let g := (a.zip d).reverse
  let h := a.set! 1 100
  let k := a.push 7 |>.push 8
  let sw := (a.swapIfInBounds 0 n).swapIfInBounds 1 2
  let big := if n % 2 == 1 then 2 ^ 70 else 0
  let r := Id.run do
    let mut arr : Array Nat := Array.mkEmpty 6
    for i in [0:n + 1] do arr := arr.push (i * i)
    let snap := arr
    for i in [0:n + 1] do arr := arr.set! i (arr[i]! + 1)
    for i in [0:n] do arr := arr.set! (i + 1) (arr[i]! + arr[i + 1]!)
    return (snap, arr)
  let w := (a.filter (· % 3 == 0)).foldl (· + ·) 0
  r.1.foldl (· + ·) 0 + r.2.foldl (fun acc x => acc * 5 + x) 0 + w + (b.filter id).size + c.foldl (fun acc (x, y) => acc + x * y) 0 + d.foldl (· + ·) 0
    + e.foldl (fun acc x => acc + x.toNat) 0 + v.foldl (· + ·) 0 + usz.foldl (fun acc x => acc + x.toNat) 0
    + f.size + f.foldl (· + ·) 0 + g.size + g.foldl (fun acc (x, y) => acc * 3 + x + y) 1
    + h.getD 1 0 + a.getD 1 0 + k.size + k.getD (n + 2) 0 + sw.foldl (fun acc x => acc * 7 + x) 0
    + a.size + big % 1000003 + (if big > 0 then 1 else 0)
''')
add("array_narrow_paths", '''
-- UInt8/16/32/64 and Char element arrays: push, get!, getD, set!, swap and fold, in place and on a kept snapshot.
def mix32 (x : UInt32) : UInt32 := x * 1664525 + 1013904223
def mix64 (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

def fill32 (n : Nat) : Array UInt32 := Id.run do
  let mut a : Array UInt32 := Array.mkEmpty 3
  let mut s : UInt32 := 7
  for _ in [0:n] do
    a := a.push s
    s := mix32 s
  return a

def fill64 (n : Nat) : Array UInt64 := Id.run do
  let mut a : Array UInt64 := Array.mkEmpty 5
  let mut s : UInt64 := 11
  for _ in [0:n] do
    a := a.push s
    s := mix64 s
  return a

def fill16 (n : Nat) : Array UInt16 := Id.run do
  let mut a : Array UInt16 := Array.mkEmpty 6
  for i in [0:n] do a := a.push (i * 40503).toUInt16
  return a

def fill8 (n : Nat) : Array UInt8 := Id.run do
  let mut a : Array UInt8 := Array.mkEmpty 7
  for i in [0:n] do a := a.push (i * 37 + 5).toUInt8
  return a

def fillC (n : Nat) : Array Char := Id.run do
  let mut a : Array Char := Array.mkEmpty 9
  for i in [0:n] do a := a.push (Char.ofNat (97 + i % 26))
  return a

-- an insertion sort by swaps, then a reversal, reading with get! and writing with swapIfInBounds
def isort32 (a0 : Array UInt32) : Array UInt32 := Id.run do
  let mut a := a0
  for i in [1:a.size] do
    let mut j := i
    while j > 0 && a[j]! < a[j - 1]! do
      a := a.swapIfInBounds j (j - 1)
      j := j - 1
  return a

-- in-place writes with set! (the array is owned), including a write past the end that must do nothing
def bump (n : Nat) : Nat := Id.run do
  let mut a := fill32 n
  let mut b := fill64 n
  let mut c := fill16 n
  let mut d := fill8 n
  for i in [0:n + 3] do
    a := a.set! i (a[i]! * 3 + i.toUInt32)
    b := b.set! i (b[i]! * 5 + i.toUInt64)
    c := c.set! i (c[i]! * 7 + i.toUInt16)
    d := d.set! i (d[i]! * 9 + i.toUInt8)
    a := a.swapIfInBounds i (n + 1 - i)
    b := b.swapIfInBounds (i / 2) (n + 5 - i)
    c := c.swapIfInBounds i (i * 2 % (n + 2))
    d := d.swapIfInBounds (n + 6 - i) i
  return a.foldl (fun acc x => (acc + x.toNat) % 1000003) 0 + b.foldl (fun acc x => (acc + x.toNat) % 1000003) 0
    + c.foldl (fun acc x => (acc + x.toNat) % 1000003) 0 + d.foldl (fun acc x => (acc + x.toNat) % 1000003) 0

def entry (n : Nat) : Nat :=
  let n := n % 300 + 2
  let bumped := bump n
  let a := fill32 n
  let snap := a
  let s := isort32 a
  let b := fill64 n
  let b2 := b.set! 1 12345678901234567 |>.set! (n - 1) 0
  let c := fill16 n
  let c2 := c.map (fun x => x + 60000)
  let d := fill8 n
  let d2 := (d.swapIfInBounds 0 (n - 1)).set! 2 250
  let e := fillC n
  let e2 := e.swapIfInBounds 1 2
  let sorted := (List.range (s.size - 1)).all fun i => s[i]! <= s[i + 1]!
  let loopSum := Id.run do
    let mut t : Nat := 0
    for x in s do t := (t * 3 + x.toNat) % 1000003
    for x in b2 do t := (t * 5 + x.toNat) % 1000003
    for x in d2 do t := (t * 7 + x.toNat) % 1000003
    for x in c2 do t := (t * 11 + x.toNat) % 1000003
    return t
  s.foldl (fun acc x => (acc * 31 + x.toNat) % 1000003) 0
    + snap.foldl (fun acc x => (acc * 17 + x.toNat) % 1000003) 0
    + b2.foldl (fun acc x => (acc * 13 + x.toNat) % 1000003) 0 + b.foldl (fun acc x => (acc + x.toNat) % 1000003) 0
    + c2.foldl (fun acc x => (acc * 7 + x.toNat) % 1000003) 0 + c.foldl (fun acc x => (acc + x.toNat) % 1000003) 0
    + d2.foldl (fun acc x => (acc * 5 + x.toNat) % 1000003) 0 + d.foldl (fun acc x => (acc + x.toNat) % 1000003) 0
    + e2.foldl (fun acc x => (acc * 3 + x.toNat) % 1000003) 0 + e.foldl (fun acc x => (acc + x.toNat) % 1000003) 0
    + bumped + loopSum + (if sorted then 1 else 0) + (a.getD (n + 5) 99).toNat + (b.getD (n + 5) 98).toNat + (c.getD (n + 5) 97).toNat
    + (d.getD (n + 5) 96).toNat + (e.getD (n + 5) 'z').toNat + (s.pop.pop.size)
''')
add("array_list_conv", '''
def entry (n : Nat) : Nat :=
  let l := (List.range (n + 1)).toArray.toList
  let a := Array.replicate (n + 1) 3
  l.length + a.size + a.foldl (· + ·) 0
''')
add("nat_repr", '''
def entry (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc i => acc + (toString (i * 977)).toNat! % 13) 0
''')
add("string_compare", '''
def entry (n : Nat) : Nat :=
  let ss := (List.range (n + 1)).map fun i => toString ((i * 37) % 101)
  let sorted := ss.toArray.qsort (· < ·)
  sorted.foldl (fun acc s => acc * 3 + s.length) 0 % 100003 + (if "abc" < "abd" then 1 else 0) + (if "x" == "x" then 2 else 0)
''')
add("array_option", '''
def entry (n : Nat) : Nat :=
  let a : Array (Option Nat) := (Array.range (n + 1)).map fun i => if i % 3 == 0 then none else some i
  a.foldl (fun acc o => acc + o.getD 100) 0
''')
add("deriving", '''
structure K where
  a : Nat
  b : Bool
  deriving BEq, Hashable, Ord, Repr
def entry (n : Nat) : Nat :=
  let xs := (List.range (n + 1)).map fun i => K.mk (i % 5) (i % 2 == 0)
  (xs.filter (· == K.mk 2 true)).length + (hash (K.mk 1 false)).toNat % 7 + (if compare (K.mk 1 true) (K.mk 2 false) == .lt then 3 else 0)
''')
add("nat_fold", '''
def entry (n : Nat) : Nat :=
  Nat.fold (n + 1) (fun i _ acc => acc + i * 2) 0
''')
add("int_array", '''
def entry (n : Nat) : Nat :=
  let a : Array Int := (Array.range (n + 1)).map fun (i : Nat) => (i : Int) - 20
  (a.foldl (fun acc x => acc + x * x) 0).toNat + (a.foldl (fun acc x => acc + x) 0).natAbs
''')
add("parser_monad", '''
structure Parser (α : Type) where
  run : List Char → Option (α × List Char)
instance : Monad Parser where
  pure a := ⟨fun s => some (a, s)⟩
  bind p f := ⟨fun s => match p.run s with | none => none | some (a, r) => (f a).run r⟩
def item : Parser Char := ⟨fun | [] => none | c :: cs => some (c, cs)⟩
def two : Parser (Char × Char) := do
  let a ← item
  let b ← item
  pure (a, b)
def entry (n : Nat) : Nat :=
  let s := (List.range (n + 3)).map fun i => Char.ofNat (97 + i % 26)
  match two.run s with
  | some ((a, b), r) => a.toNat + b.toNat + r.length
  | none => 0
''')
add("subtype_index", '''
def sumArr (a : Array Nat) : Nat := Id.run do
  let mut s := 0
  for h : i in [0:a.size] do
    s := s + a[i]'(Membership.get_elem_helper h rfl)
  return s
def entry (n : Nat) : Nat := sumArr ((Array.range (n + 1)).map (· + 1))
''')
add("usize_loop", '''
def entry (n : Nat) : Nat :=
  let a := (Array.range (n + 1)).map (· + 2)
  let rec go (i : USize) (acc : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | f + 1 => if h : i.toNat < a.size then go (i + 1) (acc + a.uget i (by simpa using h)) f else acc
  go 0 0 (n + 2)
''')
add("string_get", '''
def loop (str : String) (i : Nat) (fuel : Nat) (acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | f + 1 => if i < str.utf8ByteSize then loop str (i + 1) f (acc + (str.get ⟨i⟩).toNat) else acc
def entry (n : Nat) : Nat := loop (String.join ((List.range (n + 1)).map toString)) 0 100000 0
''')
add("thunk_lazy", '''
def entry (n : Nat) : Nat :=
  let t : Thunk Nat := Thunk.mk fun _ => n * 7
  t.get + t.get
''')
add("array_2d_loop", '''
def entry (n : Nat) : Nat := Id.run do
  let m := n % 20 + 3
  let mut g : Array (Array Nat) := Array.replicate m (Array.replicate m 0)
  for i in [0:m] do
    for j in [0:m] do
      g := g.set! i (g[i]!.set! j (i * j + 1))
  let mut s := 0
  for row in g do
    for x in row do s := s + x
  return s
''')
add("list_pattern", '''
def f : List Nat → Nat
  | [] => 0
  | [a] => a
  | a :: b :: rest => a * b % 1009 + f rest
def entry (n : Nat) : Nat := f (List.range (n + 1))
''')
add("nat_match_lit", '''
def g : Nat → Nat
  | 0 => 10
  | 1 => 20
  | 2 => 30
  | k + 3 => g k + 1
def entry (n : Nat) : Nat := g (n * 2)
''')

# ---- wave 2
add("str_ops", '''
def entry (n : Nat) : Nat :=
  let s := "  Hello, World " ++ toString n ++ "  "
  let t := s.trim
  (t.toUpper.length) + (t.toLower.length) + (if t.startsWith "Hello" then 1 else 0) + (if t.endsWith "9" then 2 else 0)
    + (t.replace "o" "00").length + (if t.contains 'W' then 4 else 0) + (t.toList.reverse.length) + (String.join ["a", "b"]).length
''')
add("str_map_any", '''
def entry (n : Nat) : Nat :=
  let s := (List.range (n + 3)).foldl (fun s i => s.push (Char.ofNat (97 + i % 26))) ""
  (s.map Char.toUpper).length + (if s.any (· == 'c') then 1 else 0) + (if s.all Char.isAlpha then 2 else 0) + (s.get! 0).toNat
''')
add("int_repr", '''
def entry (n : Nat) : Nat :=
  let xs : List Int := (List.range (n + 1)).map fun (i : Nat) => (i : Int) * (if i % 2 == 0 then 1 else -1) - 3
  (xs.map (fun x => (toString x).length)).foldl (· + ·) 0 + (xs.foldl (fun a x => a + x * x) 0).toNat
''')
add("int_div_cases", '''
def entry (n : Nat) : Nat :=
  let xs : List Int := [(-7 : Int), 7, -8, 0, (n : Int), -(n : Int) - 1]
  let ys : List Int := [2, -2, 3, -3, 5]
  (xs.foldl (fun a x => ys.foldl (fun b y => b + (x / y).natAbs * 3 + (x % y).natAbs + (Int.tdiv x y).natAbs + (Int.tmod x y).natAbs + (Int.fdiv x y).natAbs) a) 0)
''')
add("int_match", '''
def sgn : Int → Nat
  | .ofNat 0 => 0
  | .ofNat (_ + 1) => 1
  | .negSucc _ => 2
def entry (n : Nat) : Nat := (List.range (n + 1)).foldl (fun (a : Nat) (i : Nat) => a + sgn ((i : Int) - 5) * (i + 1)) 0
''')
add("int_pow_cmp", '''
def entry (n : Nat) : Nat :=
  let b : Int := -3
  ((b ^ (n % 10)).natAbs) + (if b < 0 then 1 else 0) + (if b ≤ -3 then 2 else 0) + (max b 5).toNat + (min b 5).natAbs
''')
add("float_ops", '''
def entry (n : Nat) : Nat :=
  let x : Float := n.toFloat + 0.5
  let y := Float.sin x + Float.cos x * 2.0 - Float.exp (x / 50.0) + Float.log (x + 1.0)
  (y * 1000.0).abs.floor.toUInt64.toNat + (if x < 3.5 then 1 else 0) + (if x == 0.5 then 2 else 0) + x.ceil.toUInt32.toNat
''')
add("float_array", '''
def entry (n : Nat) : Nat :=
  let a : Array Float := (Array.range (n + 1)).map fun i => i.toFloat * 0.25
  let s := a.foldl (· + ·) 0.0
  s.toUInt64.toNat + (Float.ofInt (-3 : Int)).abs.toUInt8.toNat
''')
add("nat_bits", '''
def entry (n : Nat) : Nat :=
  Nat.log2 (n + 1) + (n <<< 3) + (n >>> 1) + (if Nat.testBit n 0 then 5 else 0) + (n &&& 6) + (n ||| 9) + (n ^^^ 5) + Nat.pred n + min n 4 + max n 4
''')
add("nat_digits", '''
def entry (n : Nat) : Nat :=
  let ds := Nat.toDigits 10 (n * 12345 + 6789)
  ds.length + ds.foldl (fun a c => a + c.toNat) 0 + (Nat.toDigits 2 n).length
''')
add("list_misc", '''
def entry (n : Nat) : Nat :=
  let xs := List.range (n + 2)
  let (a, b) := xs.partition (· % 3 == 0)
  a.length * 7 + b.length + (xs.head!) + (xs.tail!).length + (xs.getLast!) + (xs.foldl max 0) + xs.sum
    + (List.replicate 3 n).length + (xs.flatMap fun x => [x, x]).length + (xs.zipIdx.map (·.2)).sum + (if xs.any (· > 3) then 1 else 0) + (xs.eraseDups.length)
''')
add("list_span_group", '''
def entry (n : Nat) : Nat :=
  let xs := (List.range (n + 6)).map (· / 3)
  let (a, b) := xs.span (· < 1)
  a.length + b.length + (xs.splitBy (· == ·)).length + (xs.dropWhile (· < 2)).length + (xs.takeWhile (· < 2)).length
''')
add("array_misc", '''
def entry (n : Nat) : Nat :=
  let a := (Array.range (n + 5)).map (· * 7 % 11)
  (a.back!) + (a.pop.size) + ((a.findIdx? (· > 3)).getD 0) + ((a.mapIdx fun i x => i + x).foldl (· + ·) 0)
    + (a.insertionSort (· < ·))[0]! + (a.foldr (· + ·) 0) + ((a.zipIdx).size) + (if a.isEmpty then 1 else 0)
''')
add("shared_rare_write", '''
def maybeSet (a : Array Nat) (i : Nat) : Array Nat := if i % 7 == 0 then a.set! i 0 else a
def entry (n : Nat) : Nat :=
  let a := (Array.range (n + 20)).map (· + 1)
  let t := (List.range (n + 20)).foldl (fun acc i => acc + (maybeSet a i).size + (maybeSet a i)[i]!) 0
  t + a[3]! + a.foldl (· + ·) 0
''')
add("shared_always_write", '''
def bump (a : Array Nat) (i : Nat) : Array Nat := a.set! (i % a.size) (i + 1)
def entry (n : Nat) : Nat :=
  let a := (Array.range (n + 20)).map (· * 3)
  let t := (List.range (n + 20)).foldl (fun acc i => acc + (bump a i)[i % a.size]!) 0
  t + a.foldl (· + ·) 0
''')
add("shared_twice", '''
def swapEnds (a : Array Nat) : Array Nat := if a.size < 2 then a else a.swapIfInBounds 0 (a.size - 1)
def twice (a : Array Nat) : Nat := (swapEnds a)[0]! + (swapEnds a)[0]! + a[0]!
def entry (n : Nat) : Nat :=
  let a := (Array.range (n + 5)).map (· + 10)
  let b := a.push 99
  twice a + twice b + a.size + b.size
''')
add("subarray", '''
def entry (n : Nat) : Nat := Id.run do
  let a := (Array.range (n + 8)).map (· + 1)
  let mut s := 0
  for x in a[2:6] do s := s + x
  return s + (a[3:].foldl (· + ·) 0) + a[1:4].size
''')
add("state_except_stack", '''
def step (i : Nat) : StateT Nat (Except String) Unit := do
  let s ← get
  if s > 10000 then throw "overflow"
  set (s * 2 + i)
def run (n : Nat) : Except String Nat := do
  let ((), s) ← (do for i in [0:n+1] do step i : StateT Nat (Except String) Unit).run 1
  return s
def entry (n : Nat) : Nat := match run n with | .ok v => v | .error e => e.length * 1000
''')
add("reader_monad", '''
def sumWith : List Nat → ReaderM Nat Nat
  | [] => pure 0
  | x :: xs => do
    let k ← read
    let r ← sumWith xs
    pure (x * k + r)
def entry (n : Nat) : Nat := (sumWith (List.range (n + 1))).run 3
''')
add("exceptt_id", '''
def f (x : Nat) : ExceptT String Id Nat := if x == 7 then throw "seven" else pure (x + 1)
def go (n : Nat) : ExceptT String Id Nat := do
  let mut acc := 0
  for i in [0:n+1] do acc := acc + (← f i)
  return acc
def entry (n : Nat) : Nat := match (go n).run with | .ok v => v | .error e => e.length
''')
add("hashset", '''
import Std.Data.HashSet
def entry (n : Nat) : Nat :=
  let s : Std.HashSet Nat := (List.range (n * 3 + 1)).foldl (fun s i => s.insert (i % 11)) {}
  s.size + (if s.contains 4 then 100 else 0) + (s.toList.foldl (· + ·) 0)
''')
add("hashmap_str", '''
import Std.Data.HashMap
def entry (n : Nat) : Nat :=
  let m : Std.HashMap String Nat := (List.range (n + 1)).foldl (fun m i => m.insert (toString (i % 7)) i) {}
  (m.getD "3" 0) + m.size + (m.toList.foldl (fun a (k, v) => a + k.length + v) 0) + (if m.contains "5" then 1 else 0)
''')
add("class_default", '''
class Animal (α : Type) where
  name : α → Nat
  legs : α → Nat := fun _ => 4
structure Dog where id : Nat
structure Bird where id : Nat
instance : Animal Dog := { name := fun d => d.id }
instance : Animal Bird := { name := fun b => b.id + 100, legs := fun _ => 2 }
def info {α} [Animal α] (a : α) : Nat := Animal.name a * 10 + Animal.legs a
def entry (n : Nat) : Nat := info (Dog.mk n) + info (Bird.mk n)
''')
add("instance_add", '''
structure V where (x y : Int)
instance : Add V := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩
instance : Mul V := ⟨fun a b => ⟨a.x * b.x - a.y * b.y, a.x * b.y + a.y * b.x⟩⟩
def entry (n : Nat) : Nat :=
  let z := (List.range (n % 7 + 1)).foldl (fun (acc : V) (i : Nat) => acc * V.mk 1 (i : Int) + V.mk 1 1) (V.mk 1 0)
  z.x.natAbs % 100003 + z.y.natAbs % 100003
''')
add("functor_tree", '''
inductive T (α : Type) where
  | leaf : T α
  | node : T α → α → T α → T α
def T.map {α β} (f : α → β) : T α → T β
  | .leaf => .leaf
  | .node l x r => .node (l.map f) (f x) (r.map f)
def T.insert (t : T Nat) (v : Nat) : T Nat :=
  match t with
  | .leaf => .node .leaf v .leaf
  | .node l x r => if v < x then .node (l.insert v) x r else .node l x (r.insert v)
def T.sum : T Nat → Nat
  | .leaf => 0
  | .node l x r => l.sum + x + r.sum
def entry (n : Nat) : Nat :=
  let t := (List.range (n + 1)).foldl (fun t i => t.insert ((i * 37) % 101)) T.leaf
  (t.map (· * 2)).sum
''')
add("vec_indexed", '''
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
def Vec.toList : Vec α n → List α
  | .nil => []
  | .cons x xs => x :: xs.toList
def mk : (k : Nat) → Vec Nat k
  | 0 => .nil
  | k + 1 => .cons k (mk k)
def entry (n : Nat) : Nat := (mk (n % 20)).toList.foldl (· + ·) 0
''')
add("fn_fields", '''
structure Op where
  name : Nat
  f : Nat → Nat → Nat
def ops : List Op := [⟨1, (· + ·)⟩, ⟨2, (· * ·)⟩, ⟨3, fun a b => a - b⟩]
def entry (n : Nat) : Nat := ops.foldl (fun acc o => o.f acc (n + o.name) % 100003) 7
''')
add("partial_def", '''
partial def loop (i acc : Nat) : Nat := if i > 50 then acc else loop (i + 1) (acc + i * i)
partial def collatz (n steps : Nat) : Nat := if n ≤ 1 then steps else collatz (if n % 2 == 0 then n / 2 else 3 * n + 1) (steps + 1)
def entry (n : Nat) : Nat := loop n 0 + collatz (n + 3) 0
''')
add("where_let_rec", '''
def entry (n : Nat) : Nat := go (n + 1) 0 + helper n
where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | k + 1, acc => go k (acc + k * 2)
  helper (m : Nat) : Nat := m * m + 1
''')
add("decide_props", '''
def entry (n : Nat) : Nat :=
  (if h : n < 10 then n else 10) + (if decide (n % 2 = 0) then 3 else 4) + (if n ∣ 12 then 1 else 0 : Nat) + (if (n, 1) = (n, 1) then 1 else 0)
''')
add("uint_conv", '''
def entry (n : Nat) : Nat :=
  let a : UInt8 := n.toUInt8 * 37
  let b : UInt16 := a.toUInt16 * 1000
  let c : UInt32 := b.toUInt32 * 70000
  let d : UInt64 := c.toUInt64 * 5000000000
  let e : USize := d.toUSize + 1
  a.toNat + b.toNat + c.toNat + d.toNat % 1000003 + e.toNat % 17 + (d >>> 3).toNat % 11 + (a - 200).toNat
''')
add("char_str", '''
def entry (n : Nat) : Nat :=
  let c := Char.ofNat (65 + n % 26)
  (toString c).length + (c.isWhitespace.toNat) + (' '.isWhitespace.toNat * 5) + (c.isAlphanum.toNat) + (String.singleton c).length + c.val.toNat
''')
add("opt_nested", '''
def lookup (n : Nat) : Option (Option Nat) := if n % 3 == 0 then none else if n % 3 == 1 then some none else some (some n)
def entry (n : Nat) : Nat := (List.range (n + 1)).foldl (fun a i => a + match lookup i with | none => 1 | some none => 2 | some (some v) => v) 0
''')
add("prod_arrays", '''
def entry (n : Nat) : Nat :=
  let a : Array (Nat × String) := (Array.range (n + 1)).map fun i => (i, toString i)
  a.foldl (fun acc (k, v) => acc + k + v.length) 0
''')
add("string_sort_unique", '''
def entry (n : Nat) : Nat :=
  let ws := (List.range (n + 1)).map fun i => "w" ++ toString (i * 7 % 13)
  let u := ws.eraseDups
  u.length + (u.toArray.qsort (· < ·)).size + (u.map String.length).sum
''')
add("bool_logic", '''
def entry (n : Nat) : Nat :=
  let a := n % 2 == 0
  let b := n % 3 == 0
  (a && b).toNat + (a || b).toNat * 2 + (xor a b).toNat * 4 + (!a).toNat * 8 + (a == b).toNat * 16
''')
add("rec_nat_big", '''
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
def fibFast (n : Nat) : Nat := (go n).1
where go : Nat → Nat × Nat
  | 0 => (0, 1)
  | k + 1 => let (a, b) := go k; (b, a + b)
def entry (n : Nat) : Nat := fib (n % 15) + (fibFast (n * 10)) % 1000000007
''')
add("array_sum_ranges", '''
def entry (n : Nat) : Nat := Id.run do
  let mut t := 0
  for i in [0:n+1:2] do t := t + i
  for i in [3:n+4] do t := t + i * 2
  return t
''')
add("nested_loops_break", '''
def entry (n : Nat) : Nat := Id.run do
  let mut count := 0
  for i in [0:n+1] do
    for j in [0:n+1] do
      if j > i then break
      if (i + j) % 3 == 0 then continue
      count := count + 1
  return count
''')
add("early_return", '''
def find (xs : Array Nat) (t : Nat) : Option Nat := Id.run do
  for i in [0:xs.size] do
    if xs[i]! == t then return some i
  return none
def entry (n : Nat) : Nat := ((find ((Array.range (n + 5)).map (· * 3)) 9).getD 999)
''')
add("string_toint", '''
def entry (n : Nat) : Nat :=
  let a := (toString n).toNat?.getD 0
  let b := ("-" ++ toString n).toInt?.getD 0
  a + b.natAbs + ("12x".toNat?.getD 7) + ("42".toNat!)
''')
add("list_array_nested", '''
def entry (n : Nat) : Nat :=
  let xs : List (Array (List Nat)) := (List.range (n % 6 + 1)).map fun i => #[List.range i, [i, i]]
  xs.foldl (fun a arr => arr.foldl (fun b l => b + l.length + l.sum) a) 0
''')

add("t_map", '''
def entry (n : Nat) : Nat := ("abc".push 'd' |>.map Char.toUpper).length + n
''')
add("t_get", '''
def entry (n : Nat) : Nat := ("abcdef".get! ⟨n % 4⟩).toNat
''')
add("t_any", '''
def entry (n : Nat) : Nat := (if "abcdef".any (· == 'c') then 1 else 0) + n
''')
add("t_trim", '''
def entry (n : Nat) : Nat := ("  ab  ".trim).length + n
''')
add("t_replace", '''
def entry (n : Nat) : Nat := ("hello".replace "l" "LL").length + n
''')

add("t_all", '''
def entry (n : Nat) : Nat := (if "abc".all Char.isAlpha then 2 else 0) + n
''')

add("t_get0", '''
def entry (n : Nat) : Nat := ("abc".get! 0).toNat + n
''')

add("t_upper", '''
def entry (n : Nat) : Nat := ("abc".toUpper).length + n
''')

add("t_lower", '''
def entry (n : Nat) : Nat := ("ABc".toLower).length + n
''')

add("t_starts", '''
def entry (n : Nat) : Nat := (if "Hello".startsWith "He" then 1 else 0) + n
''')

add("t_ends", '''
def entry (n : Nat) : Nat := (if "Hello".endsWith "lo" then 1 else 0) + n
''')

add("t_contains", '''
def entry (n : Nat) : Nat := (if "Hello".contains 'e' then 4 else 0) + n
''')

add("t_join", '''
def entry (n : Nat) : Nat := (String.join ["a", "b"]).length + n
''')

add("t_rev", '''
def entry (n : Nat) : Nat := ("abc".toList.reverse.length) + n
''')

add("t_pushmap", '''
def entry (n : Nat) : Nat :=
  let s := (List.range (n + 3)).foldl (fun s i => s.push (Char.ofNat (97 + i % 26))) ""
  (s.map Char.toUpper).length
''')

add("t_pushget", '''
def entry (n : Nat) : Nat :=
  let s := (List.range (n + 3)).foldl (fun s i => s.push (Char.ofNat (97 + i % 26))) ""
  (s.get! 0).toNat
''')

add("t_pushall", '''
def entry (n : Nat) : Nat :=
  let s := (List.range (n + 3)).foldl (fun s i => s.push (Char.ofNat (97 + i % 26))) ""
  (if s.all Char.isAlpha then 2 else 0) + s.length
''')

add("t_append3", '''
def entry (n : Nat) : Nat :=
  let s := "  Hello, World " ++ toString n ++ "  "
  s.trim.length
''')

add("t_replace2", '''
def entry (n : Nat) : Nat :=
  let s := "Hello, World " ++ toString n
  (s.replace "o" "00").length
''')

# ---- typed-array hazards: library code that writes placeholders or changes element types in place
add("arr_modify", '''
def entry (n : Nat) : Nat :=
  let a := Array.replicate (n % 7 + 4) (7 : Nat)
  let b := (a.modify 1 (· + 5)).modify 0 (· * 3)
  let c := b.modify 2 (· + 100)
  b[0]! + b[1]! + c[2]! + c.foldl (· + ·) 0
''')
add("arr_map_types", '''
def entry (n : Nat) : Nat :=
  let a := Array.replicate (n % 6 + 3) (3 : Nat)
  let bools := a.map (fun x => decide (x > 2))
  let strs := a.map toString
  let nats := a.map (· + 1)
  (bools.foldl (fun s b => s + (if b then 1 else 0)) 0) + (strs.foldl (fun s t => s + t.length) 0) + nats.foldl (· + ·) 0
''')
add("arr_swapat", '''
def entry (n : Nat) : Nat :=
  let a := Array.replicate (n % 5 + 4) (2 : Nat)
  let a := a.set! 1 9
  let (old, b) := a.swapAt! 1 40
  old + b[1]! + b.foldl (· + ·) 0 + a.foldl (· + ·) 0
''')
add("arr_u8_modify", '''
def entry (n : Nat) : Nat :=
  let a := Array.replicate (n % 5 + 4) (200 : UInt8)
  let b := (a.modify 2 (· + 100)).modify 0 (· * 2)
  let c := b.map (· + 1)
  let d := c.map (fun x => x.toNat * 1000)
  b.foldl (fun s x => s + x.toNat) 0 + d.foldl (· + ·) 0
''')
add("arr_bool_flip", '''
def entry (n : Nat) : Nat := Id.run do
  let m := n % 20 + 5
  let mut a := Array.replicate m false
  for i in [0:m] do
    if i % 3 == 0 then a := a.set! i true
  a := a.modify 1 (fun b => !b)
  let flips := a.map (fun b => !b)
  return (a.foldl (fun s b => s + (if b then 1 else 0)) 0) * 10 + flips.foldl (fun s b => s + (if b then 1 else 0)) 0
''')
add("arr_nested_types", '''
def entry (n : Nat) : Nat :=
  let a := Array.replicate (n % 4 + 3) (5 : Nat)
  let pairs := a.map (fun x => (x, x + 1))
  let opts := a.map (fun x => if x > 4 then some x else none)
  pairs.foldl (fun s (p, q) => s + p * q) 0 + opts.foldl (fun s o => s + o.getD 100) 0
''')
add("variant_poly_const", '''
inductive T where
  | leaf
  | node : T -> Nat -> T -> T

def T.ins : T -> Nat -> T
  | .leaf, k => .node .leaf k .leaf
  | .node l x r, k => if k < x then .node (l.ins k) x r else .node l x (r.ins k)

def T.fold (f : Nat -> σ -> σ) : T -> σ -> σ
  | .leaf, b => b
  | .node l k r, b => T.fold f r (f k (T.fold f l b))

def entry (n : Nat) : Nat :=
  let t := (List.range (n + 3)).foldl (fun t i => t.ins ((i * 7) % 11)) T.leaf
  t.fold (fun k acc => acc * 3 + k) 0
''')
add("array_same_cap", '''
def entry (n : Nat) : Nat :=
  let u8 : Array UInt8 := Id.run do
    let mut r := Array.mkEmpty 4
    for x in [0:n + 1] do r := r.push x.toUInt8
    return r
  let v := u8.map (fun x => x.toNat * 1000)
  let r := Id.run do
    let mut arr : Array Nat := Array.mkEmpty 4
    for i in [0:n + 1] do arr := arr.push (i * i)
    return arr
  r.foldl (fun acc x => acc * 5 + x) 0 + v.foldl (· + ·) 0
''')
