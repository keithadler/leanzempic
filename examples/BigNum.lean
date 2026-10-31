import Zempic

/-- Checksum of a big number: its residue modulo a 61-bit prime (linear time, so printing stays cheap). -/
def chk (n : Nat) : Nat := n % 2305843009213693951

/-- n! by a plain left fold. -/
def factAux (acc : Nat) : Nat → Nat
  | 0 => acc
  | k+1 => factAux (acc * (k+1)) k

def fact (n : Nat) : Nat := factAux 1 n

/-- Square-and-multiply modular exponentiation, `fuel` bounds the bit count of the exponent. -/
def powModAux (fuel : Nat) (b e m acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | f+1 =>
    if e == 0 then acc
    else
      let acc' := if e % 2 == 1 then acc * b % m else acc
      powModAux f (b * b % m) (e / 2) m acc'

def powMod (b e m : Nat) : Nat := powModAux 100000 b e m 1

/-- Euclid's algorithm written in Lean (not the built-in gcd). -/
def euclid (fuel a b : Nat) : Nat :=
  match fuel with
  | 0 => a
  | f+1 => if b == 0 then a else euclid f b (a % b)

/-- Lucas-Lehmer test for the Mersenne number 2^p - 1 (p an odd prime): 1 for prime, 0 for composite. -/
def llAux (m : Nat) : Nat → Nat → Nat
  | 0, s => s
  | k+1, s => llAux m k ((s * s + m - 2) % m)

def lucasLehmer (p : Nat) : Nat :=
  let m := 2 ^ p - 1
  if llAux m (p - 2) 4 == 0 then 1 else 0

/-- Miller-Rabin to the fixed bases 2,3,5,7,11,13,17,19,23,29,31,37 for `n` (odd, > 40). -/
def mrWitness (n d : Nat) (r : Nat) (a : Nat) : Bool :=
  let x := powMod a d n
  if x == 1 || x == n - 1 then true
  else
    let rec go (fuel : Nat) (x : Nat) : Bool :=
      match fuel with
      | 0 => false
      | f+1 =>
        let y := x * x % n
        if y == n - 1 then true else go f y
    go r x

def oddPart (fuel d r : Nat) : Nat × Nat :=
  match fuel with
  | 0 => (d, r)
  | f+1 => if d % 2 == 0 then oddPart f (d / 2) (r + 1) else (d, r)

def millerRabin (n : Nat) : Nat :=
  let (d, r) := oddPart 100000 (n - 1) 0
  let bases := [2,3,5,7,11,13,17,19,23,29,31,37]
  if bases.all (fun a => mrWitness n d r a) then 1 else 0

/-- Fast-doubling Fibonacci: returns (F k, F (k+1)). -/
def fibPair (fuel k : Nat) : Nat × Nat :=
  match fuel with
  | 0 => (0, 1)
  | f+1 =>
    if k == 0 then (0, 1)
    else
      let (a, b) := fibPair f (k / 2)
      let c := a * (2 * b - a)
      let d := a * a + b * b
      if k % 2 == 0 then (c, d) else (d, c + d)

def fib (k : Nat) : Nat := (fibPair 64 k).1

/-- Iterative Fibonacci by additions (n additions of growing numbers). -/
def fibIter (a b : Nat) : Nat → Nat
  | 0 => a
  | k+1 => fibIter b (a + b) k

/-- Int: extended Euclid on big Ints, returns x of a*x + b*y = gcd. -/
def egcd (fuel : Nat) (r0 r1 s0 s1 : Int) : Int :=
  match fuel with
  | 0 => s0
  | f+1 => if r1 == 0 then s0 else
      let q := r0 / r1
      egcd f r1 (r0 - q * r1) s1 (s0 - q * s1)

/-- Int workload: alternating-sign product and a big extended gcd. -/
def intWork (n : Nat) : Nat :=
  let rec prod (k : Nat) (acc : Int) : Int :=
    match k with
    | 0 => acc
    | j+1 => prod j (acc * (if j % 2 == 0 then -(Int.ofNat (j+1)) else Int.ofNat (j+1)))
  let p := prod n 1
  let a : Int := (2 : Int) ^ 4423 - 1
  let b : Int := - ((3 : Int) ^ 2500 + 12345)
  (p % 2305843009213693951).toNat + (egcd 100000 a b 1 0 % 2305843009213693951).toNat

/-- Newton integer square root of n (start above the root). -/
def isqrtAux (fuel n x : Nat) : Nat :=
  match fuel with
  | 0 => x
  | f+1 =>
    let y := (x + n / x) / 2
    if y >= x then x else isqrtAux f n y

def isqrt (n : Nat) : Nat := isqrtAux 100000 n (1 <<< (Nat.log2 n / 2 + 1))

/-- Bit operations on big numbers: shifts, and, or, xor, testBit by shifting. -/
def bitWork (size : Nat) : Nat :=
  let a := fib size
  let b := (a <<< 17) ^^^ (a >>> 5)
  let c := (a &&& b) ||| (b ^^^ (a <<< 3))
  let rec cnt (k : Nat) (x : Nat) (acc : Nat) : Nat :=
    match k with
    | 0 => acc
    | j+1 => cnt j (x >>> 7) (acc + (x &&& 127))
  chk c + cnt 200 c 0 + Nat.log2 c

/-- Int division and conversion variants on big negative operands. -/
def intOps (size : Nat) : Nat :=
  let a : Int := -(Int.ofNat (fib size)) - 7
  let b : Int := Int.ofNat (fib (size / 2 + 3)) + 1
  let q1 := a / b
  let r1 := a % b
  let q2 := Int.tdiv a b
  let r2 := Int.tmod a b
  let q3 := Int.fdiv a b
  let r3 := Int.fmod a b
  let p : Int := (-3 : Int) ^ (size / 4)
  let s := a >>> 11
  (q1 + r1 + q2 + r2 + q3 + r3 + p + s).natAbs % 1000000007 + (a * b).toNat + (Int.gcd a b) + (a.natAbs % 97)

/-- Workload selector. -/
def runBig (which size : Nat) : Nat :=
  match which with
  | 0 => chk (fact size)
  | 1 => chk (powMod (3 ^ 3000 + 7) (2 ^ size - 12345) (2 ^ 4423 - 1))
  | 2 => Nat.gcd (fib size) (fib (size + size / 2)) % 1000000007 + chk (Nat.gcd (3 ^ size - 1) (6 ^ size - 1))
  | 3 => euclid 1000000 (fib size) (fib size / 3 + 12345) % 1000000007
  | 4 => lucasLehmer size
  | 5 => millerRabin (2 ^ size - 1)
  | 6 => chk (fib size)
  | 7 => chk (fibIter 0 1 size)
  | 8 => intWork size
  | 9 => (toString (fib size)).length
  | 10 => isqrt (fib size * fib size + 12345) % 1000000007
  | 11 => bitWork size
  | _ => intOps size

def main (args : List String) : IO Unit :=
  IO.println (runBig ((args.headD "0").toNat?.getD 0) ((args.getD 1 "100").toNat?.getD 100))

#zempic runBig to "build/BigNum.hs"
