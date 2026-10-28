import Zempic
import AES.Spec

/-! AES-256 from the machine-checked FIPS-197 development (keithadler/lean-aes), run as a benchmark.
The `AES/` files are copied unchanged; the proofs live in that repository. -/

open AES

/-- Encrypt the block `n` times in a row under one key, each output feeding the next. -/
def chain (key : Key) : Nat → State → State
  | 0, s => s
  | n + 1, s => chain key n (encrypt key s)

/-- A fingerprint of a block: its sixteen bytes folded into one number. -/
def fingerprint (s : State) : Nat :=
  let w (x : Word) : Nat := x.b0.toNat + 256 * (x.b1.toNat + 256 * (x.b2.toNat + 256 * x.b3.toNat))
  w s.c0 + 4294967296 * (w s.c1 + 4294967296 * (w s.c2 + 4294967296 * w s.c3))

/-- Byte `i` of a test pattern: small numbers only, so the whole run stays on the `Word` fast path. -/
def pat (seed i : Nat) : Byte := ((seed * 31 + i * 7 + i * i) % 256).toUInt8

/-- A key from a seed: 32 pattern bytes. -/
def keyOf (seed : Nat) : Key :=
  let w (j : Nat) : Word := ⟨pat seed (4 * j), pat seed (4 * j + 1), pat seed (4 * j + 2), pat seed (4 * j + 3)⟩
  ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩

/-- A block from a seed: 16 pattern bytes, input order. -/
def blockOf (seed : Nat) : State :=
  let w (j : Nat) : Word := ⟨pat seed (100 + 4 * j), pat seed (101 + 4 * j), pat seed (102 + 4 * j), pat seed (103 + 4 * j)⟩
  ⟨w 0, w 1, w 2, w 3⟩

/-- The block's 16 bytes as four numbers of 32 bits each, so each stays under 2^64. -/
def lane (s : State) (j : Nat) : Nat :=
  let w := match j with | 0 => s.c0 | 1 => s.c1 | 2 => s.c2 | _ => s.c3
  w.b0.toNat + 256 * (w.b1.toNat + 256 * (w.b2.toNat + 256 * w.b3.toNat))

/-- `n` chained encryptions from the seeded key and block; the four 32-bit lanes of the result,
combined as `((l0 * 2^32 + l1) % 2^61) + l2 + l3`, which stays a `Word`. -/
def aesBench (n seed : Nat) : Nat :=
  let s := chain (keyOf seed) n (blockOf seed)
  (lane s 0 * 4294967296 + lane s 1) % 2305843009213693951 + lane s 2 + lane s 3

def main (args : List String) : IO Unit :=
  IO.println (aesBench (args.headD "1000").toNat! (args.getD 1 "1").toNat!)
