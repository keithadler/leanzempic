/-!
# Bytes, words and the state

FIPS-197 §3. A byte is an element of GF(2⁸) written in the polynomial basis, a word is four bytes, and
the state is a 4×4 array of bytes held as four columns. Everything here is a plain structure rather than
an array, so that the kernel can evaluate a whole encryption by `decide` without unfolding any
well-founded recursion, and so that a proof about a column can take it apart with `cases`.
-/

namespace AES

/-- A byte. FIPS-197 §3.2 reads its bits as the coefficients of a polynomial over GF(2). -/
abbrev Byte := UInt8

/-- A word: four bytes. As a column of the state, `b0` is row 0. -/
structure Word where
  /-- Byte 0; row 0 when the word is a column of the state. -/
  b0 : Byte
  /-- Byte 1. -/
  b1 : Byte
  /-- Byte 2. -/
  b2 : Byte
  /-- Byte 3. -/
  b3 : Byte
  deriving DecidableEq, Repr, Inhabited

/-- The state, FIPS-197 §3.4: `c.bR` is `s[R, c]`. Input byte `in[r + 4c]` lands at `s[r, c]`. -/
structure State where
  /-- Column 0: `s[0,0] … s[3,0]`, input bytes 0–3. -/
  c0 : Word
  /-- Column 1: input bytes 4–7. -/
  c1 : Word
  /-- Column 2: input bytes 8–11. -/
  c2 : Word
  /-- Column 3: input bytes 12–15. -/
  c3 : Word
  deriving DecidableEq, Repr, Inhabited

namespace Word

instance : XorOp Word := ⟨fun a b => ⟨a.b0 ^^^ b.b0, a.b1 ^^^ b.b1, a.b2 ^^^ b.b2, a.b3 ^^^ b.b3⟩⟩
instance : Zero Word := ⟨⟨0, 0, 0, 0⟩⟩

@[simp] theorem xor_def (a b : Word) :
    a ^^^ b = ⟨a.b0 ^^^ b.b0, a.b1 ^^^ b.b1, a.b2 ^^^ b.b2, a.b3 ^^^ b.b3⟩ := rfl
@[simp] theorem zero_def : (0 : Word) = ⟨0, 0, 0, 0⟩ := rfl

/-- Apply a byte function to each byte. -/
def map (f : Byte → Byte) (w : Word) : Word := ⟨f w.b0, f w.b1, f w.b2, f w.b3⟩

@[simp] theorem map_mk (f : Byte → Byte) (a b c d : Byte) : map f ⟨a, b, c, d⟩ = ⟨f a, f b, f c, f d⟩ := rfl

end Word

namespace State

instance : XorOp State := ⟨fun a b => ⟨a.c0 ^^^ b.c0, a.c1 ^^^ b.c1, a.c2 ^^^ b.c2, a.c3 ^^^ b.c3⟩⟩
instance : Zero State := ⟨⟨0, 0, 0, 0⟩⟩

@[simp] theorem xor_def (a b : State) : a ^^^ b = ⟨a.c0 ^^^ b.c0, a.c1 ^^^ b.c1, a.c2 ^^^ b.c2, a.c3 ^^^ b.c3⟩ :=
  rfl
@[simp] theorem zero_def : (0 : State) = ⟨0, 0, 0, 0⟩ := rfl

/-- Apply a column function to each column. -/
def mapCols (f : Word → Word) (s : State) : State := ⟨f s.c0, f s.c1, f s.c2, f s.c3⟩

@[simp] theorem mapCols_mk (f : Word → Word) (a b c d : Word) :
    mapCols f ⟨a, b, c, d⟩ = ⟨f a, f b, f c, f d⟩ := rfl

/-- Byte `i` of a 128-bit number written most significant byte first, the way FIPS-197 prints blocks. -/
def byteOf (n : Nat) (i : Nat) : Byte := ((n >>> (8 * (15 - i))) % 256).toUInt8

/-- A block written as one hexadecimal number, `0x00112233445566778899aabbccddeeff`, laid out as
FIPS-197 §3.4 lays out `in₀ … in₁₅`. -/
def ofNat (n : Nat) : State :=
  let b := byteOf n
  ⟨⟨b 0, b 1, b 2, b 3⟩, ⟨b 4, b 5, b 6, b 7⟩, ⟨b 8, b 9, b 10, b 11⟩, ⟨b 12, b 13, b 14, b 15⟩⟩

/-- The sixteen bytes in input order. -/
def toList (s : State) : List Byte :=
  [s.c0.b0, s.c0.b1, s.c0.b2, s.c0.b3, s.c1.b0, s.c1.b1, s.c1.b2, s.c1.b3,
   s.c2.b0, s.c2.b1, s.c2.b2, s.c2.b3, s.c3.b0, s.c3.b1, s.c3.b2, s.c3.b3]

/-- The block as one number, most significant byte first; the inverse of `ofNat` below 2¹²⁸. -/
def toNat (s : State) : Nat := s.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

end State

/-! ## Deciding a statement about every byte

`decide` has no instance for `∀ x : UInt8, p x`, and the kernel is fastest on a plain structural loop, so
a statement about all 256 bytes is checked by `allBytes` and turned back into a `∀` by `allBytes_spec`. -/

/-- `p 0 && p 1 && … && p (n-1)`, by structural recursion so the kernel can run it. -/
def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p n && allBelow n p

theorem allBelow_spec {n : Nat} {p : Nat → Bool} (h : allBelow n p = true) : ∀ m < n, p m = true := by
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
    · exact ih h.2 m hm
    · exact h.1

/-- Every byte satisfies `p`. -/
def allBytes (p : Byte → Bool) : Bool := allBelow 256 fun n => p n.toUInt8

theorem allBytes_spec {p : Byte → Bool} (h : allBytes p = true) (x : Byte) : p x = true := by
  have := allBelow_spec h x.toNat x.toNat_lt
  simpa [Nat.toUInt8, UInt8.ofNat_toNat] using this

end AES
