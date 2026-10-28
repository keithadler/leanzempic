import AES.Basic

/-!
# Arithmetic in GF(2⁸)

FIPS-197 §4. Addition is XOR. Multiplication is defined the way §4.2 defines it: `xtime` multiplies by
`x` and reduces by `m(x) = x⁸ + x⁴ + x³ + x + 1`, and a general product is the sum of `xtimeⁱ b` over
the bits `i` of `a`.

The field laws are proved rather than enumerated. Everything follows from one fact, that `xtime` is
additive, which is a bit-level argument about a shift and a conditional XOR. From it, multiplication by
any `a` is additive and commutes with `xtime`; that makes any two multiplications commute, and
commutativity and associativity fall out by putting `1` in the right place. The only facts checked by
running over all 256 bytes are the one-variable ones: `a • 1 = a` and `b • b⁻¹ = 1`.
-/

namespace AES

set_option maxHeartbeats 0

/-- `xTimes`, FIPS-197 §4.2: multiply by the polynomial `x`, reducing by `m(x)` when bit 7 falls off. -/
def xtime (b : Byte) : Byte := if b &&& 0x80 = 0 then b <<< 1 else (b <<< 1) ^^^ 0x1b

/-- The loop behind `mul`: `n` more bits of `a` to read, `b` the current `xtimeⁱ` of the multiplicand,
`acc` the sum so far. Structural on `n`, so the kernel runs it. -/
def mulLoop : Nat → Byte → Byte → Byte → Byte
  | 0, _, _, acc => acc
  | n + 1, a, b, acc => mulLoop n (a >>> 1) (xtime b) (if a &&& 1 = 0 then acc else acc ^^^ b)

/-- Multiplication in GF(2⁸), written `a • b` in FIPS-197 §4.2. -/
def mul (a b : Byte) : Byte := mulLoop 8 a b 0

/-- The multiplicative inverse, FIPS-197 §4.4: `b⁻¹ = b²⁵⁴`, and `0⁻¹ = 0`. Computed by an addition
chain, `254 = 2 + 4 + 8 + 16 + 32 + 64 + 128`. -/
def inv (b : Byte) : Byte :=
  let b2 := mul b b
  let b4 := mul b2 b2
  let b8 := mul b4 b4
  let b16 := mul b8 b8
  let b32 := mul b16 b16
  let b64 := mul b32 b32
  let b128 := mul b64 b64
  mul b2 (mul b4 (mul b8 (mul b16 (mul b32 (mul b64 b128)))))

/-! ## XOR on bytes -/

theorem and_xor_distrib (x y z : Byte) : (x ^^^ y) &&& z = (x &&& z) ^^^ (y &&& z) := by
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_xor, BitVec.getElem_and, BitVec.getElem_xor]
  cases x.toBitVec[i] <;> cases y.toBitVec[i] <;> simp

/-- Bit 7 of a byte is either clear or set. -/
theorem and_0x80 (x : Byte) : x &&& 0x80 = 0 ∨ x &&& 0x80 = 0x80 := by
  have : allBytes (fun x => x &&& 0x80 == 0 || x &&& 0x80 == 0x80) = true := by decide +kernel
  simpa using allBytes_spec this x

/-! ## `xtime` is additive -/

theorem xor_xor_cancel (a b k : Byte) : (a ^^^ k) ^^^ (b ^^^ k) = a ^^^ b := by
  rw [show (a ^^^ k) ^^^ (b ^^^ k) = (a ^^^ b) ^^^ (k ^^^ k) by ac_rfl, UInt8.xor_self, UInt8.xor_zero]

theorem xtime_xor (x y : Byte) : xtime (x ^^^ y) = xtime x ^^^ xtime y := by
  unfold xtime
  rw [and_xor_distrib, UInt8.shiftLeft_xor]
  have h80 : (0x80 : Byte) ≠ 0 := by decide
  rcases and_0x80 x with hx | hx <;> rcases and_0x80 y with hy | hy <;>
    simp only [hx, hy, UInt8.xor_self, UInt8.xor_zero, UInt8.zero_xor, h80, ↓reduceIte] <;>
    first | rfl | rw [xor_xor_cancel] | ac_rfl

theorem xtime_zero : xtime 0 = 0 := by decide

/-! ## Multiplication by a fixed `a` is additive and commutes with `xtime` -/

theorem mulLoop_xor (n : Nat) (a b b' acc acc' : Byte) :
    mulLoop n a (b ^^^ b') (acc ^^^ acc') = mulLoop n a b acc ^^^ mulLoop n a b' acc' := by
  induction n generalizing a b b' acc acc' with
  | zero => rfl
  | succ n ih =>
    simp only [mulLoop, xtime_xor]
    split
    · exact ih ..
    · rw [show acc ^^^ acc' ^^^ (b ^^^ b') = (acc ^^^ b) ^^^ (acc' ^^^ b') by ac_rfl]
      exact ih ..

theorem mul_xor (a b c : Byte) : mul a (b ^^^ c) = mul a b ^^^ mul a c := by
  unfold mul
  rw [← mulLoop_xor, UInt8.xor_self]

theorem mul_zero (a : Byte) : mul a 0 = 0 := by
  -- `m = m ^^^ m` forces `m = 0`
  have h := mul_xor a 0 0
  rw [UInt8.xor_self, UInt8.xor_self] at h
  exact h

theorem xtime_mulLoop (n : Nat) (a b acc : Byte) :
    xtime (mulLoop n a b acc) = mulLoop n a (xtime b) (xtime acc) := by
  induction n generalizing a b acc with
  | zero => rfl
  | succ n ih =>
    simp only [mulLoop, ih]
    split <;> simp [xtime_xor]

theorem xtime_mul (a b : Byte) : xtime (mul a b) = mul a (xtime b) := by
  show xtime (mulLoop 8 a b 0) = mulLoop 8 a (xtime b) 0
  rw [xtime_mulLoop, xtime_zero]

/-- Any multiplication commutes with any other: `a • (c • x) = c • (a • x)`. Multiplication by `c` is
built from `xtime` and XOR, and multiplication by `a` respects both. -/
theorem mul_mulLoop (n : Nat) (a c b acc : Byte) :
    mul a (mulLoop n c b acc) = mulLoop n c (mul a b) (mul a acc) := by
  induction n generalizing c b acc with
  | zero => rfl
  | succ n ih =>
    rw [mulLoop, mulLoop, ih, xtime_mul]
    congr 1
    split
    · rfl
    · exact mul_xor ..

theorem mul_left_comm (a c x : Byte) : mul a (mul c x) = mul c (mul a x) := by
  show mul a (mulLoop 8 c x 0) = _
  rw [mul_mulLoop, mul_zero]; rfl

/-! ## The field laws -/

theorem mul_one (a : Byte) : mul a 1 = a := by
  have : allBytes (fun a => mul a 1 == a) = true := by decide +kernel
  simpa using allBytes_spec this a

theorem mul_comm (a b : Byte) : mul a b = mul b a := by
  conv => lhs; rw [← mul_one b]
  rw [mul_left_comm, mul_one]

theorem one_mul (a : Byte) : mul 1 a = a := by rw [mul_comm, mul_one]

theorem zero_mul (a : Byte) : mul 0 a = 0 := by rw [mul_comm, mul_zero]

theorem mul_assoc (a b c : Byte) : mul (mul a b) c = mul a (mul b c) := by
  rw [mul_comm, mul_left_comm, mul_comm c]

theorem xor_mul (a b c : Byte) : mul (a ^^^ b) c = mul a c ^^^ mul b c := by
  rw [mul_comm, mul_xor, mul_comm c, mul_comm c]

theorem mul_inv {b : Byte} (h : b ≠ 0) : mul b (inv b) = 1 := by
  have : allBytes (fun b => b == 0 || mul b (inv b) == 1) = true := by decide +kernel
  simpa [h] using allBytes_spec this b

theorem inv_mul {b : Byte} (h : b ≠ 0) : mul (inv b) b = 1 := by rw [mul_comm, mul_inv h]

/-- No zero divisors. -/
theorem mul_eq_zero {a b : Byte} : mul a b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact .inl ha
    · right
      rw [← one_mul b, ← inv_mul ha, mul_assoc, h, mul_zero]
  · rintro (rfl | rfl)
    · exact zero_mul b
    · exact mul_zero a

theorem mul_ne_zero {a b : Byte} (ha : a ≠ 0) (hb : b ≠ 0) : mul a b ≠ 0 := by
  rw [Ne, mul_eq_zero]; exact fun h => h.elim ha hb

theorem inv_ne_zero {b : Byte} (h : b ≠ 0) : inv b ≠ 0 := by
  intro h'
  have := mul_inv h
  rw [h', mul_zero] at this
  exact absurd this (by decide)

/-- Division: `b • (b⁻¹ • c) = c`. -/
theorem mul_inv_mul {b : Byte} (h : b ≠ 0) (c : Byte) : mul b (mul (inv b) c) = c := by
  rw [← mul_assoc, mul_inv h, one_mul]

end AES
