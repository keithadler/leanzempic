import AES.SBox

/-!
# AES-256, as FIPS-197 specifies it

The four transformations of §5.1, their inverses from §5.3, `KeyExpansion` from §5.2 and the two
algorithms `Cipher` (Algorithm 1) and `InvCipher` (Algorithm 3), specialized to AES-256: `Nk = 8` key
words and `Nr = 14` rounds. Names follow the standard.
-/

namespace AES

/-! ## §5.1 The transformations -/

/-- `SubBytes`, §5.1.1: the S-box on every byte. -/
def subBytes (s : State) : State := s.mapCols (Word.map sbox)

/-- `ShiftRows`, §5.1.2: `s'[r, c] = s[r, (c + r) mod 4]`. Row 0 stays, row `r` rotates left by `r`. -/
def shiftRows (s : State) : State :=
  ⟨⟨s.c0.b0, s.c1.b1, s.c2.b2, s.c3.b3⟩,
   ⟨s.c1.b0, s.c2.b1, s.c3.b2, s.c0.b3⟩,
   ⟨s.c2.b0, s.c3.b1, s.c0.b2, s.c1.b3⟩,
   ⟨s.c3.b0, s.c0.b1, s.c1.b2, s.c2.b3⟩⟩

/-- One column of `MixColumns`, eq. (5.6): multiplication by the fixed matrix with rows
`[02 03 01 01]`, `[01 02 03 01]`, `[01 01 02 03]`, `[03 01 01 02]`. -/
def mixColumn (w : Word) : Word :=
  ⟨mul 0x02 w.b0 ^^^ mul 0x03 w.b1 ^^^ w.b2 ^^^ w.b3,
   w.b0 ^^^ mul 0x02 w.b1 ^^^ mul 0x03 w.b2 ^^^ w.b3,
   w.b0 ^^^ w.b1 ^^^ mul 0x02 w.b2 ^^^ mul 0x03 w.b3,
   mul 0x03 w.b0 ^^^ w.b1 ^^^ w.b2 ^^^ mul 0x02 w.b3⟩

/-- `MixColumns`, §5.1.3. -/
def mixColumns (s : State) : State := s.mapCols mixColumn

/-- `AddRoundKey`, §5.1.4: XOR with the round key. -/
def addRoundKey (s k : State) : State := s ^^^ k

/-! ## §5.3 The inverse transformations -/

/-- `InvShiftRows`, §5.3.1: `s'[r, c] = s[r, (c - r) mod 4]`. -/
def invShiftRows (s : State) : State :=
  ⟨⟨s.c0.b0, s.c3.b1, s.c2.b2, s.c1.b3⟩,
   ⟨s.c1.b0, s.c0.b1, s.c3.b2, s.c2.b3⟩,
   ⟨s.c2.b0, s.c1.b1, s.c0.b2, s.c3.b3⟩,
   ⟨s.c3.b0, s.c2.b1, s.c1.b2, s.c0.b3⟩⟩

/-- `InvSubBytes`, §5.3.2. -/
def invSubBytes (s : State) : State := s.mapCols (Word.map invSbox)

/-- One column of `InvMixColumns`, eq. (5.17): rows `[0e 0b 0d 09]`, `[09 0e 0b 0d]`, `[0d 09 0e 0b]`,
`[0b 0d 09 0e]`. -/
def invMixColumn (w : Word) : Word :=
  ⟨mul 0x0e w.b0 ^^^ mul 0x0b w.b1 ^^^ mul 0x0d w.b2 ^^^ mul 0x09 w.b3,
   mul 0x09 w.b0 ^^^ mul 0x0e w.b1 ^^^ mul 0x0b w.b2 ^^^ mul 0x0d w.b3,
   mul 0x0d w.b0 ^^^ mul 0x09 w.b1 ^^^ mul 0x0e w.b2 ^^^ mul 0x0b w.b3,
   mul 0x0b w.b0 ^^^ mul 0x0d w.b1 ^^^ mul 0x09 w.b2 ^^^ mul 0x0e w.b3⟩

/-- `InvMixColumns`, §5.3.3. -/
def invMixColumns (s : State) : State := s.mapCols invMixColumn

/-! ## §5.2 KeyExpansion -/

/-- A 256-bit key: eight words, `key[4i .. 4i+3]` in word `i`. -/
structure Key where
  /-- Key word 0: key bytes 0–3. -/
  w0 : Word
  /-- Key word 1: key bytes 4–7. -/
  w1 : Word
  /-- Key word 2: key bytes 8–11. -/
  w2 : Word
  /-- Key word 3: key bytes 12–15. -/
  w3 : Word
  /-- Key word 4: key bytes 16–19. -/
  w4 : Word
  /-- Key word 5: key bytes 20–23. -/
  w5 : Word
  /-- Key word 6: key bytes 24–27. -/
  w6 : Word
  /-- Key word 7: key bytes 28–31. -/
  w7 : Word
  deriving DecidableEq, Repr

/-- A key written as one 256-bit hexadecimal number, most significant byte first. -/
def Key.ofNat (n : Nat) : Key :=
  let b (i : Nat) : Byte := ((n >>> (8 * (31 - i))) % 256).toUInt8
  let w (i : Nat) : Word := ⟨b (4 * i), b (4 * i + 1), b (4 * i + 2), b (4 * i + 3)⟩
  ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩

/-- A word written as one 32-bit number, as FIPS-197 Appendix A prints them. -/
def Word.ofNat (n : Nat) : Word :=
  let b (i : Nat) : Byte := ((n >>> (8 * (3 - i))) % 256).toUInt8
  ⟨b 0, b 1, b 2, b 3⟩

/-- `RotWord`, eq. (5.10): `[a0, a1, a2, a3] ↦ [a1, a2, a3, a0]`. -/
def rotWord (w : Word) : Word := ⟨w.b1, w.b2, w.b3, w.b0⟩

/-- `SubWord`, eq. (5.11). -/
def subWord (w : Word) : Word := w.map sbox

/-- `xʲ⁻¹` in GF(2⁸): the first byte of `Rcon[j]`, Table 5. -/
def rconByte : Nat → Byte
  | 0 => 0x8d   -- never used; `x⁻¹`, for completeness of the function
  | 1 => 0x01
  | j + 2 => xtime (rconByte (j + 1))

/-- `Rcon[j] = [xʲ⁻¹, 0, 0, 0]`, eq. (5.12). -/
def rcon (j : Nat) : Word := ⟨rconByte j, 0, 0, 0⟩

/-- The last eight words `w[i-8] … w[i-1]`, oldest first. -/
structure Window where
  /-- `w[i-8]`. -/
  w0 : Word
  /-- `w[i-7]`. -/
  w1 : Word
  /-- `w[i-6]`. -/
  w2 : Word
  /-- `w[i-5]`. -/
  w3 : Word
  /-- `w[i-4]`. -/
  w4 : Word
  /-- `w[i-3]`. -/
  w5 : Word
  /-- `w[i-2]`. -/
  w6 : Word
  /-- `w[i-1]`. -/
  w7 : Word

/-- The body of the loop in Algorithm 2 for `Nk = 8`: `w[i]` from `w[i-8]` and `w[i-1]`. -/
def nextWord (i : Nat) (win : Window) : Word :=
  let temp := win.w7
  let temp :=
    if i % 8 = 0 then subWord (rotWord temp) ^^^ rcon (i / 8)
    else if i % 8 = 4 then subWord temp
    else temp
  win.w0 ^^^ temp

/-- `w[i], w[i+1], …`, `n` of them, given the eight words before `w[i]`. -/
def expandFrom : Nat → Nat → Window → List Word
  | 0, _, _ => []
  | n + 1, i, win =>
    let w := nextWord i win
    w :: expandFrom n (i + 1) ⟨win.w1, win.w2, win.w3, win.w4, win.w5, win.w6, win.w7, w⟩

/-- `KeyExpansion`, Algorithm 2, for AES-256: the `4 * (Nr + 1) = 60` words `w[0] … w[59]`. -/
def keyExpansion (k : Key) : List Word :=
  [k.w0, k.w1, k.w2, k.w3, k.w4, k.w5, k.w6, k.w7] ++
    expandFrom 52 8 ⟨k.w0, k.w1, k.w2, k.w3, k.w4, k.w5, k.w6, k.w7⟩

/-- Round key `r`: the words `w[4r] … w[4r+3]` as the columns of a state. -/
def roundKey (w : List Word) (r : Nat) : State :=
  ⟨w.getD (4 * r) 0, w.getD (4 * r + 1) 0, w.getD (4 * r + 2) 0, w.getD (4 * r + 3) 0⟩

/-! ## The algorithms -/

/-- The number of rounds for AES-256, Table 3. -/
def Nr : Nat := 14

/-- Rounds `r, r+1, …` of Algorithm 1 (lines 4–9), `n` of them. -/
def cipherRounds (rk : Nat → State) : Nat → Nat → State → State
  | 0, _, s => s
  | n + 1, r, s => cipherRounds rk n (r + 1) (addRoundKey (mixColumns (shiftRows (subBytes s))) (rk r))

/-- `Cipher`, Algorithm 1, over any round keys `rk 0 … rk Nr`. -/
def cipher (rk : Nat → State) (input : State) : State :=
  let s := addRoundKey input (rk 0)
  let s := cipherRounds rk (Nr - 1) 1 s
  addRoundKey (shiftRows (subBytes s)) (rk Nr)

/-- Rounds `r, r-1, …` of Algorithm 3 (lines 4–9), `n` of them. -/
def invCipherRounds (rk : Nat → State) : Nat → Nat → State → State
  | 0, _, s => s
  | n + 1, r, s =>
    invCipherRounds rk n (r - 1) (invMixColumns (addRoundKey (invSubBytes (invShiftRows s)) (rk r)))

/-- `InvCipher`, Algorithm 3, over any round keys `rk 0 … rk Nr`. -/
def invCipher (rk : Nat → State) (input : State) : State :=
  let s := addRoundKey input (rk Nr)
  let s := invCipherRounds rk (Nr - 1) (Nr - 1) s
  addRoundKey (invSubBytes (invShiftRows s)) (rk 0)

/-- AES-256 encryption of one block: `Cipher(in, 14, KeyExpansion(key))`. -/
def encrypt (key : Key) (block : State) : State := cipher (roundKey (keyExpansion key)) block

/-- AES-256 decryption of one block: `InvCipher(in, 14, KeyExpansion(key))`. -/
def decrypt (key : Key) (block : State) : State := invCipher (roundKey (keyExpansion key)) block

end AES
