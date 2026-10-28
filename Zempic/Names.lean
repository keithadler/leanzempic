/-
Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.

Haskell identifiers for Lean names. The encoding is a prefix code, so two different Lean names
can never get the same Haskell name (`mangle_injective`).
-/

namespace Zempic

/-- A hex digit of `n mod 16`. -/
def hexD (n : Nat) : Char := Nat.digitChar (n % 16)

/-- Six hex digits of `n`, most significant first: enough for every Unicode scalar value. -/
def hex6 (n : Nat) : List Char :=
  [hexD (n / 1048576), hexD (n / 65536), hexD (n / 4096), hexD (n / 256), hexD (n / 16), hexD n]

/-- Characters that stay as they are: ASCII letters and digits. -/
def isPlain (c : Char) : Bool := c.isAlphanum && c.toNat < 128

/-- Encoding of one character. Letters and digits stay; `.` becomes `_`; `_` becomes `'u`;
anything else becomes `'x` and six hex digits and `'`. A `_` therefore always means a dot and a
`'` always starts an escape, which is what makes the code unambiguous. -/
def mangleChar (c : Char) : List Char :=
  if isPlain c then [c]
  else if c = '.' then ['_']
  else if c = '_' then ['\'', 'u']
  else ['\'', 'x'] ++ hex6 c.toNat ++ ['\'']

/-- Encode a list of characters. -/
def mangleChars (s : List Char) : List Char := s.flatMap mangleChar

/-- A Haskell-identifier-safe rendering of a Lean name. -/
def mangle (s : String) : String := String.ofList (mangleChars s.toList)

/-! ## Proofs -/

theorem char_toNat_inj {a b : Char} (h : a.toNat = b.toNat) : a = b := by
  apply Char.ext
  have : a.val.toNat = b.val.toNat := h
  exact UInt32.toNat_inj.mp this

theorem char_toNat_lt (a : Char) : a.toNat < 16777216 := by
  have h := a.valid
  have h2 : Nat.isValidChar a.val.toNat := h
  unfold Nat.isValidChar at h2
  show a.val.toNat < 16777216
  omega

theorem digitChar_inj : ∀ a b : Fin 16, Nat.digitChar a = Nat.digitChar b → a = b := by decide

theorem hexD_inj {a b : Nat} (h : hexD a = hexD b) : a % 16 = b % 16 := by
  have := digitChar_inj ⟨a % 16, Nat.mod_lt _ (by omega)⟩ ⟨b % 16, Nat.mod_lt _ (by omega)⟩ h
  exact congrArg Fin.val this

theorem hex6_inj {n m : Nat} (hn : n < 16777216) (hm : m < 16777216) (h : hex6 n = hex6 m) :
    n = m := by
  simp only [hex6, List.cons.injEq, and_true] at h
  obtain ⟨h5, h4, h3, h2, h1, h0⟩ := h
  have e5 := hexD_inj h5
  have e4 := hexD_inj h4
  have e3 := hexD_inj h3
  have e2 := hexD_inj h2
  have e1 := hexD_inj h1
  have e0 := hexD_inj h0
  omega

theorem isPlain_dot : isPlain '.' = false := by decide
theorem isPlain_us : isPlain '_' = false := by decide
theorem isPlain_quote : isPlain '\'' = false := by decide

theorem mangleChar_plain {c : Char} (h : isPlain c = true) : mangleChar c = [c] := by
  simp [mangleChar, h]

theorem mangleChar_dot : mangleChar '.' = ['_'] := by
  simp [mangleChar, isPlain_dot]

theorem mangleChar_us : mangleChar '_' = ['\'', 'u'] := by
  simp [mangleChar, isPlain_us]

theorem mangleChar_other {c : Char} (hp : isPlain c = false) (hd : c ≠ '.') (hu : c ≠ '_') :
    mangleChar c = ['\'', 'x'] ++ hex6 c.toNat ++ ['\''] := by
  simp [mangleChar, hp, hd, hu]

/-- Every character is plain, a dot, an underscore, or something else. -/
theorem char_cases (c : Char) :
    isPlain c = true ∨ c = '.' ∨ c = '_' ∨ (isPlain c = false ∧ c ≠ '.' ∧ c ≠ '_') := by
  by_cases h : isPlain c = true
  · exact Or.inl h
  by_cases d : c = '.'
  · exact Or.inr (Or.inl d)
  by_cases u : c = '_'
  · exact Or.inr (Or.inr (Or.inl u))
  exact Or.inr (Or.inr (Or.inr ⟨by simpa using h, d, u⟩))

theorem hex6_length (n : Nat) : (hex6 n).length = 6 := rfl

/-- Two escapes followed by anything are equal only if their characters and rests are. -/
theorem escape_inj {a b : Char} {r s : List Char}
    (h : ('\'' :: 'x' :: (hex6 a.toNat ++ ('\'' :: r))) =
         ('\'' :: 'x' :: (hex6 b.toNat ++ ('\'' :: s)))) : a = b ∧ r = s := by
  simp only [List.cons.injEq, true_and] at h
  obtain ⟨hh, hr⟩ := List.append_inj h (by simp [hex6_length])
  exact ⟨char_toNat_inj (hex6_inj (char_toNat_lt a) (char_toNat_lt b) hh), by simpa using hr⟩

/-- Equal encodings followed by anything decode to the same character and the same rest. -/
theorem mangleChar_append_inj {a b : Char} {r s : List Char}
    (h : mangleChar a ++ r = mangleChar b ++ s) : a = b ∧ r = s := by
  rcases char_cases a with ha | rfl | rfl | ⟨ha, hda, hua⟩ <;>
  rcases char_cases b with hb | rfl | rfl | ⟨hb, hdb, hub⟩ <;>
  simp [mangleChar_plain, mangleChar_dot, mangleChar_us, mangleChar_other, *] at h
  all_goals first
    | exact ⟨h.1, h.2⟩
    | exact ⟨rfl, h⟩
    | (obtain ⟨h1, -⟩ := h
       subst h1
       simp_all [isPlain_us, isPlain_quote])
    | (obtain ⟨hh, hr⟩ := List.append_inj h (by simp [hex6_length])
       exact ⟨char_toNat_inj (hex6_inj (char_toNat_lt a) (char_toNat_lt b) hh), by simpa using hr⟩)

/-- Encoding a list of characters loses nothing. -/
theorem mangleChars_injective : Function.Injective mangleChars := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 h
    cases l2 with
    | nil => rfl
    | cons b t =>
      exfalso
      have h' : ([] : List Char) = mangleChar b ++ mangleChars t := by
        simpa [mangleChars] using h
      rcases char_cases b with hb | rfl | rfl | ⟨hb, hd, hu⟩ <;>
        simp [mangleChar_plain, mangleChar_dot, mangleChar_us, mangleChar_other, *] at h'
  | cons a t ih =>
    intro l2 h
    cases l2 with
    | nil =>
      exfalso
      have h' : mangleChar a ++ mangleChars t = [] := by simpa [mangleChars] using h
      rcases char_cases a with ha | rfl | rfl | ⟨ha, hd, hu⟩ <;>
        simp [mangleChar_plain, mangleChar_dot, mangleChar_us, mangleChar_other, *] at h'
    | cons b u =>
      have h' : mangleChar a ++ mangleChars t = mangleChar b ++ mangleChars u := by
        simpa [mangleChars] using h
      obtain ⟨hab, hrest⟩ := mangleChar_append_inj h'
      subst hab
      rw [ih hrest]

/-- Different Lean names always get different Haskell names. -/
theorem mangle_injective : Function.Injective mangle := by
  intro x y h
  have h1 : (mangle x).toList = (mangle y).toList := by rw [h]
  simp only [mangle, String.toList_ofList] at h1
  exact String.ext (by simpa using mangleChars_injective h1)

end Zempic
