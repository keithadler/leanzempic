/-
Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.

Machine-checked facts about the printer. `mangleV1_collides` is a bug the proof attempt found;
`mangle_injective` (in `Zempic.Names`) is the fix.
-/
import Zempic.Emit
import Zempic.Config

namespace Zempic.Proofs

/-- One character of the `mangle` that shipped in v0.1, kept so its flaw stays on record. -/
def mangleV1Char (c : Char) : List Char :=
  if c.isAlphanum && c.toNat < 128 then [c]
  else if c == '_' then ['_', '_']
  else if c == '.' then ['_']
  else ['_', 'x'] ++ Nat.toDigits 16 c.toNat ++ ['_']

/-- The v0.1 name mangling, on character lists. -/
def mangleV1 (s : List Char) : List Char := s.flatMap mangleV1Char

/-- Two different Lean names, `foo._lam` and `foo_.lam`, got the same Haskell name. -/
theorem mangleV1_collides :
    mangleV1 "foo._lam".toList = mangleV1 "foo_.lam".toList ∧
      "foo._lam".toList ≠ "foo_.lam".toList := by
  decide +kernel

/-- So v0.1's `mangle` was not injective. -/
theorem mangleV1_not_injective : ¬ Function.Injective mangleV1 :=
  fun h => mangleV1_collides.2 (h mangleV1_collides.1)

/-- A cast between equal types is the identity, so typed code gets no casts. -/
theorem coerce_self (x t : String) : coerce x t t = x := by
  simp [coerce]

/-- Casting into `Any` is the only cast that adds `zo`. -/
theorem coerce_to_any (x t : String) (h : t ≠ "Any") : coerce x t "Any" = s!"(zo {x})" := by
  simp [coerce, h]

/-- Casting out of `Any` to a real type adds `zu`. -/
theorem coerce_from_any (x t : String) (h : t ≠ "Any") : coerce x "Any" t = s!"(zu {x})" := by
  simp [coerce, h, Ne.symm h]

/-- The supported Lean version is accepted. -/
theorem checkLean_supported : (checkLean 4 29 false).toBool = true := by decide

/-- Another version is refused unless the user opts in. -/
theorem checkLean_other : (checkLean 4 36 false).toBool = false := by decide

/-- ... and accepted when they do. -/
theorem checkLean_override : (checkLean 4 36 true).toBool = true := by decide

/-- A mistyped mode is an error, not silently `auto`. -/
theorem checkMode_typo : (checkMode "exatc").toBool = false := by decide

/-- Every real mode is accepted. -/
theorem checkMode_valid : validModes.all (fun m => (checkMode m).toBool) = true := by decide

end Zempic.Proofs
