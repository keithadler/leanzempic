/-
Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.

Checks made before anything is generated, so that an unsupported setup fails with a clear message
rather than somewhere inside the compiler's internals.
-/
import Lean

namespace Zempic

/-- The Lean version this backend was written and tested against: 4.29.x. It reads the compiler's
intermediate representation (LCNF), whose shape and function names change between releases. -/
def supportedLean : Nat × Nat := (4, 29)

/-- Is this Lean version one the backend supports (or has the user said to try anyway)? -/
def checkLean (major minor : Nat) (allowOther : Bool) : Except String Unit :=
  if (major, minor) == supportedLean || allowOther then .ok ()
  else .error s!"leanzempic supports Lean {supportedLean.1}.{supportedLean.2}.x, but this is Lean \
    {major}.{minor}. The backend reads Lean's compiler IR, which changes between releases, so \
    other versions may fail or produce wrong code. To try anyway, put \
    `set_option zempic.allowOtherLean true` before `#zempic`."

/-- The output modes `#zempic` accepts. -/
def validModes : List String := ["auto", "word", "exact", "core"]

/-- Reject a mode that is not one of `validModes`, so a typo is not silently treated as `auto`. -/
def checkMode (mode : String) : Except String Unit :=
  if validModes.contains mode then .ok ()
  else .error s!"leanzempic: unknown mode `{mode}`; use one of: {", ".intercalate validModes}"

end Zempic
