/-
Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
-/
import Lean
import Zempic.Emit

open Lean Elab Command

namespace Zempic

/-- `#zempic f g` prints Haskell for `f`, `g` and what they reach.
`#zempic f g to "path/Name.hs"` writes it (module name = file stem), and also writes `Name.core`. -/
syntax (name := zempicCmd) "#zempic " ident+ (" to " str)? : command

@[command_elab zempicCmd] def elabZempic : CommandElab := fun stx => do
  let ids := stx[1].getArgs
  let path? := stx[2].getArgs[1]?.map (·.isStrLit?.get!)
  let mut roots : Array Name := #[]
  for i in ids do roots := roots.push (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo i)
  let modName := match path? with
    | some p => (System.FilePath.mk p).fileStem.getD "Out"
    | none => "Out"
  let out ← liftCoreM <| emitModule modName roots
  match path? with
  | some p =>
    let fp := System.FilePath.mk p
    if let some dir := fp.parent then IO.FS.createDirAll dir
    IO.FS.writeFile fp out.haskell
    IO.FS.writeFile (fp.withExtension "core") out.core
    logInfo m!"leanzempic: wrote {p}"
  | none => logInfo m!"{out.haskell}\n{out.core}"

end Zempic
