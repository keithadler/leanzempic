/-
Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
-/
import Lean
import Zempic.Emit

open Lean Elab Command

namespace Zempic

/-- `#zempic f g` prints Haskell for `f`, `g` and what they reach.
`#zempic f g to "path/Name.hs"` writes it (module name = file stem), and also writes `Name.core`. -/
syntax (name := zempicCmd) "#zempic " ident+ (" to " str)? (&" mode " ident)? : command

@[command_elab zempicCmd] def elabZempic : CommandElab := fun stx => do
  let ids := stx[1].getArgs
  let path? := stx[2].getArgs[1]?.map (·.isStrLit?.get!)
  let mut roots : Array Name := #[]
  for i in ids do roots := roots.push (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo i)
  let modName := match path? with
    | some p => (System.FilePath.mk p).fileStem.getD "Out"
    | none => "Out"
  let mode := (stx[3].getArgs[1]?.map (·.getId.toString)).getD "auto"
  let (files, core) ← liftCoreM <| emitFiles modName roots mode
  match path? with
  | some p =>
    let fp := System.FilePath.mk p
    let dir := fp.parent.getD "."
    IO.FS.createDirAll dir
    for (rel, text) in files do
      let out := dir / rel
      if let some d := out.parent then IO.FS.createDirAll d
      IO.FS.writeFile out text
    IO.FS.writeFile (fp.withExtension "core") core
    logInfo m!"leanzempic: wrote {files.size} Haskell file(s) next to {p}"
  | none => logInfo m!"{"\n".intercalate (files.toList.map (·.2))}\n{core}"

end Zempic
