/-
Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.

An LCNF pass that runs just before Lean's `specialize` pass. With `set_option zempic.fuse true`
it rewrites ordinary list code (`List.map`, `filter`, `foldl`, `range`) into calls to the
`Zempic.Fuse` combinators, so the Haskell backend can hand GHC a fusible pipeline without the
user changing their source. Off by default: the rewritten code runs a little slower natively
(closure calls instead of specialized loops), so enable it only where the target is Haskell.
-/
import Lean
import Zempic.Fuse

open Lean Compiler LCNF

register_option zempic.fuse : Bool := {
  defValue := false
  descr := "(leanzempic) rewrite List.map/filter/foldl/range into fusible Zempic.Fuse calls"
}

namespace Zempic.AutoFuse

/-- Is `a` bound to `List.nil`? (the empty accumulator of `mapTR.loop` / `filterTR.loop`) -/
def isNil (a : Arg .pure) : CompilerM Bool := do
  let .fvar id := a | return false
  let some d ← findLetDecl? (pu := .pure) id | return false
  match d.value with
  | .const ``List.nil .. => return true
  | _ => return false

/-- Rewrite one `let` value if it is a recognized list call. -/
def rewrite (v : LetValue .pure) : CompilerM (Option (LetValue .pure)) := do
  let .const n us args := v | return none
  if n == ``List.mapTR.loop && args.size == 5 then
    if ← isNil args[4]! then return some (.const ``Zempic.Fuse.map us (args.extract 0 4))
  else if n == ``List.filterTR.loop && args.size == 4 then
    if ← isNil args[3]! then return some (.const ``Zempic.Fuse.filter us (args.extract 0 3))
  else if n == ``List.map && args.size == 4 then
    return some (.const ``Zempic.Fuse.map us args)
  else if n == ``List.filter && args.size == 3 then
    return some (.const ``Zempic.Fuse.filter us args)
  else if n == ``List.foldl && args.size == 5 then
    return some (.const ``Zempic.Fuse.foldl us args)
  else if n == ``List.range && args.size == 1 then
    return some (.const ``Zempic.Fuse.range us args)
  return none

mutual
partial def goFun (d : FunDecl .pure) : CompilerM (FunDecl .pure) := do
  d.updateValue (← go d.value)

partial def go (c : Code .pure) : CompilerM (Code .pure) := do
  match c with
  | .let d k =>
    let d ← match ← rewrite d.value with
      | some v => d.updateValue v
      | none => pure d
    return c.updateLet! d (← go k)
  | .fun d k => return c.updateFun! (← goFun d) (← go k)
  | .jp d k => return c.updateFun! (← goFun d) (← go k)
  | .cases cs =>
    let alts ← cs.alts.mapM fun a => a.mapCodeM go
    return c.updateAlts! alts
  | _ => return c
end

def pass : Pass where
  phase := .base
  name := `zempicFuse
  run decls := do
    unless zempic.fuse.get (← getOptions) do return decls
    decls.mapM fun d => do
      match d.value with
      | .code c => return { d with value := .code (← go c) }
      | _ => return d

@[cpass] def installer : PassInstaller :=
  PassInstaller.installBefore .base `specialize (fun _ => pass)

end Zempic.AutoFuse
