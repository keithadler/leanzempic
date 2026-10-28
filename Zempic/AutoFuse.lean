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

/-- Turn on the list-fusion rewrite for the declarations compiled under this option. -/
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

/-- Is `a` bound to a call of constant `c` (such as the `Array.mkEmpty` that starts `takeTR`)? -/
def isCallTo (c : Name) (a : Arg .pure) : CompilerM Bool := do
  let .fvar id := a | return false
  let some d ← findLetDecl? (pu := .pure) id | return false
  match d.value with
  | .const n .. => return n == c
  | _ => return false

/-- Are the two arguments the same variable? -/
def sameVar (a b : Arg .pure) : Bool :=
  match a, b with
  | .fvar x, .fvar y => x == y
  | _, _ => false

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
  else if (n == ``List.lengthTR || n == ``List.length) && args.size == 2 then
    return some (.const ``Zempic.Fuse.length us args)
  else if (n == ``List.appendTR || n == ``List.append) && args.size == 3 then
    return some (.const ``Zempic.Fuse.append us args)
  else if (n == ``List.foldrTR || n == ``List.foldr) && args.size == 5 then
    return some (.const ``Zempic.Fuse.foldr us args)
  else if n == ``List.any && args.size == 3 then
    return some (.const ``Zempic.Fuse.any us #[args[0]!, args[2]!, args[1]!])
  else if n == ``List.all && args.size == 3 then
    return some (.const ``Zempic.Fuse.all us #[args[0]!, args[2]!, args[1]!])
  else if (n == ``List.takeTR || n == ``List.take) && args.size == 3 then
    return some (.const ``Zempic.Fuse.take us args)
  else if privateToUserName? n == some `List.takeTR.go && args.size == 5 then
    -- takeTR.go l xs n acc, started with an empty array
    if sameVar args[1]! args[2]! && (← isCallTo ``Array.mkEmpty args[4]!) then
      return some (.const ``Zempic.Fuse.take us #[args[0]!, args[3]!, args[2]!])
  else if (n == ``List.zip || n == `List.zipWith._at_.List.zip.spec_0) && args.size == 4 then
    return some (.const ``Zempic.Fuse.zip us args)
  else if n == ``List.sum && args.size == 4 then
    -- only the Nat instance: the sum is then exactly `Zempic.Fuse.sum`
    if ← isCallTo ``instAddNat args[1]! then
      return some (.const ``Zempic.Fuse.sum us #[args[3]!])
  return none

mutual
/-- Rewrite the body of a local function or join point. -/
partial def goFun (d : FunDecl .pure) : CompilerM (FunDecl .pure) := do
  d.updateValue (← go d.value)

/-- Rewrite every recognized list call in `c`, leaving the rest unchanged. -/
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

/-- The pass: a no-op unless `zempic.fuse` is set. -/
def pass : Pass where
  phase := .base
  name := `zempicFuse
  run decls := do
    unless zempic.fuse.get (← getOptions) do return decls
    decls.mapM fun d => do
      match d.value with
      | .code c => return { d with value := .code (← go c) }
      | _ => return d

/-- Install `pass` just before Lean's `specialize`. -/
@[cpass] def installer : PassInstaller :=
  PassInstaller.installBefore .base `specialize (fun _ => pass)

end Zempic.AutoFuse
