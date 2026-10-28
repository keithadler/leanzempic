/-
Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.

Printers over Lean's LCNF (mono phase) terms. LCNF is already erased, in
A-normal form, with explicit join points and Lean's strict evaluation order, so
printing it gives GHC input that is shaped like Core: every `let` is a strict
`case`-binding, every join point is a local function in tail position, and
nothing is left lazy by accident.
-/
import Lean

open Lean Compiler LCNF

namespace Zempic

/-! ## Names -/

def mangle (s : String) : String :=
  s.foldl (fun acc c =>
    if c.isAlphanum && c.toNat < 128 then acc.push c
    else if c == '_' then acc ++ "__"
    else if c == '.' then acc.push '_'
    else acc ++ s!"_x{String.ofList (Nat.toDigits 16 c.toNat)}_") ""

def fnName (n : Name) : String := "z_" ++ mangle n.toString
def ctorName (n : Name) : String := "ZC_" ++ mangle n.toString
def typeName (n : Name) : String := "ZT_" ++ mangle n.toString

def hsStr (s : String) : String :=
  "\"" ++ s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c.toNat >= 32 && c.toNat < 127 then acc.push c
    else acc ++ s!"\\{c.toNat}\\&") "" ++ "\""

/-! ## Primitives that the runtime implements -/

/-- Lean constants implemented by `runtime/Zempic/Runtime.hs`: name, Haskell name, arity. -/
def prims : List (Name × String × Nat) :=
  [ (`Nat.add, "natAdd", 2), (`Nat.sub, "natSub", 2), (`Nat.mul, "natMul", 2)
  , (`Nat.div, "natDiv", 2), (`Nat.mod, "natMod", 2), (`Nat.pow, "natPow", 2)
  , (`Nat.decEq, "natEq", 2), (`Nat.beq, "natEq", 2)
  , (`Nat.decLt, "natLt", 2), (`Nat.blt, "natLt", 2)
  , (`Nat.decLe, "natLe", 2), (`Nat.ble, "natLe", 2)
  , (`Nat.shiftRight, "natShr", 2), (`Nat.shiftLeft, "natShl", 2), (`Nat.land, "natAnd", 2)
  , (`Nat.lor, "natOr", 2), (`Nat.xor, "natXor", 2), (`Nat.gcd, "natGcd", 2)
  , (`Nat.succ, "natSucc", 1), (`Nat.zero, "natZero", 0)
  , (`Bool.true, "hsTrue", 0), (`Bool.false, "hsFalse", 0) ]

/-- Types with a builtin runtime representation; building or matching them is not supported yet. -/
def builtinTypes : List Name :=
  [`Nat, `Int, `String, `Array, `ByteArray, `FloatArray, `UInt8, `UInt16, `UInt32, `UInt64,
   `USize, `Char, `Float, `Thunk, `Task]

/-! ## Emitter state -/

structure St where
  names : Std.HashMap FVarId String := {}
  jps : Std.HashSet FVarId := {}
  next : Nat := 0
  queue : Array Name := #[]
  seen : NameSet := {}
  types : Array Name := #[]
  unsupported : Array String := #[]

abbrev EmitM := StateRefT St CoreM

def unsupported (what : String) : EmitM Unit :=
  modify fun s => if s.unsupported.contains what then s else { s with unsupported := s.unsupported.push what }

def bind (id : FVarId) (base : Name) : EmitM String := do
  let s ← get
  let short := (base.toString.toList.filter (fun c => c.isAlphanum && c.toNat < 128)).take 10 |> String.ofList
  let nm := s!"v{s.next}_{short}"
  set { s with next := s.next + 1, names := s.names.insert id nm }
  return nm

def lookup (id : FVarId) : EmitM String := do
  match (← get).names[id]? with
  | some n => return n
  | none => unsupported s!"unbound variable {id.name}"; return "undefined"

def noteType (t : Name) : EmitM Unit := do
  if t == `Bool then return
  if builtinTypes.contains t then unsupported s!"builtin type {t}"; return
  modify fun s => if s.types.contains t then s else { s with types := s.types.push t }

def request (n : Name) : EmitM Unit :=
  modify fun s => if s.seen.contains n then s else { s with seen := s.seen.insert n, queue := s.queue.push n }

def atom : Arg .pure → EmitM String
  | .fvar id => lookup id
  | _ => return "erased"

def monoDecl? (n : Name) : EmitM (Option (Decl .pure)) := do
  match ← getDeclAt? n .mono with
  | some d => return some d
  | none => return none

/-- How a constant is called. -/
inductive Head
  | prim (hs : String) (arity : Nat)
  | ctor (hs : String) (arity numParams : Nat)
  | decl (hs : String) (arity : Nat)
  | bad

def resolve (c : Name) : EmitM Head := do
  if let some (_, hs, a) := prims.find? (·.1 == c) then return .prim hs a
  match (← getEnv).find? c with
  | some (.ctorInfo v) =>
    noteType v.induct
    return .ctor (ctorName c) v.numFields v.numParams
  | _ =>
    match ← monoDecl? c with
    | some d =>
      match d.value with
      | .code _ => request c; return .decl (fnName c) d.params.size
      | .extern _ => unsupported s!"extern {c}"; return .bad
    | none => unsupported s!"constant {c}"; return .bad

def apply (head : String) (arity : Nat) (args : Array String) (ctor : Bool) : String :=
  let call (h : String) (xs : Array String) :=
    if xs.isEmpty then h else h ++ " " ++ " ".intercalate xs.toList
  if args.size ≤ arity then
    let e := call head args
    if ctor || args.size < arity then s!"(zo ({e}))" else e
  else
    let sat := call head (args.extract 0 arity)
    let sat := if ctor then s!"(zo ({sat}))" else sat
    (args.extract arity args.size).foldl (fun acc a => s!"(zap {acc} {a})") sat

def single (t : Name) : EmitM (Option (Name × Nat)) := do
  noteType t
  match (← getEnv).find? t with
  | some (.inductInfo v) =>
    match v.ctors with
    | [c] => match (← getEnv).find? c with
      | some (.ctorInfo cv) => return some (c, cv.numFields)
      | _ => return none
    | _ => return none
  | _ => return none

def pad (n : Nat) : String := "".pushn ' ' (2 * n)

/-! ## Haskell printer -/

def hsLetValue : LetValue .pure → EmitM String
  | .lit (.nat n) => return s!"(zo ({n} :: Natural))"
  | .lit (.str s) => return s!"(zo ({hsStr s} :: String))"
  | .lit _ => do unsupported "fixed-width integer literal"; return "erased"
  | .erased => return "erased"
  | .fvar f args => do
    let f ← lookup f
    let args ← args.mapM atom
    return args.foldl (fun acc a => s!"(zap {acc} {a})") f
  | .proj t i x => do
    let x ← lookup x
    match ← single t with
    | some (c, n) =>
      let ps := (List.range n).map (s!"p{·}")
      return s!"(case (zu {x} :: {typeName t}) of \{ {ctorName c} {" ".intercalate ps} -> p{i} })"
    | none => unsupported s!"projection on {t}"; return "erased"
  | .const c _ args => do
    let args ← args.mapM atom
    match ← resolve c with
    | .prim hs a => return apply hs a args false
    | .decl hs a => return apply hs a args false
    | .ctor hs a np => return apply hs a (args.extract np args.size) true
    | .bad => return "erased"

mutual
partial def hsCode (c : Code .pure) (ind : Nat) : EmitM String := do
  match c with
  | .let d k =>
    let rhs ← hsLetValue d.value
    let x ← bind d.fvarId d.binderName
    return s!"let \{ !{x} = {rhs} } in\n{pad ind}{← hsCode k ind}"
  | .fun d k =>
    let ps ← d.params.mapM fun p => bind p.fvarId p.binderName
    let f ← bind d.fvarId d.binderName
    let body ← hsCode d.value (ind + 2)
    return s!"let \{ {f} = zo (\\{" ".intercalate ps.toList} ->\n{pad (ind + 2)}{body}) } in\n{pad ind}{← hsCode k ind}"
  | .jp d k =>
    let ps ← d.params.mapM fun p => bind p.fvarId p.binderName
    let j ← bind d.fvarId d.binderName
    modify fun s => { s with jps := s.jps.insert d.fvarId }
    let body ← hsCode d.value (ind + 2)
    return s!"let \{ {j} {" ".intercalate ps.toList} =\n{pad (ind + 2)}{body} } in\n{pad ind}{← hsCode k ind}"
  | .jmp j args =>
    let j ← lookup j
    let args ← args.mapM atom
    return " ".intercalate (j :: args.toList)
  | .return x => lookup x
  | .unreach _ => return "error \"leanzempic: unreachable\""
  | .cases cs =>
    let x ← lookup cs.discr
    let ty := if cs.typeName == `Bool then "Bool" else typeName cs.typeName
    noteType cs.typeName
    let mut alts : Array String := #[]
    for a in cs.alts do
      match a with
      | .alt n ps k =>
        let pat ←
          if n == `Bool.true then pure "True"
          else if n == `Bool.false then pure "False"
          else do
            let bs ← ps.mapM fun p => bind p.fvarId p.binderName
            pure (" ".intercalate (ctorName n :: bs.toList))
        alts := alts.push s!"{pat} ->\n{pad (ind + 2)}{← hsCode k (ind + 2)}"
      | .default k => alts := alts.push s!"_ ->\n{pad (ind + 2)}{← hsCode k (ind + 2)}"
    let sep := s!";\n{pad (ind + 1)}"
    return s!"case (zu {x} :: {ty}) of \{\n{pad (ind + 1)}{sep.intercalate alts.toList} }"
end

def hsDecl (d : Decl .pure) : EmitM String := do
  let .code body := d.value | return ""
  let ps ← d.params.mapM fun p => bind p.fvarId p.binderName
  let n := fnName d.name
  let sig := " -> ".intercalate ((ps.toList.map fun _ => "Any") ++ ["Any"])
  let body ← hsCode body 1
  return s!"{n} :: {sig}\n{n} {" ".intercalate ps.toList} =\n{pad 1}{body}\n"

/-! ## Core-notation printer (for reading; GHC cannot ingest this) -/

def coreAtom : Arg .pure → EmitM String := atom

def coreLetValue : LetValue .pure → EmitM String
  | .lit (.nat n) => return s!"{n}"
  | .lit (.str s) => return hsStr s
  | .lit _ => return "<lit>"
  | .erased => return "@erased"
  | .fvar f args => do return " ".intercalate ((← lookup f) :: (← args.mapM atom).toList)
  | .proj t i x => do return s!"{← lookup x}.{i} @{t}"
  | .const c _ args => do
    let args := (← args.mapM atom).filter (· != "erased")
    let h := if (← getEnv).isConstructor c then ctorName c else fnName c
    return " ".intercalate (h :: args.toList)

mutual
partial def coreCode (c : Code .pure) (ind : Nat) : EmitM String := do
  match c with
  | .let d k =>
    let rhs ← coreLetValue d.value
    let x ← bind d.fvarId d.binderName
    return s!"case {rhs} of {x} \{ __DEFAULT ->\n{pad (ind + 1)}{← coreCode k (ind + 1)} }"
  | .fun d k =>
    let ps ← d.params.mapM fun p => bind p.fvarId p.binderName
    let f ← bind d.fvarId d.binderName
    let body ← coreCode d.value (ind + 2)
    return s!"let \{ {f} = \\ {" ".intercalate ps.toList} ->\n{pad (ind + 2)}{body} } in\n{pad ind}{← coreCode k ind}"
  | .jp d k =>
    let ps ← d.params.mapM fun p => bind p.fvarId p.binderName
    let j ← bind d.fvarId d.binderName
    let body ← coreCode d.value (ind + 2)
    return s!"join \{ {j} {" ".intercalate ps.toList} =\n{pad (ind + 2)}{body} } in\n{pad ind}{← coreCode k ind}"
  | .jmp j args =>
    return " ".intercalate ("jump" :: (← lookup j) :: (← args.mapM atom).toList)
  | .return x => lookup x
  | .unreach _ => return "@unreachable"
  | .cases cs =>
    let x ← lookup cs.discr
    let mut alts : Array String := #[]
    for a in cs.alts do
      match a with
      | .alt n ps k =>
        let bs ← ps.mapM fun p => bind p.fvarId p.binderName
        alts := alts.push s!"{" ".intercalate (ctorName n :: bs.toList)} ->\n{pad (ind + 2)}{← coreCode k (ind + 2)}"
      | .default k => alts := alts.push s!"__DEFAULT ->\n{pad (ind + 2)}{← coreCode k (ind + 2)}"
    let sep := s!";\n{pad (ind + 1)}"
    return s!"case {x} of wild \{\n{pad (ind + 1)}{sep.intercalate alts.toList} }"
end

def coreDecl (d : Decl .pure) : EmitM String := do
  let .code body := d.value | return ""
  let ps ← d.params.mapM fun p => bind p.fvarId p.binderName
  let lam := if ps.isEmpty then "" else s!"\\ {" ".intercalate ps.toList} ->\n{pad 2}"
  return s!"{fnName d.name} [Arity={ps.size}] =\n{pad 1}{lam}{← coreCode body 2}\n"

/-! ## Whole-module output -/

structure Output where
  haskell : String
  core : String

def dataDecl (t : Name) : EmitM String := do
  match (← getEnv).find? t with
  | some (.inductInfo v) =>
    let mut cs : Array String := #[]
    for c in v.ctors do
      if let some (.ctorInfo cv) := (← getEnv).find? c then
        cs := cs.push (" ".intercalate (ctorName c :: List.replicate cv.numFields "!Any"))
    return s!"data {typeName t} = {" | ".intercalate cs.toList}\n"
  | _ => unsupported s!"type {t}"; return ""

/-- Compile `roots` and everything they reach into one Haskell module plus a Core-notation dump. -/
def emitModule (modName : String) (roots : Array Name) : CoreM Output := do
  let act : EmitM Output := do
    for r in roots do request r
    let mut hs : Array String := #[]
    let mut core : Array String := #[]
    let mut i := 0
    while i < (← get).queue.size do
      let n := (← get).queue[i]!
      i := i + 1
      match ← monoDecl? n with
      | some d =>
        hs := hs.push (← hsDecl d)
        core := core.push (← coreDecl d)
      | none => unsupported s!"constant {n}"
    let mut datas : Array String := #[]
    for t in (← get).types do datas := datas.push (← dataDecl t)
    let bad := (← get).unsupported
    unless bad.isEmpty do
      throwError "leanzempic: unsupported in this version:\n  {"\n  ".intercalate bad.toList}"
    let header := s!"\{-# LANGUAGE BangPatterns #-}\n\{-# OPTIONS_GHC -Wno-unused-matches -Wno-unused-imports #-}\n-- Generated by leanzempic. Do not edit.\nmodule {modName} where\n\nimport Zempic.Runtime\nimport Numeric.Natural (Natural)\n\n"
    return { haskell := header ++ "\n".intercalate (datas ++ hs).toList
             core := "-- leanzempic Core-notation dump (for reading)\n\n" ++ "\n".intercalate core.toList }
  act.run' {}

end Zempic
