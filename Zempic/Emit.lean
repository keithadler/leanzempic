/-
Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.

Printers over Lean's LCNF (mono phase) terms. LCNF is already erased, in
A-normal form, with explicit join points and Lean's strict evaluation order, so
printing it gives GHC input that is shaped like Core: every `let` is a strict
`case`-binding, every join point is a local function in tail position, and
nothing is left lazy by accident.
-/
import Lean
import Zempic.Names

open Lean Compiler LCNF

namespace Zempic

/-! ## Names -/

/-- Haskell name of a compiled Lean function. -/
def fnName (n : Name) : String := "z_" ++ mangle n.toString
/-- Haskell name of a Lean constructor. -/
def ctorName (n : Name) : String := "ZC_" ++ mangle n.toString
/-- Haskell name of the `data` type generated for a Lean inductive. -/
def typeName (n : Name) : String := "ZT_" ++ mangle n.toString

/-- A Haskell string literal for `s`, escaping everything outside printable ASCII. -/
def hsStr (s : String) : String :=
  "\"" ++ s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c.toNat >= 32 && c.toNat < 127 then acc.push c
    else acc ++ s!"\\{c.toNat}\\&") "" ++ "\""

/-! ## Primitives that the runtime implements -/

/-- Lean constants implemented by the Haskell runtime (`runtime/Zempic/*.hs`): Haskell name,
argument types, result type. -/
def prims : List (Name × String × List String × String) :=
  let n2 := ["ZNat", "ZNat"]
  [ (`Nat.add, "natAdd", n2, "ZNat"), (`Nat.sub, "natSub", n2, "ZNat")
  , (`Nat.mul, "natMul", n2, "ZNat"), (`Nat.div, "natDiv", n2, "ZNat")
  , (`Nat.mod, "natMod", n2, "ZNat"), (`Nat.pow, "natPow", n2, "ZNat")
  , (`Nat.decEq, "natEq", n2, "Bool"), (`Nat.beq, "natEq", n2, "Bool")
  , (`Nat.decLt, "natLt", n2, "Bool"), (`Nat.blt, "natLt", n2, "Bool")
  , (`Nat.decLe, "natLe", n2, "Bool"), (`Nat.ble, "natLe", n2, "Bool")
  , (`Nat.shiftRight, "natShr", n2, "ZNat"), (`Nat.shiftLeft, "natShl", n2, "ZNat")
  , (`Nat.land, "natAnd", n2, "ZNat"), (`Nat.lor, "natOr", n2, "ZNat")
  , (`Nat.xor, "natXor", n2, "ZNat"), (`Nat.gcd, "natGcd", n2, "ZNat")
  , (`Nat.succ, "natSucc", ["ZNat"], "ZNat"), (`Nat.zero, "natZero", [], "ZNat")
  , (`List.nil, "zNil", ["Any"], "[Any]"), (`List.cons, "zCons", ["Any", "Any", "[Any]"], "[Any]")
  , (`Zempic.Fuse.map, "zMap", ["Any", "Any", "Any -> Any", "[Any]"], "[Any]")
  , (`Zempic.Fuse.map._redArg, "zMap", ["Any -> Any", "[Any]"], "[Any]")
  , (`Zempic.Fuse.filter, "zFilter", ["Any", "Any -> Any", "[Any]"], "[Any]")
  , (`Zempic.Fuse.filter._redArg, "zFilter", ["Any -> Any", "[Any]"], "[Any]")
  , (`Zempic.Fuse.foldl, "zFoldl", ["Any", "Any", "Any -> Any -> Any", "Any", "[Any]"], "Any")
  , (`Zempic.Fuse.foldl._redArg, "zFoldl", ["Any -> Any -> Any", "Any", "[Any]"], "Any")
  , (`Zempic.Fuse.range, "zRange", ["ZNat"], "[Any]")
  , (`Zempic.Fuse.range._redArg, "zRange", ["ZNat"], "[Any]")
  , (`Bool.true, "True", [], "Bool"), (`Bool.false, "False", [], "Bool") ]

/-- Types with a builtin runtime representation; building or matching them is not supported yet. -/
def builtinTypes : List Name :=
  [`Nat, `Int, `String, `Array, `ByteArray, `FloatArray, `UInt8, `UInt16, `UInt32, `UInt64,
   `USize, `Char, `Float, `Thunk, `Task]

/-! ## Emitter state -/

/-- Emitter state: variable names and types, join points, the queue of constants still to
compile, and what is unsupported. -/
structure St where
  /-- Haskell name of each variable. -/
  names : Std.HashMap FVarId String := {}
  /-- Haskell type of each variable. -/
  tys : Std.HashMap FVarId String := {}
  /-- Parameter types of each join point. -/
  jpTys : Std.HashMap FVarId (List String) := {}
  /-- Join points seen. -/
  jps : Std.HashSet FVarId := {}
  /-- Counter for fresh names. -/
  next : Nat := 0
  /-- Constants still to compile. -/
  queue : Array Name := #[]
  /-- Constants ever queued. -/
  seen : NameSet := {}
  /-- Inductive types that need a `data` declaration. -/
  types : Array Name := #[]
  /-- Everything that could not be compiled. -/
  unsupported : Array String := #[]
  /-- Word-sized Nat: literals above 2^64 - 1 must raise `ZOverflow`. -/
  fast : Bool := false

/-- The emitter monad. -/
abbrev EmitM := StateRefT St CoreM

/-- Record that `what` cannot be compiled yet; reported together at the end. -/
def unsupported (what : String) : EmitM Unit :=
  modify fun s =>
    if s.unsupported.contains what then s
    else { s with unsupported := s.unsupported.push what }

/-- Give a fresh Haskell name and type to the variable `id`. -/
def bindT (id : FVarId) (base : Name) (ty : String) : EmitM String := do
  let s ← get
  let ok := fun (c : Char) => c.isAlphanum && c.toNat < 128
  let short := String.ofList ((base.toString.toList.filter ok).take 10)
  let nm := s!"v{s.next}_{short}"
  set { s with next := s.next + 1, names := s.names.insert id nm, tys := s.tys.insert id ty }
  return nm

/-- `bindT` at type `Any`. -/
def bind (id : FVarId) (base : Name) : EmitM String := bindT id base "Any"

/-- Haskell type for a Lean type: only `Nat` and `Bool` are typed so far; everything else is
`Any`. -/
def hsTy : Expr → String
  | .const `Nat _ => "ZNat"
  | .const `Bool _ => "Bool"
  | _ => "Any"

/-- Bind a parameter at its mapped type. -/
def bindP (p : Param .pure) : EmitM String := bindT p.fvarId p.binderName (hsTy p.type)

/-- The Haskell name of a variable. -/
def lookup (id : FVarId) : EmitM String := do
  match (← get).names[id]? with
  | some n => return n
  | none => unsupported s!"unbound variable {id.name}"; return "undefined"

/-- The Haskell type recorded for a variable (`Any` if unknown). -/
def tyOf (id : FVarId) : EmitM String := do
  return (← get).tys[id]?.getD "Any"

/-- Cast `x` of Haskell type `have` to `want`. Casts between `Any` and a real type are free in
Core. -/
def coerce (x have_ want : String) : String :=
  if have_ == want then x
  else if want == "Any" then s!"(zo {x})"
  else if have_ == "Any" then s!"(zu {x})"
  else s!"(zu (zo {x}))"

/-- Use variable `id` at Haskell type `want`, casting if needed. -/
def useAs (id : FVarId) (want : String) : EmitM String := do
  return coerce (← lookup id) (← tyOf id) want

/-- Producers whose result may stay lazy so GHC can fuse them into their consumer. -/
def fuseProducers : List Name :=
  [`Zempic.Fuse.map, `Zempic.Fuse.map._redArg, `Zempic.Fuse.filter, `Zempic.Fuse.filter._redArg,
   `Zempic.Fuse.range, `Zempic.Fuse.range._redArg]

/-- Remember that the `data` type for `t` must be generated (builtin types are rejected). -/
def noteType (t : Name) : EmitM Unit := do
  if t == `Bool || t == `List then return
  if builtinTypes.contains t then unsupported s!"builtin type {t}"; return
  modify fun s => if s.types.contains t then s else { s with types := s.types.push t }

/-- Queue constant `n` for compilation unless already seen. -/
def request (n : Name) : EmitM Unit :=
  modify fun s =>
    if s.seen.contains n then s
    else { s with seen := s.seen.insert n, queue := s.queue.push n }

/-- Haskell name of an argument; erased arguments become `erased`. -/
def atom : Arg .pure → EmitM String
  | .fvar id => lookup id
  | _ => return "erased"

/-- The mono-phase declaration of `n`, if Lean compiled one. -/
def monoDecl? (n : Name) : EmitM (Option (Decl .pure)) := do
  match ← getDeclAt? n .mono with
  | some d => return some d
  | none => return none

/-- How a constant is called. -/
inductive Head
  /-- A function from the Haskell runtime. -/
  | prim (hs : String) (ptys : List String) (ret : String)
  /-- A constructor: its Haskell name, field count and (dropped) parameter count. -/
  | ctor (hs : String) (arity numParams : Nat)
  /-- A function compiled from Lean. -/
  | decl (hs : String) (ptys : List String) (ret : String)
  /-- Not supported; already recorded as such. -/
  | bad

/-- Haskell result type of a declaration, read from its Lean type. -/
def declRet (d : Decl .pure) : String := hsTy (d.type.getForallBodyMaxDepth d.params.size)

/-- Decide how constant `c` is called: runtime primitive, constructor, compiled function or
unsupported. -/
def resolve (c : Name) : EmitM Head := do
  if let some (_, hs, ptys, ret) := prims.find? (·.1 == c) then return .prim hs ptys ret
  match (← getEnv).find? c with
  | some (.ctorInfo v) =>
    noteType v.induct
    return .ctor (ctorName c) v.numFields v.numParams
  | _ =>
    match ← monoDecl? c with
    | some d =>
      match d.value with
      | .code _ =>
        request c
        return .decl (fnName c) (d.params.toList.map (hsTy ·.type)) (declRet d)
      | .extern _ => unsupported s!"extern {c}"; return .bad
    | none => unsupported s!"constant {c}"; return .bad

/-- Apply `head` (parameter types `ptys`, result `ret`) to typed atoms; returns the expression and
its type. -/
def apply (head : String) (ptys : List String) (ret : String) (args : Array (String × String))
    (ctor : Bool) : String × String :=
  let arity := ptys.length
  let call (xs : List String) := if xs.isEmpty then head else head ++ " " ++ " ".intercalate xs
  let cast := fun (i : Nat) (a : String × String) => coerce a.1 a.2 (ptys.getD i "Any")
  if args.size ≤ arity then
    let e := call ((args.toList.zipIdx.map fun (a, i) => cast i a))
    if ctor || args.size < arity then (s!"(zo ({e}))", "Any")
    else if arity == 0 then (head, ret) else (e, ret)
  else
    let sat := call (((args.extract 0 arity).toList.zipIdx.map fun (a, i) => cast i a))
    let sat := if ctor || ret != "Any" then s!"(zo ({sat}))" else sat
    let rest := args.extract arity args.size
    (rest.foldl (fun acc a => s!"(zap {acc} {coerce a.1 a.2 "Any"})") sat, "Any")

/-- The constructor and field count of a single-constructor structure, or `none`. -/
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

/-- Indentation of `n` levels. -/
def pad (n : Nat) : String := "".pushn ' ' (2 * n)

/-! ## Haskell printer -/

/-- An argument with its Haskell name and type. -/
def atomT : Arg .pure → EmitM (String × String)
  | .fvar id => return (← lookup id, ← tyOf id)
  | _ => return ("erased", "Any")

/-- Expression and its Haskell type. -/
def hsLetValue : LetValue .pure → EmitM (String × String)
  | .lit (.nat n) => do
    if (← get).fast && n ≥ 2 ^ 64 then return ("(overflow :: ZNat)", "ZNat")
    return (s!"({n} :: ZNat)", "ZNat")
  | .lit (.str s) => return (s!"(zo ({hsStr s} :: String))", "Any")
  | .lit _ => do unsupported "fixed-width integer literal"; return ("erased", "Any")
  | .erased => return ("erased", "Any")
  | .fvar f args => do
    let f ← useAs f "Any"
    let args ← args.mapM atomT
    return (args.foldl (fun acc a => s!"(zap {acc} {coerce a.1 a.2 "Any"})") f, "Any")
  | .proj t i x => do
    let x ← useAs x "Any"
    match ← single t with
    | some (c, n) =>
      let ps := (List.range n).map (s!"p{·}")
      let pat := s!"{ctorName c} {" ".intercalate ps}"
      return (s!"(case (zu {x} :: {typeName t}) of \{ {pat} -> p{i} })", "Any")
    | none => unsupported s!"projection on {t}"; return ("erased", "Any")
  | .const c _ args => do
    let args ← args.mapM atomT
    match ← resolve c with
    | .prim hs ptys ret => return apply hs ptys ret args false
    | .decl hs ptys ret => return apply hs ptys ret args false
    | .ctor hs a np =>
      return apply hs (List.replicate a "Any") "Any" (args.extract np args.size) true
    | .bad => return ("erased", "Any")

mutual
/-- Print LCNF code as a Haskell expression whose result has type `ret`. -/
partial def hsCode (c : Code .pure) (ind : Nat) (ret : String) : EmitM String := do
  match c with
  | .let d k =>
    let (rhs, ty) ← hsLetValue d.value
    let x ← bindT d.fvarId d.binderName ty
    let lazy := match d.value with | .const c _ _ => fuseProducers.contains c | _ => false
    let bang := if lazy then "" else "!"
    return s!"let \{ {bang}{x} = {rhs} } in\n{pad ind}{← hsCode k ind ret}"
  | .fun d k =>
    let ps ← d.params.mapM fun p => bind p.fvarId p.binderName
    let f ← bind d.fvarId d.binderName
    let body ← hsCode d.value (ind + 2) "Any"
    let lam := " ".intercalate ps.toList
    let rest ← hsCode k ind ret
    return s!"let \{ {f} = zo (\\{lam} ->\n{pad (ind + 2)}{body}) } in\n{pad ind}{rest}"
  | .jp d k =>
    let tys := d.params.toList.map (hsTy ·.type)
    let ps ← d.params.mapM fun p => bindP p
    let ps := (ps.toList.zip tys).map fun (p, t) => s!"({p} :: {t})"
    let j ← bind d.fvarId d.binderName
    modify fun s => { s with jps := s.jps.insert d.fvarId, jpTys := s.jpTys.insert d.fvarId tys }
    let body ← hsCode d.value (ind + 2) ret
    let rest ← hsCode k ind ret
    return s!"let \{ {j} {" ".intercalate ps} =\n{pad (ind + 2)}{body} } in\n{pad ind}{rest}"
  | .jmp j args =>
    let tys := (← get).jpTys[j]?.getD []
    let j ← lookup j
    let args ← args.mapM atomT
    let args := args.toList.zipIdx.map fun (a, i) => coerce a.1 a.2 (tys.getD i "Any")
    return " ".intercalate (j :: args)
  | .return x => useAs x ret
  | .unreach _ => return "error \"leanzempic: unreachable\""
  | .cases cs =>
    let ty := if cs.typeName == `Bool then "Bool"
      else if cs.typeName == `List then "[Any]" else typeName cs.typeName
    let x ← useAs cs.discr ty
    noteType cs.typeName
    let mut alts : Array String := #[]
    for a in cs.alts do
      match a with
      | .alt n ps k =>
        let pat ←
          if n == `Bool.true then pure "True"
          else if n == `Bool.false then pure "False"
          else if n == `List.nil then pure "[]"
          else if n == `List.cons then do
            let h ← bind ps[0]!.fvarId ps[0]!.binderName
            let t ← bindT ps[1]!.fvarId ps[1]!.binderName "[Any]"
            pure s!"({h} : {t})"
          else do
            let bs ← ps.mapM fun p => bind p.fvarId p.binderName
            pure (" ".intercalate (ctorName n :: bs.toList))
        alts := alts.push s!"{pat} ->\n{pad (ind + 2)}{← hsCode k (ind + 2) ret}"
      | .default k => alts := alts.push s!"_ ->\n{pad (ind + 2)}{← hsCode k (ind + 2) ret}"
    let sep := s!";\n{pad (ind + 1)}"
    return s!"case ({x} :: {ty}) of \{\n{pad (ind + 1)}{sep.intercalate alts.toList} }"
end

/-- Print one declaration as a typed Haskell function. -/
def hsDecl (d : Decl .pure) : EmitM String := do
  let .code body := d.value | return ""
  let ps ← d.params.mapM bindP
  let n := fnName d.name
  let ret := declRet d
  let sig := " -> ".intercalate ((d.params.toList.map (hsTy ·.type)) ++ [ret])
  let body ← hsCode body 1 ret
  return s!"{n} :: {sig}\n{n} {" ".intercalate ps.toList} =\n{pad 1}{body}\n"

/-! ## Core-notation printer (for reading; GHC cannot ingest this) -/

/-- An argument in the Core dump. -/
def coreAtom : Arg .pure → EmitM String := atom

/-- A `let` right-hand side in the Core dump. -/
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
/-- Print LCNF code in Core notation (for reading; GHC cannot ingest it). -/
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
    let rest ← coreCode k ind
    let lam := " ".intercalate ps.toList
    return s!"let \{ {f} = \\ {lam} ->\n{pad (ind + 2)}{body} } in\n{pad ind}{rest}"
  | .jp d k =>
    let ps ← d.params.mapM fun p => bind p.fvarId p.binderName
    let j ← bind d.fvarId d.binderName
    let body ← coreCode d.value (ind + 2)
    let rest ← coreCode k ind
    let params := " ".intercalate ps.toList
    return s!"join \{ {j} {params} =\n{pad (ind + 2)}{body} } in\n{pad ind}{rest}"
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
        let body ← coreCode k (ind + 2)
        alts := alts.push s!"{" ".intercalate (ctorName n :: bs.toList)} ->\n{pad (ind + 2)}{body}"
      | .default k => alts := alts.push s!"__DEFAULT ->\n{pad (ind + 2)}{← coreCode k (ind + 2)}"
    let sep := s!";\n{pad (ind + 1)}"
    return s!"case {x} of wild \{\n{pad (ind + 1)}{sep.intercalate alts.toList} }"
end

/-- Print one declaration in Core notation. -/
def coreDecl (d : Decl .pure) : EmitM String := do
  let .code body := d.value | return ""
  let ps ← d.params.mapM fun p => bind p.fvarId p.binderName
  let lam := if ps.isEmpty then "" else s!"\\ {" ".intercalate ps.toList} ->\n{pad 2}"
  return s!"{fnName d.name} [Arity={ps.size}] =\n{pad 1}{lam}{← coreCode body 2}\n"

/-! ## Whole-module output -/

/-- Printed output of one module. -/
structure Output where
  /-- The Haskell module text. -/
  haskell : String
  /-- The Core-notation dump. -/
  core : String

/-- The Haskell `data` declaration for Lean inductive `t`. -/
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
def emitModule (modName : String) (roots : Array Name) (natMod : String := "Zempic.Nat.Exact")
    (fast : Bool := false) : CoreM Output := do
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
    let header := "\n".intercalate [
      "{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}",
      "{-# OPTIONS_GHC -Wno-unused-matches -Wno-unused-imports #-}",
      "-- Generated by leanzempic. Do not edit.",
      s!"module {modName} where", "",
      "import Zempic.Runtime", s!"import {natMod}", "import Zempic.List", "", ""]
    return { haskell := header ++ "\n".intercalate (datas ++ hs).toList
             core := "-- leanzempic Core-notation dump (for reading)\n\n" ++
               "\n".intercalate core.toList }
  act.run' { fast }

/-- Haskell wrapper for auto mode: for each root whose signature is only `Nat`/`Bool`, run the
`Word` version and fall back to the exact one if it overflows. -/
def autoWrapper (modName : String) (roots : Array Name) : CoreM String := do
  let mut exports : Array String := #[]
  let mut defs : Array String := #[]
  let mut skipped : Array String := #[]
  for r in roots do
    let some d ← getDeclAt? r .mono | continue
    let ptys := d.params.toList.map (hsTy ·.type)
    let ret := declRet d
    let ok := (ptys.all fun t => t == "ZNat" || t == "Bool") && (ret == "ZNat" || ret == "Bool")
    if !ok then skipped := skipped.push (fnName r); continue
    let hs := fun (t : String) => if t == "ZNat" then "Natural" else "Bool"
    let names := (List.range ptys.length).map (s!"a{·}")
    let fastArgs := (names.zip ptys).map fun (a, t) => if t == "ZNat" then s!"(toW {a})" else a
    let call := fun (q : String) (xs : List String) => " ".intercalate (s!"{q}.{fnName r}" :: xs)
    let conv := if ret == "ZNat" then "fromIntegral" else "id"
    let sig := " -> ".intercalate ((ptys.map hs) ++ [hs ret])
    exports := exports.push (fnName r)
    let lhs := " ".intercalate (fnName r :: names)
    let body := s!"tryFast {conv} ({call "F" fastArgs}) ({call "E" names})"
    defs := defs.push s!"{fnName r} :: {sig}\n{lhs} =\n  {body}\n"
  let note := if skipped.isEmpty then "" else
    let who := ", ".intercalate skipped.toList
    s!"-- Not wrapped (signature mentions non-Nat/Bool values): {who}.\n" ++
    s!"-- Use {modName}.Fast / {modName}.Exact directly.\n"
  let hdr := "-- Generated by leanzempic (auto mode). Do not edit.\n"
  let exps := ", ".intercalate exports.toList
  let imports := "import Numeric.Natural (Natural)\nimport Zempic.Auto\n" ++
    s!"import qualified {modName}.Fast as F\nimport qualified {modName}.Exact as E\n"
  return s!"{hdr}{note}module {modName} ({exps}) where\n\n{imports}\n{"\n".intercalate defs.toList}"

/-- Files (relative path, contents) and the Core dump for `mode` = `auto`, `word` or `exact`. -/
def emitFiles (modName : String) (roots : Array Name) (mode : String) :
    CoreM (Array (String × String) × String) := do
  let rel := fun (m : String) => (m.replace "." "/") ++ ".hs"
  match mode with
  | "word" =>
    let o ← emitModule modName roots "Zempic.Nat.Word" true
    return (#[(rel modName, o.haskell)], o.core)
  | "exact" =>
    let o ← emitModule modName roots "Zempic.Nat.Exact" false
    return (#[(rel modName, o.haskell)], o.core)
  | _ =>
    let fast ← emitModule (modName ++ ".Fast") roots "Zempic.Nat.Word" true
    let exact ← emitModule (modName ++ ".Exact") roots "Zempic.Nat.Exact" false
    let wrap ← autoWrapper modName roots
    return (#[(rel modName, wrap), (rel (modName ++ ".Fast"), fast.haskell),
              (rel (modName ++ ".Exact"), exact.haskell)], exact.core)

end Zempic
