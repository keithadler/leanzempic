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
import Zempic.Own

open Lean Compiler LCNF

namespace Zempic

/-- Largest literal that a recursive call's counter may have for the call to be unrolled. -/
register_option zempic.unroll : Nat := {
  defValue := 16
  descr := "(leanzempic) unroll self-recursive calls whose Nat argument is a literal up to this; 0 = off"
}

/-- Give arrays of numeric and `Bool` elements an unboxed buffer when the element type is known. -/
register_option zempic.typedArrays : Bool := {
  defValue := true
  descr := "(leanzempic) store arrays of UInt8/16/32/64, Bool, Char, USize and Nat as unboxed buffers"
}

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
  , (`Zempic.Fuse.map._redArg, "zMap", ["Any -> Any", "[Any]"], "[Any]")
  , (`Zempic.Fuse.filter._redArg, "zFilter", ["Any -> Any", "[Any]"], "[Any]")
  , (`Zempic.Fuse.foldl._redArg, "zFoldl", ["Any -> Any -> Any", "Any", "[Any]"], "Any")
  , (`Zempic.Fuse.range, "zRange", ["ZNat"], "[Any]")
  , (`Zempic.Fuse.range._redArg, "zRange", ["ZNat"], "[Any]")
  , (`Zempic.Fuse.length._redArg, "zLength", ["[Any]"], "ZNat")
  , (`Zempic.Fuse.sum, "zSum", ["[Any]"], "ZNat")
  , (`Zempic.Fuse.take._redArg, "zTake", ["ZNat", "[Any]"], "[Any]")
  , (`Zempic.Fuse.append._redArg, "zAppend", ["[Any]", "[Any]"], "[Any]")
  , (`Zempic.Fuse.foldr._redArg, "zFoldr", ["Any -> Any -> Any", "Any", "[Any]"], "Any")
  , (`Zempic.Fuse.any._redArg, "zAny", ["Any -> Any", "[Any]"], "Bool")
  , (`Zempic.Fuse.all._redArg, "zAll", ["Any -> Any", "[Any]"], "Bool")
  , (`Zempic.Fuse.zip._redArg, "zZip", ["[Any]", "[Any]"], "[Any]")
  , (`Prod.mk, "zPair", ["Any", "Any", "Any", "Any"], "(Any, Any)")
  , (`Array.mkEmpty, "arrMkEmpty", ["Any", "ZNat"], "Any")
  , (`Array.emptyWithCapacity, "arrMkEmpty", ["Any", "ZNat"], "Any")
  , (`Array.replicate, "arrReplicate", ["Any", "ZNat", "Any"], "Any")
  , (`Array.range, "arrRange", ["ZNat"], "Any")
  , (`Zempic.pushUget, "arrPushUget", ["Any", "Any", "Any", "Word"], "Any")
  , (`Zempic.pushGetI, "arrPushGetI", ["Any", "Any", "Any", "ZNat"], "Any")
  , (`Array.size, "arrSize", ["Any", "Any"], "ZNat")
  , (`Array.usize, "arrUSize", ["Any", "Any"], "Word")
  , (`Array.push, "arrPush", ["Any", "Any", "Any"], "Any")
  , (`Array.get!Internal, "arrGetD", ["Any", "Any", "Any", "ZNat"], "Any")
  , (`Array.getInternal, "arrGetI", ["Any", "Any", "ZNat", "Any"], "Any")
  , (`Array.uget, "arrUGet", ["Any", "Any", "Word", "Any"], "Any")
  , (`Array.set!, "arrSet", ["Any", "Any", "ZNat", "Any"], "Any")
  , (`Array.uset, "arrUSet", ["Any", "Any", "Word", "Any", "Any"], "Any")
  , (`Array.swapIfInBounds, "arrSwap", ["Any", "Any", "ZNat", "ZNat"], "Any")
  , (`Array.pop, "arrPop", ["Any", "Any"], "Any")
  , (`String.length, "strLen", ["Any"], "ZNat")
  , (`String.utf8ByteSize, "strBytes", ["Any"], "ZNat")
  , (`String.append, "strAppend", ["Any", "Any"], "Any")
  , (`String.Internal.append, "strAppend", ["Any", "Any"], "Any")
  , (`panicCore, "panicCore", ["Any", "Any", "Any"], "Any")
  , (`String.push, "strPush", ["Any", "Word32"], "Any")
  , (`String.decEq, "strEq", ["Any", "Any"], "Bool")
  , (`String.decidableLT, "strLt", ["Any", "Any"], "Bool")
  , (`String.toList, "strToList", ["Any"], "[Any]")
  , (`String.ofList, "strOfList", ["[Any]"], "Any")
  , (`String.mk, "strOfList", ["[Any]"], "Any")
  , (`Nat.reprFast, "natRepr", ["ZNat"], "Any")
  , (`Nat.repr, "natRepr", ["ZNat"], "Any")
  , (`Array.mk, "arrOfList", ["Any", "[Any]"], "Any")
  , (`List.toArray, "arrOfList", ["Any", "[Any]"], "Any")
  , (`List.toArrayImpl, "arrOfList", ["Any", "[Any]"], "Any")
  , (`Array.toList, "arrToList", ["Any", "Any"], "[Any]")
  , (`Array.swap, "arrSwapP", ["Any", "Any", "ZNat", "ZNat", "Any", "Any"], "Any")
  , (`Char.ofNat, "charOfNat", ["ZNat"], "Word32")
  , (`Char.ofNatAux, "charOfNatAux", ["ZNat", "Any"], "Word32")
  , (`Char.toNat, "u32ToNat", ["Word32"], "ZNat")
  , (`Array.set, "arrSetH", ["Any", "Any", "ZNat", "Any", "Any"], "Any")
  , (`String.get, "strGet", ["Any", "ZNat"], "Word32")
  , (`String.Pos.Raw.get, "strGet", ["Any", "ZNat"], "Word32")
  , (`String.Internal.get, "strGet", ["Any", "ZNat"], "Word32")
  , (`String.next, "strNext", ["Any", "ZNat"], "ZNat")
  , (`String.Pos.Raw.next, "strNext", ["Any", "ZNat"], "ZNat")
  , (`String.Internal.next, "strNext", ["Any", "ZNat"], "ZNat")
  , (`String.prev, "strPrev", ["Any", "ZNat"], "ZNat")
  , (`String.Pos.Raw.prev, "strPrev", ["Any", "ZNat"], "ZNat")
  , (`String.Internal.prev, "strPrev", ["Any", "ZNat"], "ZNat")
  , (`String.atEnd, "strAtEnd", ["Any", "ZNat"], "Bool")
  , (`String.Pos.Raw.atEnd, "strAtEnd", ["Any", "ZNat"], "Bool")
  , (`String.Internal.atEnd, "strAtEnd", ["Any", "ZNat"], "Bool")
  , (`String.extract, "strExtract", ["Any", "ZNat", "ZNat"], "Any")
  , (`String.Pos.Raw.extract, "strExtract", ["Any", "ZNat", "ZNat"], "Any")
  , (`String.Internal.extract, "strExtract", ["Any", "ZNat", "ZNat"], "Any")
  , (`String.pushn, "strPushn", ["Any", "Word32", "ZNat"], "Any")
  , (`String.Internal.pushn, "strPushn", ["Any", "Word32", "ZNat"], "Any")
  , (`String.decodeChar, "strDecodeChar", ["Any", "ZNat", "Any"], "Word32")
  , (`String.Pos.next, "strPosNext", ["Any", "ZNat", "Any"], "ZNat")
  , (`String.getUTF8Byte, "strGetByte", ["Any", "ZNat", "Any"], "Word8")
  , (`String.isEmpty, "strIsEmpty", ["Any"], "Bool")
  , (`String.hash, "strHash", ["Any"], "Word64")
  , (`String.Slice.Pattern.Internal.memcmpStr, "strMemcmp", ["Any", "Any", "ZNat", "ZNat", "ZNat", "Any", "Any"], "Bool")
  , (`String.Pos.set, "strSetAtH", ["Any", "ZNat", "Word32", "Any"], "Any"), (`String.Pos.Raw.set, "strSetAt", ["Any", "ZNat", "Word32"], "Any")
  , (`String.set, "strSetAt", ["Any", "ZNat", "Word32"], "Any")
  , (`String.get!, "strGet", ["Any", "ZNat"], "Word32"), (`String.Pos.Raw.get!, "strGet", ["Any", "ZNat"], "Word32")
  , (`Nat.log2, "natLog2", ["ZNat"], "ZNat"), (`Nat.pred, "natPred", ["ZNat"], "ZNat")
  , (`String.Internal.length, "strLen", ["Any"], "ZNat")
  , (`String.Internal.posOf, "strPosOf", ["Any", "Word32"], "ZNat"), (`String.posOf, "strPosOf", ["Any", "Word32"], "ZNat")
  , (`String.Internal.offsetOfPos, "strOffsetOfPos", ["Any", "ZNat"], "ZNat")
  , (`String.offsetOfPos, "strOffsetOfPos", ["Any", "ZNat"], "ZNat")
  , (`Int.ofNat, "intOfNat", ["ZNat"], "Integer"), (`Int.negSucc, "intNegSucc", ["ZNat"], "Integer")
  , (`Int.add, "intAdd", ["Integer", "Integer"], "Integer"), (`Int.sub, "intSub", ["Integer", "Integer"], "Integer")
  , (`Int.mul, "intMul", ["Integer", "Integer"], "Integer"), (`Int.neg, "intNeg", ["Integer"], "Integer")
  , (`Int.ediv, "intEDiv", ["Integer", "Integer"], "Integer"), (`Int.emod, "intEMod", ["Integer", "Integer"], "Integer")
  , (`Int.div, "intTDiv", ["Integer", "Integer"], "Integer"), (`Int.mod, "intTMod", ["Integer", "Integer"], "Integer")
  , (`Int.tdiv, "intTDiv", ["Integer", "Integer"], "Integer"), (`Int.tmod, "intTMod", ["Integer", "Integer"], "Integer")
  , (`Int.fdiv, "intFDiv", ["Integer", "Integer"], "Integer"), (`Int.fmod, "intFMod", ["Integer", "Integer"], "Integer")
  , (`Int.decEq, "intEq", ["Integer", "Integer"], "Bool"), (`Int.decLt, "intLt", ["Integer", "Integer"], "Bool")
  , (`Int.decLe, "intLe", ["Integer", "Integer"], "Bool")
  , (`Int.natAbs, "intNatAbs", ["Integer"], "ZNat"), (`Int.toNat, "intToNat", ["Integer"], "ZNat")
  , (`Int.pow, "intPow", ["Integer", "ZNat"], "Integer")
  , (`Float.add, "floatAdd", ["Double", "Double"], "Double"), (`Float.sub, "floatSub", ["Double", "Double"], "Double")
  , (`Float.mul, "floatMul", ["Double", "Double"], "Double"), (`Float.div, "floatDiv", ["Double", "Double"], "Double")
  , (`Float.neg, "floatNeg", ["Double"], "Double")
  , (`Float.beq, "floatEq", ["Double", "Double"], "Bool"), (`Float.decLt, "floatLt", ["Double", "Double"], "Bool")
  , (`Float.decLe, "floatLe", ["Double", "Double"], "Bool")
  , (`Float.lt, "floatLt", ["Double", "Double"], "Bool"), (`Float.le, "floatLe", ["Double", "Double"], "Bool")
  , (`Float.sqrt, "floatSqrt", ["Double"], "Double"), (`Float.sin, "floatSin", ["Double"], "Double")
  , (`Float.cos, "floatCos", ["Double"], "Double"), (`Float.tan, "floatTan", ["Double"], "Double")
  , (`Float.exp, "floatExp", ["Double"], "Double"), (`Float.log, "floatLog", ["Double"], "Double")
  , (`Float.log2, "floatLog2", ["Double"], "Double"), (`Float.log10, "floatLog10", ["Double"], "Double")
  , (`Float.exp2, "floatExp2", ["Double"], "Double"), (`Float.abs, "floatAbs", ["Double"], "Double")
  , (`Float.floor, "floatFloor", ["Double"], "Double"), (`Float.ceil, "floatCeil", ["Double"], "Double")
  , (`Float.round, "floatRound", ["Double"], "Double"), (`Float.atan, "floatAtan", ["Double"], "Double")
  , (`Float.asin, "floatAsin", ["Double"], "Double"), (`Float.acos, "floatAcos", ["Double"], "Double")
  , (`Float.sinh, "floatSinh", ["Double"], "Double"), (`Float.cosh, "floatCosh", ["Double"], "Double")
  , (`Float.tanh, "floatTanh", ["Double"], "Double")
  , (`Float.pow, "floatPow", ["Double", "Double"], "Double"), (`Float.atan2, "floatAtan2", ["Double", "Double"], "Double")
  , (`Float.isNaN, "floatIsNaN", ["Double"], "Bool"), (`Float.isInf, "floatIsInf", ["Double"], "Bool")
  , (`Float.isFinite, "floatIsFinite", ["Double"], "Bool")
  , (`Float.ofNat, "floatOfNat", ["ZNat"], "Double"), (`Nat.toFloat, "floatOfNat", ["ZNat"], "Double")
  , (`Float.ofInt, "floatOfInt", ["Integer"], "Double")
  , (`Float.ofScientific, "floatOfSciN", ["ZNat", "Bool", "ZNat"], "Double")
  , (`Float.toUInt8, "floatToU8", ["Double"], "Word8"), (`Float.toUInt16, "floatToU16", ["Double"], "Word16")
  , (`Float.toUInt32, "floatToU32", ["Double"], "Word32"), (`Float.toUInt64, "floatToU64", ["Double"], "Word64")
  , (`Float.toUSize, "floatToUsz", ["Double"], "Word")
  , (`Thunk.mk, "thunkMk", ["Any", "Any"], "Any"), (`Thunk.pure, "thunkPure", ["Any", "Any"], "Any")
  , (`Thunk.get, "thunkGet", ["Any", "Any"], "Any")
  , (`mixHash, "mixHash", ["Word64", "Word64"], "Word64")
  , (`ByteArray.emptyWithCapacity, "baEmpty", ["ZNat"], "Any"), (`ByteArray.mkEmpty, "baEmpty", ["ZNat"], "Any")
  , (`ByteArray.size, "baSize", ["Any"], "ZNat"), (`ByteArray.usize, "baSize", ["Any"], "ZNat")
  , (`ByteArray.push, "baPush", ["Any", "Word8"], "Any")
  , (`ByteArray.get!, "baGet", ["Any", "ZNat"], "Word8"), (`ByteArray.get, "baGetF", ["Any", "ZNat", "Any"], "Word8")
  , (`ByteArray.uget, "baUGet", ["Any", "Word", "Any"], "Word8")
  , (`ByteArray.set!, "baSet", ["Any", "ZNat", "Word8"], "Any"), (`ByteArray.set, "baSet", ["Any", "ZNat", "Word8"], "Any")
  , (`Bool.true, "True", [], "Bool"), (`Bool.false, "False", [], "Bool") ]

/-- Fixed-width integer types: Lean name, runtime prefix, Haskell type. Must match
`tools/gen_runtime.py`. -/
def uintTypes : List (String × String × String) :=
  [("UInt8", "u8", "Word8"), ("UInt16", "u16", "Word16"), ("UInt32", "u32", "Word32"),
   ("UInt64", "u64", "Word64"), ("USize", "usz", "Word")]

/-- The runtime name suffix for converting to the type with prefix `p` (`u8` becomes `U8`). -/
def capPrefix (p : String) : String := p.capitalize

/-- Operations on fixed-width integers, generated from `uintTypes`. -/
def uintPrims : List (Name × String × List String × String) :=
  uintTypes.flatMap fun (L, s, h) =>
    let bin := fun (op : String) (hs : String) => (s!"{L}.{op}".toName, s!"{s}{hs}", [h, h], h)
    let cmp := fun (op : String) (hs : String) => (s!"{L}.{op}".toName, s!"{s}{hs}", [h, h], "Bool")
    [ bin "add" "Add", bin "sub" "Sub", bin "mul" "Mul", bin "div" "Div", bin "mod" "Mod"
    , bin "land" "Land", bin "lor" "Lor", bin "xor" "Xor"
    , bin "shiftLeft" "Shl", bin "shiftRight" "Shr"
    , (s!"{L}.complement".toName, s!"{s}Compl", [h], h), (s!"{L}.neg".toName, s!"{s}Neg", [h], h)
    , cmp "decEq" "Eq", cmp "decLt" "Lt", cmp "decLe" "Le"
    , (s!"{L}.ofNat".toName, s!"{s}OfNat", ["ZNat"], h)
    , (s!"{L}.ofNatLT".toName, s!"{s}OfNatLT", ["ZNat", "Any"], h)
    , (s!"Nat.to{L}".toName, s!"{s}OfNat", ["ZNat"], h)
    , (s!"{L}.toNat".toName, s!"{s}ToNat", [h], "ZNat") ] ++
    (uintTypes.filter (·.2.1 != s)).map fun (L2, s2, h2) =>
      (s!"{L}.to{L2}".toName, s!"{s}To{capPrefix s2}", [h], h2)

/-- Types with a builtin runtime representation; building or matching them is not supported yet. -/
def builtinTypes : List Name :=
  [`Nat, `Int, `String, `Array, `ByteArray, `FloatArray, `UInt8, `UInt16, `UInt32, `UInt64,
   `USize, `Char, `Float, `Thunk, `Task]

/-! ## Emitter state -/

/-- A function whose array is resolved to its raw buffer once (see "Hoisted buffers" in `Zempic.Arr`):
parameter `kidx` holds the array, either as the parameter itself or inside nested loop-state cells
(`MProd`, `Prod`) at the field `path` (`cells` names the cell type at each step); `kind` is the buffer kind
(`"8"`, `"16"`, `"32"`, `"64"`, `"W"` for a `Word` buffer, `"Bool"`), `sfx` the suffix the ordinary array
primitives get at this element type (`""` for `Bool`), `hty` the Haskell element type of the raw buffer, and
`amap` every variable of the function that is that array or a cell holding it, with the path to the array
inside it (`[]` for the array itself). -/
structure Hoist where
  kidx : Nat
  path : List Nat
  cells : List Name
  kind : String
  sfx : String
  hty : String
  amap : Std.HashMap FVarId (List Nat)
  deriving Inhabited

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
  /-- The Lean type of each variable, to recover the type arguments of generic data. -/
  exprTys : Std.HashMap FVarId Expr := {}
  /-- Word-sized Nat: literals above 2^64 - 1 must raise `ZOverflow`. -/
  fast : Bool := false
  /-- Let bindings whose array operation the ownership analysis proved may update in place. -/
  destr : Std.HashSet (Name × FVarId) := {}
  /-- Call arguments to wrap in a lazy copy (`Own.Sums.shares`). -/
  shares : Std.HashSet (Name × FVarId × Nat) := {}
  /-- The function being printed (variable ids repeat across functions). -/
  cur : Name := Name.anonymous
  /-- Fresh arrays whose uses disagree about the element type (Lean's CSE merged two `Array.mkEmpty`
  calls of different element types): they get a boxed buffer. -/
  mixedArrs : Std.HashSet FVarId := {}
  /-- Variables known to be this `Nat` literal in the function being printed. -/
  known : Std.HashMap FVarId Nat := {}
  /-- Variables known to be this `Bool` (a comparison of known numbers). -/
  knownB : Std.HashMap FVarId Bool := {}
  /-- Largest literal counter a recursive call is specialized on; 0 turns specializing off. -/
  unrollMax : Nat := 16
  /-- Specialized copies of recursive functions still to print: function and, per parameter, the
  literal it is fixed to. -/
  vqueue : Array (Name × Array (Option Nat)) := #[]
  /-- Names of the specialized copies ever queued. -/
  vseen : Std.HashSet String := {}
  /-- How many copies each function has, to bound code growth. -/
  vcount : Std.HashMap Name Nat := {}
  /-- Unboxed array buffers are on (`zempic.typedArrays`). -/
  typedArrays : Bool := true
  /-- Array reads whose value is later used as a `Word`: read without a box. -/
  wordGets : Std.HashSet FVarId := {}
  /-- Set while printing the hoisted worker of a function (see `hoistPlan`). -/
  hoist : Option Hoist := none

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

/-- The Haskell type for `Nat` and `Bool`, and `Any` for everything else. Pure, so the auto-mode
wrapper can use it; the emitter proper uses `hsTyM`, which also types user inductives. -/
def basicTy : Expr → String
  | .const `Nat _ => "ZNat"
  | .const `Bool _ => "Bool"
  | _ => "Any"

/-- The Haskell name of a variable. -/
def lookup (id : FVarId) : EmitM String := do
  match (← get).names[id]? with
  | some n => return n
  | none => unsupported s!"unbound variable {id.name}"; return "undefined"

/-- The Haskell type recorded for a variable (`Any` if unknown). -/
def tyOf (id : FVarId) : EmitM String := do
  return (← get).tys[id]?.getD "Any"

/-- The component types of a Haskell pair type `(A, B)`; `Any` for both when `t` is not a pair type
(a value of unknown type, which has the layout of a pair of `Any`). -/
def pairTys (t : String) : String × String := Id.run do
  if !(t.startsWith "(" && t.endsWith ")") then return ("Any", "Any")
  let cs := ((t.drop 1).dropEnd 1).toString.toList
  let mut depth := 0
  let mut i := 0
  for c in cs do
    if c == '(' then depth := depth + 1
    else if c == ')' then depth := depth - 1
    else if c == ',' && depth == 0 then
      let a := String.ofList (cs.take i)
      let b := String.ofList (cs.drop (i + 1))
      return (a.trimAscii.toString, b.trimAscii.toString)
    i := i + 1
  return ("Any", "Any")

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
   `Zempic.Fuse.range, `Zempic.Fuse.range._redArg, `Zempic.Fuse.take, `Zempic.Fuse.take._redArg,
   `Zempic.Fuse.append, `Zempic.Fuse.append._redArg, `Zempic.Fuse.zip, `Zempic.Fuse.zip._redArg]

/-- Remember that the `data` type for `t` must be generated (builtin types are rejected). -/
def noteType (t : Name) : EmitM Unit := do
  if t == `Bool || t == `List || t == `Prod then return
  if builtinTypes.contains t then unsupported s!"builtin type {t}"; return
  modify fun s => if s.types.contains t then s else { s with types := s.types.push t }

/-- Is the inductive type `v` a proposition? Its values are proofs and carry no data. -/
def isPropInduct (v : InductiveVal) : Bool :=
  match v.type.getForallBody with
  | .sort .zero => true
  | _ => false

/-- Remember the Lean type of a variable. -/
def noteExpr (id : FVarId) (e : Expr) : EmitM Unit :=
  modify fun s => { s with exprTys := s.exprTys.insert id e }

/-- Which of the first `numParams` parameters of an inductive are types (and so become Haskell
type variables)? Value parameters and higher-kinded ones are not. -/
def typeParamMask (v : InductiveVal) : Array Bool := Id.run do
  let mut ty := v.type
  let mut out : Array Bool := #[]
  for _ in [0:v.numParams] do
    match ty with
    | .forallE _ dom body _ =>
      out := out.push (match dom with | .sort _ => true | _ => false)
      ty := body
    | _ => out := out.push false
  return out

/-- Parenthesize a type that is an application, so it can be an argument. -/
def paren (t : String) : String := if t.contains ' ' then s!"({t})" else t

mutual
/-- Haskell type for a Lean type. `Nat` and `Bool` are `ZNat` and `Bool`; a user inductive is its
generated `data` type applied to the Haskell types of its type arguments (noted so that it gets
declared); lists, pairs, functions, builtin types and everything else are `Any`. `env` gives the
Haskell type of each enclosing bound variable, innermost first. -/
partial def hsTyWith (env : List String) (e : Expr) : EmitM String := do
  match e.getAppFn with
  | .bvar i => return env.getD i "Any"
  | .const `Nat _ => return "ZNat"
  | .const `Bool _ => return "Bool"
  | .const `Char _ => return "Word32"
  | .const `Int _ => return "Integer"
  | .const `Float _ => return "Double"
  | .const n _ =>
    if let some (_, _, h) := uintTypes.find? (·.1.toName == n) then return h
    if n == `Prod then
      -- A pair is a Haskell pair of its components' types. It has the layout of a pair of `Any`s (a
      -- component is a pointer to its value either way), so the two are interchangeable by a free cast;
      -- the typed one lets GHC return the components unboxed from a function that builds a pair.
      let args := e.getAppArgs
      if args.size == 2 then
        return s!"({← hsTyWith env args[0]!}, {← hsTyWith env args[1]!})"
      return "Any"
    if n == `List || builtinTypes.contains n then return "Any"
    match (← getEnv).find? n with
    | some (.inductInfo v) =>
      if isPropInduct v then return "Any"
      let mask := typeParamMask v
      let args := e.getAppArgs
      let mut ts : Array String := #[]
      let mut raw : Array String := #[]
      for k in [0:v.numParams] do
        if mask[k]! then
          let t ← match args[k]? with
            | some a => hsTyWith env a
            | none => pure "Any"
          ts := ts.push (paren t)
          raw := raw.push t
      -- Lean stores a structure with one relevant field as that field (`String.Pos` is a `Nat`);
      -- values built by the compiled code are the bare field, so the type must be too.
      if let some info ← liftM (m := CoreM) (hasTrivialStructure? n) then
        return (← ctorFieldTys info.ctorName raw).getD info.fieldIdx "Any"
      noteType n
      return if ts.isEmpty then typeName n else typeName n ++ " " ++ " ".intercalate ts.toList
    | some (.defnInfo d) =>
      -- A type alias (`abbrev Byte := UInt8`) has the layout of what it abbreviates.
      if getReducibilityStatusCore (← getEnv) n == .reducible then
        let body := (d.value.instantiateLevelParams d.levelParams e.getAppFn.constLevels!).beta e.getAppArgs
        hsTyWith env body
      else return "Any"
    | _ => return "Any"
  | _ => return "Any"

/-- Haskell types of the fields of constructor `c`, read from its signature. `targs` are the
Haskell types of the inductive's type parameters (a missing one is `Any`). -/
partial def ctorFieldTys (c : Name) (targs : Array String := #[]) : EmitM (List String) := do
  let some (.ctorInfo v) := (← getEnv).find? c | return []
  let some (.inductInfo iv) := (← getEnv).find? v.induct | return []
  let mask := typeParamMask iv
  let mut ty := v.type
  let mut env : List String := []
  let mut out : Array String := #[]
  let mut i := 0
  let mut ti := 0
  repeat
    match ty with
    | .forallE _ dom body _ =>
      if i < v.numParams then
        if mask[i]! then
          env := targs.getD ti "Any" :: env
          ti := ti + 1
        else env := "Any" :: env
      else
        out := out.push (← hsTyWith env dom)
        env := "Any" :: env
      i := i + 1
      ty := body
    | _ => break
  return out.toList
end

/-- `hsTyWith` outside any binder. -/
def hsTyM (e : Expr) : EmitM String := hsTyWith [] e

/-- The Haskell types of the type arguments of `e`, an application of inductive `ind`; empty when
`e` is something else (the fields then default to `Any`, which has the same layout). -/
def typeArgsOf (e : Expr) (ind : Name) : EmitM (Array String) := do
  match e.getAppFn, (← getEnv).find? ind with
  | .const n _, some (.inductInfo v) =>
    if n != ind then return #[]
    let mask := typeParamMask v
    let args := e.getAppArgs
    let mut out : Array String := #[]
    for k in [0:v.numParams] do
      if mask[k]! then
        out := out.push (← match args[k]? with
          | some a => hsTyWith [] a
          | none => pure "Any")
    return out
  | _, _ => return #[]

/-- The type `ind` applied to `Any` for every type parameter: how a value of unknown type
arguments is typed. -/
def genericTy (ind : Name) : EmitM String := do
  noteType ind
  match (← getEnv).find? ind with
  | some (.inductInfo v) =>
    let k := (typeParamMask v).foldl (fun n b => if b then n + 1 else n) 0
    return " ".intercalate (typeName ind :: List.replicate k "Any")
  | _ => return typeName ind

/-- The Haskell type of `e` as a value of inductive `ind`, falling back to the generic type. -/
def instTy (e : Expr) (ind : Name) : EmitM String := do
  match e.getAppFn with
  | .const n _ => if n == ind then hsTyWith [] e else genericTy ind
  | _ => genericTy ind

/-- Bind a parameter at its mapped type. -/
def bindP (p : Param .pure) : EmitM String := do
  noteExpr p.fvarId p.type
  bindT p.fvarId p.binderName (← hsTyM p.type)

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
  /-- A constructor: its Haskell name, field types, type, and (dropped) parameter count. -/
  | ctor (hs : String) (ptys : List String) (ret : String) (numParams : Nat)
  /-- A function compiled from Lean. -/
  | decl (hs : String) (ptys : List String) (ret : String)
  /-- Not supported; already recorded as such. -/
  | bad

/-- Result type of a declaration as `Nat`/`Bool`/`Any`, for the wrapper. -/
def declRetBasic (d : Decl .pure) : String :=
  basicTy (d.type.getForallBodyMaxDepth d.params.size)

/-- Haskell result type of a declaration, read from its Lean type. -/
def declRetM (d : Decl .pure) : EmitM String :=
  hsTyM (d.type.getForallBodyMaxDepth d.params.size)

/-- Decide how constant `c` is called: runtime primitive, constructor, compiled function or
unsupported. -/
def resolve (c : Name) (ty : Expr) : EmitM Head := do
  if let some (_, hs, ptys, ret) := (prims ++ uintPrims).find? (·.1 == c) then
    return .prim hs ptys ret
  match (← getEnv).find? c with
  | some (.ctorInfo v) =>
    noteType v.induct
    let targs ← typeArgsOf ty v.induct
    return .ctor (ctorName c) (← ctorFieldTys c targs) (← instTy ty v.induct) v.numParams
  | _ =>
    match ← monoDecl? c with
    | some d =>
      match d.value with
      | .code _ =>
        request c
        let ptys ← d.params.toList.mapM (hsTyM ·.type)
        return .decl (fnName c) ptys (← declRetM d)
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
    let sat := if ctor || ret != "Any" then s!"(zo ({sat}))" else s!"({sat})"
    let rest := args.extract arity args.size
    (rest.foldl (fun acc a => s!"(zap {acc} {coerce a.1 a.2 "Any"})") sat, "Any")

/-- The constructor and field types of a single-constructor structure, or `none`. -/
def single (t : Name) (targs : Array String := #[]) : EmitM (Option (Name × List String)) := do
  noteType t
  match (← getEnv).find? t with
  | some (.inductInfo v) =>
    match v.ctors with
    | [c] => return some (c, ← ctorFieldTys c targs)
    | _ => return none
  | _ => return none

/-- Indentation of `n` levels. -/
def pad (n : Nat) : String := "".pushn ' ' (2 * n)

/-! ## Haskell printer -/

/-- An argument with its Haskell name and type. -/
def atomT : Arg .pure → EmitM (String × String)
  | .fvar id => return (← lookup id, ← tyOf id)
  | _ => return ("erased", "Any")

/-- Does the code call constant `n`? -/
partial def callsConst (n : Name) : Code .pure → Bool
  | .let d k => (match d.value with | .const c _ _ => c == n | _ => false) || callsConst n k
  | .fun d k => callsConst n d.value || callsConst n k
  | .jp d k => callsConst n d.value || callsConst n k
  | .cases cs => cs.alts.any fun
    | .alt _ _ k => callsConst n k
    | .default k => callsConst n k
  | _ => false

/-- How many times the code calls constant `n`. -/
partial def countCallsTo (n : Name) : Code .pure → Nat
  | .let d k => (match d.value with | .const c _ _ => if c == n then 1 else 0 | _ => 0) + countCallsTo n k
  | .fun d k => countCallsTo n d.value + countCallsTo n k
  | .jp d k => countCallsTo n d.value + countCallsTo n k
  | .cases cs => cs.alts.foldl (fun a alt => a + match alt with
      | .alt _ _ k => countCallsTo n k
      | .default k => countCallsTo n k) 0
  | _ => 0

/-- Largest estimated size of an unrolled chain: GHC inlines each copy into the next, so a body with `c`
recursive call sites unrolled `k` deep becomes about `size * c^k`. Without this bound a loop with two
branches and a counter of 16 made GHC run out of memory compiling the result. -/
def unrollChainBudget : Nat := 8000

/-- Number of bindings in the code, and the constants it calls. -/
partial def sizeCalls (c : Code .pure) (acc : Nat × Array Name) : Nat × Array Name :=
  match c with
  | .let d k =>
    let acc := (acc.1 + 1, match d.value with
      | .const n _ _ => if acc.2.contains n then acc.2 else acc.2.push n
      | _ => acc.2)
    sizeCalls k acc
  | .fun d k => sizeCalls k (sizeCalls d.value (acc.1 + 1, acc.2))
  | .jp d k => sizeCalls k (sizeCalls d.value (acc.1 + 1, acc.2))
  | .cases cs => cs.alts.foldl (fun a alt => match alt with
      | .alt _ _ k => sizeCalls k (a.1 + 1, a.2)
      | .default k => sizeCalls k (a.1 + 1, a.2)) acc
  | _ => acc

/-- Size of function `c` with everything it calls that we compile, to depth 3: GHC inlines small
callees into an unrolled copy, so the copy's real size is theirs too. -/
partial def deepSize (c : Name) (depth : Nat) (seen : Array Name) : EmitM (Nat × Array Name) := do
  if seen.contains c || depth == 0 then return (0, seen)
  let seen := seen.push c
  let some d ← monoDecl? c | return (0, seen)
  let .code body := d.value | return (0, seen)
  let (n, calls) := sizeCalls body (0, #[])
  let mut total := n
  let mut seen := seen
  for k in calls do
    let (m, s') ← deepSize k (depth - 1) seen
    total := total + m
    seen := s'
  return (total, seen)

/-- Most bindings (counting what it calls) a function may have to be unrolled: bigger bodies
would multiply into code GHC cannot compile in reasonable time. -/
def unrollBudget : Nat := 60

/-- Haskell name of the copy of `c` with its parameters fixed to `ks` (`none`: left free). -/
def variantName (c : Name) (ks : Array (Option Nat)) : String :=
  fnName c ++ "_u" ++ "_".intercalate (ks.toList.map fun | some v => toString v | none => "x")

/-- Remember the value of a `let` when it is a literal or arithmetic or a comparison of known
numbers. In word mode a value of 2^64 or more is left unknown, so it still raises `ZOverflow`. -/
def noteKnown (d : LetDecl .pure) : EmitM Unit := do
  let s ← get
  let lim := if s.fast then 2 ^ 64 else 2 ^ 128
  let kn (a : Arg .pure) : Option Nat := match a with | .fvar f => s.known[f]? | _ => none
  match d.value with
  | .lit (.nat n) => if n < lim then modify fun s => { s with known := s.known.insert d.fvarId n }
  | .const c _ #[a, b] =>
    let (some x, some y) := (kn a, kn b) | return
    let r? : Option Nat :=
      if c == ``Nat.add then some (x + y) else if c == ``Nat.sub then some (x - y)
      else if c == ``Nat.mul then some (x * y) else none
    if let some r := r? then
      if r < lim then modify fun s => { s with known := s.known.insert d.fvarId r }
    let b? : Option Bool :=
      if c == ``Nat.decEq || c == ``Nat.beq then some (x == y)
      else if c == ``Nat.decLt || c == ``Nat.blt then some (decide (x < y))
      else if c == ``Nat.decLe || c == ``Nat.ble then some (decide (x ≤ y)) else none
    if let some v := b? then modify fun s => { s with knownB := s.knownB.insert d.fvarId v }
  | _ => pure ()

/-- An argument the ownership analysis passes as a lazy copy of a shared array. -/
def shareArg (letId : FVarId) (j : Nat) (a : String × String) : EmitM (String × String) := do
  let s ← get
  if s.shares.contains (s.cur, letId, j) then
    return (s!"(arrShare {coerce a.1 a.2 "Any"})", "Any")
  return a

/-- A call to a self-recursive function with a small literal for some `Nat` argument becomes a
call to a copy of it with that argument fixed (queued for printing). Its recursive calls are then
calls with smaller literals, so a loop that counts down from a constant unrolls completely and
GHC sees straight-line code, as the C compiler does. Returns the copy's name, the types of the
arguments it still takes, its result type and those arguments. -/
def tryUnroll (c : Name) (letId : FVarId) (args : Array (Arg .pure)) :
    EmitM (Option (String × List String × String × Array (String × String))) := do
  let s ← get
  if s.unrollMax == 0 then return none
  let ks : Array (Option Nat) := args.map fun
    | .fvar f => match s.known[f]? with | some v => if v ≤ s.unrollMax then some v else none | none => none
    | _ => none
  unless ks.any (·.isSome) do return none
  let some d ← monoDecl? c | return none
  let .code body := d.value | return none
  if args.size != d.params.size || !callsConst c body then return none
  let name := variantName c ks
  unless s.vseen.contains name do
    let size := (← deepSize c 3 #[]).1
    if size > unrollBudget then return none
    -- Depth of the chain: the largest literal fixed to a parameter (a loop counts down to zero or up
    -- from it); then the copies GHC will inline into each other number about calls^depth.
    let depth := ks.foldl (fun m o => max m (o.getD 0)) 0
    let calls := countCallsTo c body
    if size * calls ^ depth > unrollChainBudget then return none
    let cnt := s.vcount.getD c 0
    if cnt ≥ 64 then return none
    modify fun s => { s with vseen := s.vseen.insert name, vqueue := s.vqueue.push (c, ks),
                             vcount := s.vcount.insert c (cnt + 1) }
  let tys ← d.params.toList.mapM (hsTyM ·.type)
  let mut ptys : List String := []
  let mut free : Array (String × String) := #[]
  let mut j := 0
  for a in args, k in ks, t in tys do
    if k.isNone then
      ptys := ptys ++ [t]
      free := free.push (← shareArg letId j (← atomT a))
    j := j + 1
  return some (name, ptys, ← declRetM d, free)

/-- The unboxed buffer kind for arrays of this element type (see `Zempic.Arr`): 1 `Word8`, 2 `Word16`,
3 `Word32` (also `Char`), 4 `Word64`, 5 `Word` (`USize`, and `Nat` in word mode), 6 `Bool`; 0 means the
elements stay boxed (any other type, `Nat` in exact mode where it is a `Natural`, or the option is off). -/
def elemKind (elem : Expr) : EmitM Nat := do
  unless (← get).typedArrays do return 0
  match ← hsTyM elem with
  | "Word8" => return 1
  | "Word16" => return 2
  | "Word32" => return 3
  | "Word64" => return 4
  | "Word" => return 5
  | "Bool" => return 6
  | "ZNat" => return (if (← get).fast then 5 else 0)
  | _ => return 0

/-- Is `x` somewhere passed to a primitive that takes a `Word` there (a `Nat` in word mode, or a
`USize`)? Then `x` holds a `Word` whatever type the code gives it. It finds the real element type
of the read in Lean's in-place `Array.map`, where the view as `NonScalar` hides it. -/
partial def usedAsWord (fast : Bool) (x : FVarId) : Code .pure → Bool
  | .let d k =>
    (match d.value with
     | .const c _ args =>
       match (prims ++ uintPrims).find? (·.1 == c) with
       | some (_, _, ptys, _) =>
         args.zipIdx.any fun (a, i) =>
           (match a with | .fvar y => y == x | _ => false) &&
             (let t := ptys.getD i "Any"; t == "Word" || (fast && t == "ZNat"))
       | none => false
     | _ => false) || usedAsWord fast x k
  | .fun d k => usedAsWord fast x d.value || usedAsWord fast x k
  | .jp d k => usedAsWord fast x d.value || usedAsWord fast x k
  | .cases cs => cs.alts.any fun
    | .alt _ _ k => usedAsWord fast x k
    | .default k => usedAsWord fast x k
  | _ => false

/-! ### Hoisted array buffers

A function with an array parameter that the ownership analysis proved unshared, and that inside the function
is only read and updated in place without changing its length, can resolve the array's buffer once instead of
at every access (`Zempic.Arr`, "Hoisted buffers"). `hoistPlan` decides when. The array may be the parameter
itself or lie inside the loop-state cells (`MProd`, `Prod`) that a `for` or `while` loop passes around. The
conditions, all of which must hold:

* the array is `Array e` with `e` a `UInt8/16/32/64`, `Char`, `USize`, `Bool` or (in word mode) `Nat`, and the
  function is not the in-place `Array.map`, whose writes change the buffer's element type;
* every use of the array, and of every variable that is the array or a cell holding it (the parameter; the
  result of each in-place update; the fields of a cell that is taken apart; a cell built from such a variable;
  a join point's parameter that every jump fills with such a variable) is a read (`size`, `get`, `uget`,
  `toList`), an in-place update that keeps its length (`swap`, `set`, `uset`) that the analysis marked in
  place, building or taking apart a cell, a jump to a join point whose parameter is then the same kind of
  variable, or a use after which no such variable is used again on that path (passed to another function,
  stored, returned, jumped with). Nothing that changes the node of the array (push, pop, a persistent update,
  a copy) is followed by a raw access;
* at least one update is marked in place (so the analysis proved the array owned at entry), and either the
  function calls itself passing the array in the same place (so there is a loop to speed up) or it reads or
  updates the array in place at three or more places.

The hoisted worker then runs only while the array stays a live buffer, which nothing can change: it is
owned, so no other reference can reroot or copy it, and the worker does not push, pop or hand it on. -/

/-- Position of the array among the Lean arguments of an `Array.*` primitive that hoisting understands. -/
def hoistArrIdx (c : Name) : Option Nat :=
  if c == `Array.get!Internal then some 2
  else if [`Array.size, `Array.usize, `Array.getInternal, `Array.uget, `Array.toList,
           `Array.swapIfInBounds, `Array.swap, `Array.set!, `Array.set, `Array.uset].contains c then some 1
  else none

/-- Primitives that only read the array. -/
def hoistIsRead (c : Name) : Bool :=
  [`Array.size, `Array.usize, `Array.get!Internal, `Array.getInternal, `Array.uget, `Array.toList].contains c

/-- Primitives that update the array in place without changing its length. -/
def hoistIsSet (c : Name) : Bool :=
  [`Array.swapIfInBounds, `Array.swap, `Array.set!, `Array.set, `Array.uset].contains c

/-- The constructors of the loop-state cells that hoisting looks through. Both have two type parameters. -/
def hoistIsCell (c : Name) : Bool := c == `MProd.mk || c == `Prod.mk

/-- What the scan found. -/
structure HScan where
  amap : Std.HashMap FVarId (List Nat) := {}
  /-- For each join point, the path of the array in each parameter (none: not the array or a cell holding it). -/
  jpar : Std.HashMap FVarId (Array (Option (List Nat))) := {}
  ok : Bool := true
  destr : Bool := false
  loops : Bool := false
  raws : Nat := 0

/-- How many of the arguments are the array or a cell holding it? -/
def hoistCount (a : Std.HashMap FVarId (List Nat)) (args : Array (Arg .pure)) : Nat :=
  args.foldl (fun n x => match x with | .fvar y => if a.contains y then n + 1 else n | _ => n) 0

/-- Is the argument at position `i` the array itself, and the only argument that is the array or holds it? -/
def hoistSimple (a : Std.HashMap FVarId (List Nat)) (args : Array (Arg .pure)) (i : Nat) : Bool :=
  hoistCount a args == 1 && (match args[i]? with | some (.fvar y) => a[y]? == some [] | _ => false)

/-- Is the argument at position `i` a variable holding the array at `path`, and the only argument that is the
array or holds it? -/
def hoistSimpleAt (a : Std.HashMap FVarId (List Nat)) (path : List Nat) (args : Array (Arg .pure))
    (i : Nat) : Bool :=
  hoistCount a args == 1 && (match args[i]? with | some (.fvar y) => a[y]? == some path | _ => false)

/-- All the jumps to each join point of `c`, with their arguments. -/
partial def hoistJumps (c : Code .pure) (acc : Std.HashMap FVarId (Array (Array (Arg .pure)))) :
    Std.HashMap FVarId (Array (Array (Arg .pure))) :=
  match c with
  | .let _ k => hoistJumps k acc
  | .fun d k => hoistJumps k (hoistJumps d.value acc)
  | .jp d k => hoistJumps k (hoistJumps d.value acc)
  | .jmp j args => acc.insert j ((acc.getD j #[]).push args)
  | .cases cs => cs.alts.foldl (fun a alt => match alt with
      | .alt _ _ k => hoistJumps k a
      | .default k => hoistJumps k a) acc
  | _ => acc

/-- Record that `x` is the array (or a cell holding it) at `path`. Two different paths for one variable is a
case the scan does not understand. -/
def hoistSet (x : FVarId) (path : List Nat) : StateM HScan Unit :=
  modify fun s => match s.amap[x]? with
    | none => { s with amap := s.amap.insert x path }
    | some q => if q == path then s else { s with ok := false }

/-- First pass: which variables are the array or a cell holding it? (Repeated until nothing new is found.) -/
partial def hoistInfer (f : Name) (destr : Std.HashSet (Name × FVarId))
    (jumps : Std.HashMap FVarId (Array (Array (Arg .pure)))) (c : Code .pure) : StateM HScan Unit := do
  match c with
  | .let d k =>
    let a := (← get).amap
    match d.value with
    | .const g _ args =>
      if hoistCount a args == 0 then pure ()
      else if hoistIsSet g && (hoistArrIdx g).any (hoistSimple a args) && destr.contains (f, d.fvarId) then
        hoistSet d.fvarId []
      else if hoistIsCell g then
        let fields := args.extract 2 args.size
        if hoistCount a fields == 1 then
          for fld in fields, j in [0:fields.size] do
            if let .fvar y := fld then
              if let some q := a[y]? then hoistSet d.fvarId (j :: q)
      else pure ()
    | .proj _ i x =>
      if let some (j :: q) := a[x]? then
        if i == j then hoistSet d.fvarId q
    | _ => pure ()
    hoistInfer f destr jumps k
  | .fun d k =>
    hoistInfer f destr jumps d.value
    hoistInfer f destr jumps k
  | .jp d k =>
    -- A parameter is the array (or a cell holding it) if every jump fills it with that.
    let js := jumps.getD d.fvarId #[]
    let mut pars : Array (Option (List Nat)) := #[]
    for _ in d.params, i in [0:d.params.size] do
      let a := (← get).amap
      let ps := js.map fun args => match args[i]? with
        | some (.fvar y) => a[y]?
        | _ => none
      let first := (ps[0]?).getD none
      let allSame := !ps.isEmpty && first.isSome && ps.all (· == first)
      let par := if allSame then first else none
      pars := pars.push par
      if let some q := par then hoistSet (d.params[i]!).fvarId q
    modify fun s => { s with jpar := s.jpar.insert d.fvarId pars }
    hoistInfer f destr jumps d.value
    hoistInfer f destr jumps k
  | .cases cs =>
    let a := (← get).amap
    for alt in cs.alts do
      match alt with
      | .alt c ps k =>
        if let some (j :: q) := a[cs.discr]? then
          if hoistIsCell c && ps.size == 2 then
            if let some pj := ps[j]? then hoistSet pj.fvarId q
        hoistInfer f destr jumps k
      | .default k => hoistInfer f destr jumps k
  | _ => pure ()

/-- Second pass, with every such variable known: do the uses allow the hoist? `path` is where the array lies in
parameter `kidx`. -/
partial def hoistCheck (f : Name) (kidx : Nat) (path : List Nat) (destr : Std.HashSet (Name × FVarId))
    (jf : Std.HashMap FVarId Own.FVS) (c : Code .pure) : StateM HScan Unit := do
  -- After this point none of the variables may be used: the array was handed on.
  let gone := fun (later : Own.FVS) => do
    let st ← get
    if st.amap.toList.any (fun (x, _) => later.contains x) then modify fun s => { s with ok := false }
  match c with
  | .let d k =>
    let a := (← get).amap
    match d.value with
    | .const g _ args =>
      if hoistCount a args == 0 then pure ()
      else if hoistIsRead g && (hoistArrIdx g).any (hoistSimple a args) then
        modify fun s => { s with raws := s.raws + 1 }
      else if hoistIsSet g && (hoistArrIdx g).any (hoistSimple a args) && destr.contains (f, d.fvarId) then
        modify fun s => { s with destr := true, raws := s.raws + 1 }
      else if hoistIsCell g && hoistCount a (args.extract 2 args.size) == 1 then pure ()
      else
        if g == f && hoistSimpleAt a path args kidx then modify fun s => { s with loops := true }
        gone (Own.fvCode jf k)
    | .fvar g args =>
      if a.contains g || hoistCount a args > 0 then gone (Own.fvCode jf k)
    | _ => pure ()
    hoistCheck f kidx path destr jf k
  | .fun d k =>
    let st ← get
    if st.amap.toList.any (fun (x, _) => (Own.fvFun jf d).contains x) then modify fun s => { s with ok := false }
    hoistCheck f kidx path destr jf k
  | .jp d k =>
    hoistCheck f kidx path destr jf d.value
    hoistCheck f kidx path destr jf k
  | .jmp j args =>
    let st ← get
    let pars := st.jpar.getD j #[]
    -- an argument that is the array or holds it must land in a parameter that is the same
    let mut bad := false
    for x in args, i in [0:args.size] do
      if let .fvar y := x then
        if let some q := st.amap[y]? then
          if (pars[i]?).getD none != some q then bad := true
    if bad then gone (jf.getD j {})
  | .cases cs =>
    if (← get).amap[cs.discr]? == some [] then modify fun s => { s with ok := false }
    for alt in cs.alts do
      match alt with
      | .alt _ _ k => hoistCheck f kidx path destr jf k
      | .default k => hoistCheck f kidx path destr jf k
  | _ => pure ()

/-- The buffer kind of an `Array` element type, if the buffer is an unboxed one: the kind name, the suffix of
the ordinary primitives, and the Haskell type of the raw buffer's elements. -/
def hoistKind (e : Expr) : EmitM (Option (String × String × String)) := do
  match ← elemKind e with
  | 1 => return some ("8", "8", "Word8")
  | 2 => return some ("16", "16", "Word16")
  | 3 => return some ("32", "32", "Word32")
  | 4 => return some ("64", "64", "Word64")
  | 5 => return some ("W", "W", "Word")
  | 6 => return some ("Bool", "", "Word8")
  | _ => return none

/-- Where in a parameter of this type an array with an unboxed buffer lies: the path of field indices, the
cell types along it, and the buffer kind. -/
partial def hoistSlots (ty : Expr) : EmitM (List (List Nat × List Name × String × String × String)) := do
  match ty with
  | .app (.const `Array _) e =>
    match ← hoistKind e with
    | some (k, sfx, hty) => return [([], [], k, sfx, hty)]
    | none => return []
  | _ =>
    match ty.getAppFn, ty.getAppArgs with
    | .const c _, #[a, b] =>
      if c == `MProd || c == `Prod then
        let mut out := []
        for (t, j) in [(a, 0), (b, 1)] do
          for (path, cells, k, sfx, hty) in ← hoistSlots t do
            out := out ++ [(j :: path, c :: cells, k, sfx, hty)]
        return out
      else return []
    | _, _ => return []

/-- Is function `d` a loop whose array parameter can be hoisted? (See above.) -/
def hoistPlan (d : Decl .pure) (body : Code .pure) : EmitM (Option Hoist) := do
  if ((← get).cur.toString.splitOn "Array.mapMUnsafe").length > 1 then return none
  let jf := Own.jpFvs body
  let jumps := hoistJumps body {}
  let destr := (← get).destr
  for p in d.params, k in [0:d.params.size] do
    for (path, cells, kind, sfx, hty) in ← hoistSlots p.type do
      -- the first pass is repeated until no new variable turns up
      let mut sc : HScan := { amap := ({} : Std.HashMap FVarId (List Nat)).insert p.fvarId path }
      let mut settled := false
      for _ in [0:64] do
        let n := sc.amap.size
        let (_, sc') := (hoistInfer d.name destr jumps body).run sc
        sc := sc'
        if sc.amap.size == n then
          settled := true
          break
      -- a variable that was not found would be used without being checked: give up if it is not settled
      let (_, sc') := (hoistCheck d.name k path destr jf body).run { sc with ok := sc.ok && settled }
      if sc'.ok && sc'.destr && (sc'.loops || sc'.raws ≥ 3) then
        return some { kidx := k, path, cells, kind, sfx, hty, amap := sc'.amap }
  return none

/-- The array of a hoisted function's parameter `x`, as a Haskell expression of type `Arr`: the parameter
itself, or taken out of the loop-state cells (typed loosely: a cell has the same layout whatever its type
arguments are). -/
def hoistExtract (x : String) (path : List Nat) (cells : List Name) : String :=
  let e := (path.zip cells).foldl (fun acc (i, c) =>
    let ps := (List.range 2).map (s!"p{·}")
    if c == `Prod then s!"(case (zu (zo {acc}) :: (Any, Any)) of \{ (p0, p1) -> p{i} })"
    else s!"(case (zu (zo {acc}) :: {typeName c} Any Any) of \{ {ctorName (c ++ `mk)} {" ".intercalate ps} -> p{i} })") x
  s!"(zu (zo {e}))"

/-- Expression and its Haskell type. -/
def hsLetValue (v : LetValue .pure) (letTy : Expr) (letId : FVarId) : EmitM (String × String) :=
  match v with
  | .lit (.nat n) => do
    if (← get).fast && n ≥ 2 ^ 64 then return ("(overflow :: ZNat)", "ZNat")
    return (s!"({n} :: ZNat)", "ZNat")
  | .lit (.str s) => return (s!"(strLit {hsStr s})", "Any")
  | .lit (.uint8 n) => return (s!"({n} :: Word8)", "Word8")
  | .lit (.uint16 n) => return (s!"({n} :: Word16)", "Word16")
  | .lit (.uint32 n) => return (s!"({n} :: Word32)", "Word32")
  | .lit (.uint64 n) => return (s!"({n} :: Word64)", "Word64")
  | .lit (.usize n) => return (s!"({n} :: Word)", "Word")
  | .erased => return ("erased", "Any")
  | .fvar f args => do
    let f ← useAs f "Any"
    let args ← args.mapM atomT
    return (args.foldl (fun acc a => s!"(zap {acc} {coerce a.1 a.2 "Any"})") f, "Any")
  | .proj `Prod i x => do
    let xt ← tyOf x
    let (t0, t1) := pairTys xt
    let ty := if xt.startsWith "(" then xt else "(Any, Any)"
    let x ← useAs x ty
    return (s!"(case {x} of \{ (p0, p1) -> p{i} })", if i == 0 then t0 else t1)
  | .proj t i x => do
    let (targs, full) ← match (← get).exprTys[x]? with
      | some e => pure (← typeArgsOf e t, ← instTy e t)
      | none => pure (#[], ← genericTy t)
    let x ← useAs x full
    match ← single t targs with
    | some (c, ftys) =>
      let ps := (List.range ftys.length).map (s!"p{·}")
      let pat := s!"{ctorName c} {" ".intercalate ps}"
      return (s!"(case ({x} :: {full}) of \{ {pat} -> p{i} })", ftys.getD i "Any")
    | none => unsupported s!"projection on {t}"; return ("erased", "Any")
  | .const c _ argsRaw => do
    -- A call to the function being printed that hands on the hoisted array: it stays in the hoisted worker.
    let hoist? := (← get).hoist
    let cur := (← get).cur
    let selfH := match hoist? with
      | some h => c == cur && hoistSimpleAt h.amap h.path argsRaw h.kidx
      | none => false
    let unrolled ← tryUnroll c letId argsRaw
    if let some (hs, ptys, ret, free) := unrolled then
      -- a copy of the loop fixed to literals: inside a hoisted worker, the copy's worker
      if selfH then
        let h := hoist?.get!
        return apply (hs ++ "_h") (s!"HB {h.hty}" :: ptys) ret (#[("hb", s!"HB {h.hty}")] ++ free) false
      return apply hs ptys ret free false
    let mut args : Array (String × String) := #[]
    let mut j := 0
    for a in argsRaw do
      args := args.push (← shareArg letId j (← atomT a))
      j := j + 1
    match ← resolve c letTy with
    | .prim hs ptys ret =>
      -- A pair is built at the component types of its Lean type.
      let (ptys, ret) ← if hs == "zPair" then
          match letTy.getAppFn, letTy.getAppArgs with
          | .const `Prod _, #[a, b] =>
            let ta ← hsTyM a
            let tb ← hsTyM b
            pure (["Any", "Any", ta, tb], s!"({ta}, {tb})")
          | _, _ => pure (ptys, ret)
        else pure (ptys, ret)
      let elem? : Option Expr := match letTy.getAppFn, letTy.getAppArgs with
        | .const `Array _, #[elem] => some elem
        | _, _ => none
      -- Lean's in-place `Array.map` (`Array.mapMUnsafe`) views an `Array Nat` as `Array NonScalar` and
      -- stores results of any type; the compiler erases `NonScalar` to `Nat`, so the type cannot show
      -- it. It is the only library function that changes an array's element type in place (checked in
      -- Init/Data/Array), so a write inside it makes the buffer boxed first.
      let punned := ((← get).cur.toString.splitOn "Array.mapMUnsafe").length > 1
      let hs := if punned && ["arrSet", "arrSetH", "arrUSet", "arrPush"].contains hs then hs ++ "B" else hs
      -- The analysis proved this array operation may update in place: use the in-place primitive.
      let hs := if (← get).destr.contains ((← get).cur, letId) then hs ++ "U" else hs
      -- An in-place swap on an array of a known word-like element type exchanges in line.
      let swapSfx? ← match hs, elem? with
        | "arrSwapU", some elem | "arrSwapPU", some elem =>
          match ← hsTyM elem with
          | "Word8" => pure (some "8") | "Word16" => pure (some "16") | "Word32" => pure (some "32")
          | "Word64" => pure (some "64") | "Word" => pure (some "W")
          | "ZNat" => pure (if (← get).fast then some "W" else none)
          | _ => pure none
        | _, _ => pure none
      let hs := match swapSfx? with | some sfx => hs ++ sfx | none => hs
      -- A new array of a known numeric element type gets an unboxed buffer.
      let hs ← if hs == "arrMkEmpty" || hs == "arrReplicate" || hs == "arrOfList" then
          match elem? with
          | some elem =>
            let k ← if (← get).mixedArrs.contains letId then pure 0 else elemKind elem
            pure (if k == 0 then hs else s!"{hs}K {k}")
          | none => pure hs
        else pure hs
      -- A new range of naturals gets a word buffer in word mode (and no per-element box).
      let hs ← if hs == "arrRange" then
          pure s!"arrRangeK {← elemKind (.const `Nat [])}"
        else pure hs
      -- An element known to be a `Word` (a `Nat` in word mode, or a `USize`) is read and written
      -- without a box. The type must be the value's own, so a read inside the in-place `Array.map`
      -- (where the view as `NonScalar` hides the real element type) stays boxed.
      let fast := (← get).fast
      let isW := fun (t : String) => t == "Word" || (fast && t == "ZNat")
      let letHs ← hsTyM letTy
      let isWordGet := (← get).wordGets.contains letId
      let valT := fun (k : Nat) => (args[k]?).map (·.2)
      let valW := fun (k : Nat) => match args[k]? with | some a => isW a.2 | none => false
      let setW := ["arrPushU", "arrSetU", "arrUSetU", "arrUSetBU"]
      -- `get!` hands over its default as a `Word` too, so it is not boxed at every read.
      let getPtys := fun (h : String) (ps : List String) =>
        if h == "arrGetD" then ps.set 1 (if fast then "ZNat" else "Word") else ps
      -- An element of a narrow integer type (`UInt8/16/32/64`, `Char`) is read and written in line from a
      -- buffer of its own kind, again with no box. Not inside the in-place `Array.map` (a pun).
      let narrow? : Option String := match letHs with
        | "Word8" => some "8" | "Word16" => some "16" | "Word32" => some "32" | "Word64" => some "64"
        | _ => none
      let narrowOf := fun (t : String) => match t with
        | "Word8" => some "8" | "Word16" => some "16" | "Word32" => some "32" | "Word64" => some "64"
        | _ => (none : Option String)
      let narrowSet := ["arrPushU", "arrSetU", "arrUSetU"]
      let narrowK := if hs.startsWith "arrPush" then 2 else 3
      let narrowV : Option String := (valT narrowK).bind narrowOf
      let (hs, ptys, ret) :=
        if ["arrGetD", "arrGetI", "arrUGet"].contains hs && !punned && narrow?.isSome then
          (hs ++ narrow?.get!, (if hs == "arrGetD" then ptys.set 1 letHs else ptys), letHs)
        else if narrowSet.contains hs && !punned && narrowV.isSome then
          (hs ++ narrowV.get!, ptys.set narrowK (valT narrowK).get!, ret)
        else if ["arrGetD", "arrGetI", "arrUGet"].contains hs && !punned && isW letHs then
          (hs ++ "W", getPtys hs ptys, letHs)
        else if ["arrGetD", "arrGetI", "arrUGet"].contains hs && isWordGet then
          (hs ++ "W", getPtys hs ptys, if fast then "ZNat" else "Word")
        else if setW.contains hs && valW (if hs.startsWith "arrPush" then 2 else 3) then
          let k := if hs.startsWith "arrPush" then 2 else 3
          (hs ++ "W", ptys.set k (args[k]!).2, ret)
        else (hs, ptys, ret)
      -- Inside a hoisted worker the array's accesses go to the raw buffer.
      if let some h := (← get).hoist then
        if let some i := hoistArrIdx c then
          let base? := ["arrGetD", "arrGetI", "arrUGet", "arrSetU", "arrUSetU", "arrSwapU", "arrSwapPU"].find?
            (fun b => hs == b ++ h.sfx)
          if let some b := base? then
           if (match argsRaw[i]? with | some (.fvar y) => h.amap[y]? == some [] | _ => false) then
            return apply (b ++ h.kind ++ "H") (s!"HB {h.hty}" :: ptys) ret (#[("hb", s!"HB {h.hty}")] ++ args) false
      return apply hs ptys ret args false
    | .decl hs ptys ret =>
      if selfH then
        let h := (← get).hoist.get!
        return apply (hs ++ "_h") (s!"HB {h.hty}" :: ptys) ret (#[("hb", s!"HB {h.hty}")] ++ args) false
      else return apply hs ptys ret args false
    | .ctor hs ptys ret np => return apply hs ptys ret (args.extract np args.size) false
    | .bad => return ("erased", "Any")

/-- How many times variable `x` is used in the code (any use counts; unknown forms count as many). -/
partial def useCount (x : FVarId) : Code .pure → Nat
  | .let d k =>
    (match d.value with
     | .const _ _ args => Own.occurrences args x
     | .fvar f args => (if f == x then 1 else 0) + Own.occurrences args x
     | .proj _ _ f => if f == x then 1 else 0
     | .lit _ => 0
     | .erased => 0) + useCount x k
  | .fun d k => useCount x d.value + useCount x k
  | .jp d k => useCount x d.value + useCount x k
  | .jmp _ args => Own.occurrences args x
  | .return y => if y == x then 1 else 0
  | .cases cs => (if cs.discr == x then 1 else 0) + cs.alts.foldl (fun a alt => a + match alt with
      | .alt _ _ k => useCount x k
      | .default k => useCount x k) 0
  | .unreach _ => 0

/-- Is the only use of `x` in the code an `Array.uset` of index `i` on it? Then a write of `x`'s
slot `i` just before is dead: nothing can read it. -/
partial def onlyOverwrittenAt (x i : FVarId) : Code .pure → Bool
  | .let d k =>
    (match d.value with
     | .const `Array.uset _ #[_, .fvar a, .fvar j, _, _] => a == x && j == i
     | _ => false) || onlyOverwrittenAt x i k
  | .fun _ k => onlyOverwrittenAt x i k
  | .jp _ k => onlyOverwrittenAt x i k
  | .cases cs => cs.alts.any fun
    | .alt _ _ k => onlyOverwrittenAt x i k
    | .default k => onlyOverwrittenAt x i k
  | _ => false

/-- The element kinds (see `elemKind`) that the code demands of array variable `x`, from the type
argument of an `Array.*` primitive that takes it and from the parameter type of a function it is
passed to. A use whose element type is erased, unknown or the `NonScalar` pun of the in-place
`Array.map` says nothing and is skipped. -/
partial def useKinds (x : FVarId) : Code .pure → EmitM (List Nat)
  | .let d k => do
    let here : List Nat ← match d.value with
      | .const c _ args => do
        let mut out : List Nat := []
        let isEl := fun (e : Expr) => !e.isErased && !(e.isConstOf `Zempic.NonScalar) && !(e.isConstOf `NonScalar)
        for a in args, i in [0:args.size] do
          if let .fvar y := a then
            if y == x then
              if c.getPrefix == `Array then
                if let some (Arg.type e _) := args[0]? then
                  if isEl e then out := (← elemKind e) :: out
              else if let some cd ← monoDecl? c then
                if let some prm := cd.params[i]? then
                  if let .app (.const `Array _) e := prm.type then
                    if isEl e then out := (← elemKind e) :: out
        pure out
      | _ => pure []
    return here ++ (← useKinds x k)
  | .fun d k => return (← useKinds x d.value) ++ (← useKinds x k)
  | .jp d k => return (← useKinds x d.value) ++ (← useKinds x k)
  | .cases cs => do
    let mut out : List Nat := []
    for alt in cs.alts do
      match alt with
      | .alt _ _ k => out := out ++ (← useKinds x k)
      | .default k => out := out ++ (← useKinds x k)
    return out
  | _ => return []


mutual
/-- Print LCNF code as a Haskell expression whose result has type `ret`. -/
partial def hsCode (c : Code .pure) (ind : Nat) (ret : String) : EmitM String := do
  match c with
  | .let d k =>
    -- A placeholder write that the loop overwrites at once (`Array.map`) is skipped: the array passes through.
    let d := match d.value with
      | .const `Array.uset _ #[_, .fvar a, .fvar i, _, _] =>
        if useCount d.fvarId k == 1 && onlyOverwrittenAt d.fvarId i k then { d with value := .fvar a #[] } else d
      | _ => d
    match d.value with
    | .const c _ _ =>
      if [`Array.uget, `Array.getInternal, `Array.get!Internal].contains c then
        -- Variables are unique only within a function, so the mark is set or cleared at every read.
        let w := usedAsWord (← get).fast d.fvarId k
        modify fun s => { s with wordGets := if w then s.wordGets.insert d.fvarId
                                              else s.wordGets.erase d.fvarId }
    | _ => pure ()
    -- An element read whose only use is to be pushed (in place) on another array is moved in one
    -- step.
    let st ← get
    let (d, k) := match d.value, k with
      | .const g gu #[_, .fvar src, idx, _], .let d2 k2 =>
        match d2.value with
        | .const `Array.push _ #[t, .fvar arr, .fvar v] =>
          if (g == `Array.uget || g == `Array.getInternal) && v == d.fvarId && arr != d.fvarId
              && src != arr && useCount d.fvarId k2 == 0
              && st.destr.contains (st.cur, d2.fvarId) then
            let fused := if g == `Array.uget then `Zempic.pushUget else `Zempic.pushGetI
            let newArgs : Array (Arg .pure) := #[t, .fvar arr, .fvar src, idx]
            ({ d2 with value := .const fused gu newArgs }, k2)
          else (d, k)
        | _ => (d, k)
      | _, _ => (d, k)
    -- Lean's CSE merges `Array.mkEmpty` calls of different element types into one variable, and the
    -- type on the `let` is only the first one's. Pick an unboxed buffer only if every use agrees.
    match d.value with
    | .const c _ _ =>
      if [`Array.mkEmpty, `Array.emptyWithCapacity, `Array.replicate, `List.toArray, `List.toArrayImpl, `Array.mk].contains c then
        let ks ← useKinds d.fvarId k
        let want ← match d.type.getAppFn, d.type.getAppArgs with
          | .const `Array _, #[elem] => elemKind elem
          | _, _ => pure 0
        if ks.any (· != want) then modify fun s => { s with mixedArrs := s.mixedArrs.insert d.fvarId }
    | _ => pure ()
    let (rhs, ty) ← hsLetValue d.value d.type d.fvarId
    noteExpr d.fvarId d.type
    let x ← bindT d.fvarId d.binderName ty
    noteKnown d
    let lazy := match d.value with | .const c _ _ => fuseProducers.contains c | _ => false
    let bang := if lazy then "" else "!"
    return s!"let \{ {bang}{x} = {rhs} } in\n{pad ind}{← hsCode k ind ret}"
  | .fun d k =>
    for p in d.params do noteExpr p.fvarId p.type
    let ps ← d.params.mapM fun p => bind p.fvarId p.binderName
    let f ← bind d.fvarId d.binderName
    let body ← hsCode d.value (ind + 2) "Any"
    let lam := " ".intercalate ps.toList
    let rest ← hsCode k ind ret
    return s!"let \{ {f} = zo (\\{lam} ->\n{pad (ind + 2)}{body}) } in\n{pad ind}{rest}"
  | .jp d k =>
    let tys ← d.params.toList.mapM (hsTyM ·.type)
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
    -- A test of known numbers has one possible answer: print only that branch.
    if cs.typeName == `Bool then
      if let some b := (← get).knownB[cs.discr]? then
        let want := if b then `Bool.true else `Bool.false
        let mut pick : Option (Code .pure) := none
        for a in cs.alts do
          match a with
          | .alt n _ k => if n == want then pick := some k
          | .default k => if pick.isNone then pick := some k
        if let some k := pick then return ← hsCode k ind ret
    if cs.typeName == `Int then
      -- Int is an Integer: `ofNat n` for non-negative values, `negSucc n` (= -n-1) otherwise.
      let x ← useAs cs.discr "Integer"
      let mut pos : Option String := none
      let mut neg : Option String := none
      let mut dflt : Option String := none
      for a in cs.alts do
        match a with
        | .alt n ps k =>
          let v ← bindT ps[0]!.fvarId ps[0]!.binderName "ZNat"
          let body ← hsCode k (ind + 2) ret
          if n == `Int.ofNat then pos := some s!"let \{ !{v} = intToNat {x} } in\n{pad (ind + 2)}{body}"
          else neg := some s!"let \{ !{v} = intNatAbs ({x} + 1) } in\n{pad (ind + 2)}{body}"
        | .default k => dflt := some (← hsCode k (ind + 2) ret)
      let p := pos.getD (dflt.getD "error \"leanzempic: unreachable\"")
      let n := neg.getD (dflt.getD "error \"leanzempic: unreachable\"")
      return s!"if intIsNeg {x}\n{pad (ind + 1)}then {n}\n{pad (ind + 1)}else {p}"
    noteType cs.typeName
    let dty? := (← get).exprTys[cs.discr]?
    let targs ← match dty? with
      | some e => typeArgsOf e cs.typeName
      | none => pure #[]
    let ty ← if cs.typeName == `Bool then pure "Bool"
      else if cs.typeName == `List then pure "[Any]"
      else if cs.typeName == `Prod then
        pure (let t := (← tyOf cs.discr); if t.startsWith "(" then t else "(Any, Any)")
      else match dty? with
        | some e => instTy e cs.typeName
        | none => genericTy cs.typeName
    let x ← useAs cs.discr ty
    let mut alts : Array String := #[]
    for a in cs.alts do
      match a with
      | .alt n ps k =>
        let pat ←
          if n == `Bool.true then pure "True"
          else if n == `Bool.false then pure "False"
          else if n == `Prod.mk then do
            let (t0, t1) := pairTys ty
            noteExpr ps[0]!.fvarId ps[0]!.type
            noteExpr ps[1]!.fvarId ps[1]!.type
            let a ← bindT ps[0]!.fvarId ps[0]!.binderName t0
            let b ← bindT ps[1]!.fvarId ps[1]!.binderName t1
            pure s!"({a}, {b})"
          else if n == `List.nil then pure "[]"
          else if n == `List.cons then do
            let h ← bind ps[0]!.fvarId ps[0]!.binderName
            let t ← bindT ps[1]!.fvarId ps[1]!.binderName "[Any]"
            pure s!"({h} : {t})"
          else do
            let ftys ← ctorFieldTys n targs
            let mut bs : Array String := #[]
            for p in ps, i in [0:ps.size] do
              noteExpr p.fvarId p.type
              bs := bs.push (← bindT p.fvarId p.binderName (ftys.getD i "Any"))
            pure (" ".intercalate (ctorName n :: bs.toList))
        alts := alts.push s!"{pat} ->\n{pad (ind + 2)}{← hsCode k (ind + 2) ret}"
      | .default k => alts := alts.push s!"_ ->\n{pad (ind + 2)}{← hsCode k (ind + 2) ret}"
    let sep := s!";\n{pad (ind + 1)}"
    return s!"case ({x} :: {ty}) of \{\n{pad (ind + 1)}{sep.intercalate alts.toList} }"
end

/-- Print one declaration as a typed Haskell function. -/
def hsDecl (d : Decl .pure) : EmitM String := do
  let .code body := d.value | return ""
  modify fun s => { s with known := {}, knownB := {} }
  let ps ← d.params.mapM bindP
  let n := fnName d.name
  let ret ← declRetM d
  let ptys ← d.params.toList.mapM (hsTyM ·.type)
  let sig := " -> ".intercalate (ptys ++ [ret])
  let text ← hsCode body 1 ret
  let some h ← hoistPlan d body
    | return s!"{n} :: {sig}\n{n} {" ".intercalate ps.toList} =\n{pad 1}{text}\n"
  -- A loop over an unshared array: `n` checks once that the array is a live buffer and runs the worker on
  -- the raw buffer; if it is not, the ordinary code `n_slow` runs one step, and its recursive calls come
  -- back to `n`, which checks again (a lazy handle becomes a live buffer at its first write).
  let hb := s!"HB {h.hty}"
  let args := " ".intercalate ps.toList
  let arr := hoistExtract ps[h.kidx]! h.path h.cells
  modify fun s => { s with hoist := some h }
  let ps2 ← d.params.mapM bindP
  let fast ← hsCode body 1 ret
  modify fun s => { s with hoist := none }
  return s!"{n} :: {sig}\n{n} {args} =\n{pad 1}aHoist{h.kind} {arr} (\\hb -> {n}_h hb {args}) ({n}_slow {args})\n\n" ++
    s!"{n}_slow :: {sig}\n{n}_slow {args} =\n{pad 1}{text}\n\n" ++
    s!"{n}_h :: {hb} -> {sig}\n{n}_h !hb {" ".intercalate (ps2.toList.map ("!" ++ ·))} =\n{pad 1}{fast}\n"

/-- Print the copy of `d` whose parameters `ks` are fixed to literals. It takes only the other
parameters; `INLINE` lets GHC splice the chain of copies of an unrolled loop into straight-line
code. A copy of a loop over an unshared array is hoisted like the loop itself (see `hsDecl`). -/
def hsVariant (d : Decl .pure) (ks : Array (Option Nat)) : EmitM String := do
  let .code body := d.value | return ""
  -- Bind the parameters; the fixed ones become literals, the others the copy's arguments.
  let prepare : EmitM (List String × Array String × String) := do
    modify fun s => { s with known := {}, knownB := {} }
    let ps ← d.params.mapM bindP
    let tys ← d.params.toList.mapM (hsTyM ·.type)
    let mut sig : List String := []
    let mut names : Array String := #[]
    let mut pre := ""
    for p in d.params, k in ks, nm in ps, t in tys do
      match k with
      | some v =>
        -- The fixed parameter is bound below as a `ZNat` whatever its declared type: a polymorphic
        -- parameter is `Any`, and its uses would otherwise skip the cast (`zo`) to `Any`.
        modify fun s => { s with known := s.known.insert p.fvarId v, tys := s.tys.insert p.fvarId "ZNat" }
        pre := pre ++ s!"let \{ !{nm} = ({v} :: ZNat) } in\n{pad 1}"
      | none =>
        sig := sig ++ [t]
        names := names.push nm
    return (sig, names, pre)
  let (sig, names, pre) ← prepare
  let ret ← declRetM d
  let n := variantName d.name ks
  let args := " ".intercalate names.toList
  let text ← hsCode body 1 ret
  let some h ← hoistPlan d body
    | return s!"{n} :: {" -> ".intercalate (sig ++ [ret])}\n{n} {args} =\n{pad 1}{pre}{text}\n\{-# INLINABLE {n} #-}\n"
  let (_, names2, pre2) ← prepare
  modify fun s => { s with hoist := some h }
  let fast ← hsCode body 1 ret
  modify fun s => { s with hoist := none }
  let hb := s!"HB {h.hty}"
  let full := " -> ".intercalate (sig ++ [ret])
  -- the array is one of the copy's arguments (a fixed parameter is a number)
  let mut arrArg : Option String := none
  let mut idx := 0
  for k in ks, i in [0:ks.size] do
    if k.isNone then
      if i == h.kidx then arrArg := names[idx]?
      idx := idx + 1
  let some arrName := arrArg | return s!"{n} :: {full}\n{n} {args} =\n{pad 1}{pre}{text}\n\{-# INLINABLE {n} #-}\n"
  let arr := hoistExtract arrName h.path h.cells
  return s!"{n} :: {full}\n{n} {args} =\n{pad 1}aHoist{h.kind} {arr} (\\hb -> {n}_h hb {args}) ({n}_slow {args})\n\{-# INLINABLE {n} #-}\n\n" ++
    s!"{n}_slow :: {full}\n{n}_slow {args} =\n{pad 1}{pre}{text}\n\n" ++
    s!"{n}_h :: {hb} -> {full}\n{n}_h !hb {" ".intercalate (names2.toList.map ("!" ++ ·))} =\n{pad 1}{pre2}{fast}\n"

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
  /-- The code contains Lean's own list loops (`map`, `filter`, `foldl`, ...) and none of the fusion
  combinators: `zempic.fuse` was off, and turning it on would let GHC fuse them. -/
  fusible : Bool := false

/-- The Haskell `data` declaration for Lean inductive `t`. A generic inductive becomes a
polymorphic Haskell type with strict fields (`data ZT_MProd a0 a1 = ZC_MProd_mk !a0 !a1`), so every
instantiation has the same layout and GHC unboxes the fields wherever the types are known. -/
def dataDecl (t : Name) : EmitM String := do
  match (← getEnv).find? t with
  | some (.inductInfo v) =>
    let k := (typeParamMask v).foldl (fun n b => if b then n + 1 else n) 0
    let tyvars := (List.range k).map (s!"a{·}")
    -- A parameter used by no field would otherwise be kind-generalized, and `T Any` then fails.
    let kinded := tyvars.map (s!"({·} :: Type)")
    let mut cs : Array String := #[]
    for c in v.ctors do
      if let some (.ctorInfo _) := (← getEnv).find? c then
        let fields := (← ctorFieldTys c tyvars.toArray).map (s!"!{paren ·}")
        cs := cs.push (" ".intercalate (ctorName c :: fields))
    let head := " ".intercalate (typeName t :: kinded)
    return s!"data {head} = {" | ".intercalate cs.toList}\n"
  | _ => unsupported s!"type {t}"; return ""

/-- Compile `roots` and everything they reach into one Haskell module plus a Core-notation dump. -/
def emitModule (modName : String) (roots : Array Name) (natMod : String := "Zempic.Nat.Exact")
    (fast : Bool := false) : CoreM Output := do
  let act : EmitM Output := do
    for r in roots do request r
    let mut hs : Array String := #[]
    let mut core : Array String := #[]
    let mut i := 0
    let mut vi := 0
    while i < (← get).queue.size || vi < (← get).vqueue.size do
      if i < (← get).queue.size then
        let n := (← get).queue[i]!
        i := i + 1
        match ← monoDecl? n with
        | some d =>
          modify fun st => { st with cur := n }
          hs := hs.push (← hsDecl d)
          core := core.push (← coreDecl d)
        | none => unsupported s!"constant {n}"
      else
        let (n, ks) := (← get).vqueue[vi]!
        vi := vi + 1
        if let some d ← monoDecl? n then
          modify fun st => { st with cur := n }
          hs := hs.push (← hsVariant d ks)
    -- Declaring a type can mention more types, so go until none are new.
    let mut datas : Array String := #[]
    let mut j := 0
    while j < (← get).types.size do
      datas := datas.push (← dataDecl (← get).types[j]!)
      j := j + 1
    let bad := (← get).unsupported
    unless bad.isEmpty do
      throwError "leanzempic: unsupported in this version:\n  {"\n  ".intercalate bad.toList}"
    -- In-place updates assume GHC never shares two calls that make an array, so forbid the
    -- transformations that would (common subexpression elimination, floating to top level).
    let ownFlags := if (← get).destr.isEmpty && (← get).shares.isEmpty then []
      else ["{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}"]
    -- Strict arguments are passed already evaluated and tagged, so the callee skips its tag test and
    -- enter (const_fold's Word path: 13% fewer instructions retired). But it stops GHC's SpecConstr from
    -- unboxing fixed-width integer arguments in loops (qsort: 15% more), so a module whose function
    -- signatures mention a fixed-width type does not get it.
    let fixedWidth := hs.any fun h => h.splitOn "\n" |>.any fun l =>
      l.startsWith "z_" && (l.splitOn " :: ").length > 1 && (l.splitOn "Word").length > 1
    let cbvFlag := if fixedWidth then [] else ["{-# OPTIONS_GHC -fworker-wrapper-cbv #-}"]
    let header := "\n".intercalate ([
      "{-# LANGUAGE BangPatterns, ScopedTypeVariables, KindSignatures #-}",
      "{-# OPTIONS_GHC -Wno-unused-matches -Wno-unused-imports #-}",
      -- GHC 9.14.1's Float Inwards pass can produce an ill-scoped coercion variable on code full of
      -- casts (found by -dcore-lint; the compiler then panics in StgToCmm). It costs nothing measurable here.
      "{-# OPTIONS_GHC -fno-float-in #-}"] ++ cbvFlag ++ ownFlags ++ [
      "-- Generated by leanzempic. Do not edit.",
      s!"module {modName} where", "",
      "import Zempic.Runtime", s!"import {natMod}", "import Zempic.List", "import Zempic.UInt", "import Zempic.Prims",
      "import Data.Word (Word8, Word16, Word32, Word64)", "import Data.Kind (Type)",
      "import Zempic.Arr (HB, aHoist8, aHoist16, aHoist32, aHoist64, aHoistW, aHoistBool)", "", ""])
    let names := (← get).seen.toList.map (·.toString)
    let listy := ["List.map", "List.filter", "List.foldl", "List.foldr", "List.zip", "List.flatMap"]
    let fusible := names.any (fun n => listy.any fun l => n.startsWith l) && !names.any (·.startsWith "Zempic.Fuse")
    return { haskell := header ++ "\n".intercalate (datas ++ hs).toList
             core := "-- leanzempic Core-notation dump (for reading)\n\n" ++
               "\n".intercalate core.toList
             fusible }
  let own := zempic.own.get (← getOptions)
  let (destr, shares) ← if own then Own.analyze roots else pure ({}, {})
  act.run' { fast, destr, shares, unrollMax := zempic.unroll.get (← getOptions),
             typedArrays := zempic.typedArrays.get (← getOptions) }

/-! ## Core-plugin input (spike): LCNF as an s-expression

The plugin in `plugin/` builds GHC Core from this instead of parsing generated Haskell. Only the
`Nat`/`Bool` subset: lets of literals and calls, `cases` on `Bool`, and returns. -/

/-- A value as an s-expression: `(lit n)`, `(call f args...)` or `(var x)`. -/
def zcValue : LetValue .pure → EmitM String
  | .lit (.nat n) => return s!"(lit {n})"
  | .fvar f #[] => do return s!"(var {← lookup f})"
  | .const c _ args => do
    let args ← args.mapM atom
    match ← resolve c (.const c []) with
    | .prim hs _ _ => return s!"(call {hs} {" ".intercalate args.toList})"
    | .decl hs _ _ => return s!"(call {hs} {" ".intercalate args.toList})"
    | _ => unsupported s!"core mode: constructor {c}"; return "(var erased)"
  | _ => do unsupported "core mode: this kind of value"; return "(var erased)"

/-- Code as an s-expression: `(let x value code)`, `(case x (True code) (False code))`,
`(ret x)`. -/
partial def zcCode (c : Code .pure) : EmitM String := do
  match c with
  | .let d k =>
    let v ← zcValue d.value
    let x ← bindT d.fvarId d.binderName (← hsTyM d.type)
    return s!"(let {x} {v} {← zcCode k})"
  | .return x => return s!"(ret {← lookup x})"
  | .cases cs =>
    let x ← lookup cs.discr
    let mut alts : Array String := #[]
    for a in cs.alts do
      match a with
      | .alt n _ k =>
        let con ← if n == `Bool.true then pure "True"
          else if n == `Bool.false then pure "False"
          else do unsupported s!"core mode: case on {n}"; pure "?"
        alts := alts.push s!"({con} {← zcCode k})"
      | .default k => alts := alts.push s!"(_ {← zcCode k})"
    return s!"(case {x} {" ".intercalate alts.toList})"
  | _ => do unsupported "core mode: this kind of code"; return "(ret erased)"

/-- One declaration as `(fn name (params) code)`, and its stub signature for the Haskell side. -/
def zcDecl (d : Decl .pure) : EmitM (String × String) := do
  let .code body := d.value | return ("", "")
  let ps ← d.params.mapM bindP
  let n := fnName d.name
  let ptys ← d.params.toList.mapM (hsTyM ·.type)
  let sig := " -> ".intercalate (ptys ++ [← declRetM d])
  let code ← zcCode body
  return (s!"(fn {n} ({" ".intercalate ps.toList}) {code})\n", s!"{n} :: {sig}\n{n} = {n}\n")

/-- The stub module (declarations the plugin will fill in) and the s-expression file. -/
def emitCore (modName : String) (roots : Array Name) : CoreM (String × String) := do
  let act : EmitM (String × String) := do
    for r in roots do request r
    let mut zc : Array String := #[]
    let mut stubs : Array String := #[]
    let mut i := 0
    while i < (← get).queue.size do
      let n := (← get).queue[i]!
      i := i + 1
      if let some d ← monoDecl? n then
        let (z, st) ← zcDecl d
        zc := zc.push z
        stubs := stubs.push st
    let bad := (← get).unsupported
    unless bad.isEmpty do
      throwError "leanzempic core mode: unsupported in this spike:\n  {
        "\n  ".intercalate bad.toList}"
    let header := "\n".intercalate [
      "-- Stub generated by leanzempic. The Core plugin replaces every right-hand side.",
      s!"module {modName} where", "", "import Zempic.Nat.Word", "", ""]
    -- Bind each runtime primitive the code calls, so the plugin can read its Id off the stub.
    let calls := ("\n".intercalate zc.toList).splitOn "(call " |>.drop 1
    let names := calls.map fun t => (t.takeWhile (fun c => c != ' ' && c != ')')).toString
    let prims := names.eraseDups.filter fun n => !n.startsWith "z_"
    let primStubs := prims.map fun n => s!"p_{n} = {n}\n"
    return (header ++ "\n".intercalate stubs.toList ++ "\n" ++ "".intercalate primStubs,
      "\n".intercalate zc.toList)
  act.run' { fast := true }

/-- Haskell wrapper for auto mode: for each root whose signature is only `Nat`/`Bool`, run the
`Word` version and fall back to the exact one if it overflows. -/
def autoWrapper (modName : String) (roots : Array Name) : CoreM String := do
  let mut exports : Array String := #[]
  let mut defs : Array String := #[]
  let mut skipped : Array String := #[]
  for r in roots do
    let some d ← getDeclAt? r .mono | continue
    let ptys := d.params.toList.map (basicTy ·.type)
    let ret := declRetBasic d
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
    CoreM (Array (String × String) × String × Bool) := do
  let rel := fun (m : String) => (m.replace "." "/") ++ ".hs"
  match mode with
  | "word" =>
    let o ← emitModule modName roots "Zempic.Nat.Word" true
    return (#[(rel modName, o.haskell)], o.core, o.fusible)
  | "exact" =>
    let o ← emitModule modName roots "Zempic.Nat.Exact" false
    return (#[(rel modName, o.haskell)], o.core, o.fusible)
  | _ =>
    let fast ← emitModule (modName ++ ".Fast") roots "Zempic.Nat.Word" true
    let exact ← emitModule (modName ++ ".Exact") roots "Zempic.Nat.Exact" false
    let wrap ← autoWrapper modName roots
    return (#[(rel modName, wrap), (rel (modName ++ ".Fast"), fast.haskell),
              (rel (modName ++ ".Exact"), exact.haskell)], exact.core, fast.fusible)

end Zempic
