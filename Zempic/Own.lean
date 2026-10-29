/-
Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.

A conservative ownership analysis over LCNF, to decide when an array operation may update in
place. Lean knows this at run time from reference counts; GHC has none, so the Haskell backend
proves it at compile time or falls back to a persistent array.

An abstract value is `top` (shared or unknown), `own` (an array that nothing else references),
or `con c fs` (a constructor cell that nothing else references, holding fields with known
ownership: how a loop's `MProd` state carries its array). Every variable starts as `top`; only
fresh arrays, the results of destructive operations, constructor cells built from owned parts, and
parameters that every caller passes owned become more. Anything unrecognized forgets ownership.
An operation is destructive only if its array is `own` and no later code can see it.

Parameter, return and join-point summaries are met over all call sites and iterated to a fixpoint,
starting from "no information". Roots, and functions used as values, get `top` parameters.
-/
import Lean

open Lean Compiler LCNF

/-- Update arrays in place where the ownership analysis proves it safe. -/
register_option zempic.own : Bool := {
  defValue := true
  descr := "(leanzempic) update arrays in place where an ownership analysis proves it safe"
}

namespace Zempic.Own

/-- What is known about the ownership of a value. -/
inductive AV
  /-- Shared, or not known to be unshared. -/
  | top
  /-- An array with exactly one reference. -/
  | own
  /-- A constructor cell with exactly one reference, with the ownership of its fields. -/
  | con (c : Name) (fs : Array AV)
  deriving BEq, Inhabited

/-- Does this value carry any ownership? -/
def AV.isTop : AV → Bool
  | .top => true
  | _ => false

/-- The most that two values both guarantee. -/
partial def AV.meet : AV → AV → AV
  | .own, .own => .own
  | .con c fs, .con d gs =>
    if c == d && fs.size == gs.size then
      let hs := (fs.zip gs).map fun (a, b) => AV.meet a b
      if hs.all AV.isTop then .top else .con c hs
    else .top
  | _, _ => .top

/-- How deeply nested constructor cells are tracked. A loop with `k` mutable variables nests its
state `k` levels deep in `MProd` cells, so this bounds how many variables a loop may have and still
keep ownership of an array. It exists so the fixpoint is finite, not because deeper is costly. -/
def maxDepth : Nat := 12

/-- Limit nesting, so the fixpoint is finite. -/
partial def AV.cap (d : Nat) : AV → AV
  | .con c fs => if d == 0 then .top else .con c (fs.map (AV.cap (d - 1)))
  | v => v

/-- A set of variables. -/
abbrev FVS := Std.HashSet FVarId

/-- Variable ids are unique only within one function, so anything remembered across functions is
keyed by the function as well. -/
abbrev Key := Name × FVarId

/-! ## Free variables -/

/-- Add an argument's variable, if it is one, to a set. -/
def argFv (a : Arg .pure) (s : FVS) : FVS :=
  match a with
  | .fvar x => s.insert x
  | _ => s

/-- The variables a `let` right-hand side uses. -/
def valFv : LetValue .pure → FVS
  | .fvar f args => args.foldl (fun s a => argFv a s) (({} : FVS).insert f)
  | .const _ _ args => args.foldl (fun s a => argFv a s) {}
  | .proj _ _ x => ({} : FVS).insert x
  | _ => {}

mutual
/-- Free variables of `c`; a jump counts as using whatever its join point's body uses. -/
partial def fvCode (jf : Std.HashMap FVarId FVS) (c : Code .pure) : FVS :=
  match c with
  | .let d k => (fvCode jf k).erase d.fvarId |>.union (valFv d.value)
  | .fun d k => (fvFun jf d).union (fvCode jf k)
  | .jp d k => fvCode (jf.insert d.fvarId (fvFun jf d)) k
  | .jmp j args => args.foldl (fun s a => argFv a s) (jf.getD j {})
  | .cases cs =>
    cs.alts.foldl (fun s a => match a with
      | .alt _ ps k => (ps.foldl (fun t p => t.erase p.fvarId) (fvCode jf k)).union s
      | .default k => (fvCode jf k).union s) (({} : FVS).insert cs.discr)
  | .return x => ({} : FVS).insert x
  | _ => {}

/-- Free variables of a local function or join point body, without its own parameters. -/
partial def fvFun (jf : Std.HashMap FVarId FVS) (d : FunDecl .pure) : FVS :=
  d.params.foldl (fun t p => t.erase p.fvarId) (fvCode jf d.value)
end

/-- The free variables of every join point body in `c` (inner join points resolved first). -/
partial def jpFvs (c : Code .pure) (jf : Std.HashMap FVarId FVS := {}) :
    Std.HashMap FVarId FVS :=
  match c with
  | .let _ k => jpFvs k jf
  | .fun d k => jpFvs k (jpFvs d.value jf)
  | .jp d k =>
    let jf := jpFvs d.value jf
    jpFvs k (jf.insert d.fvarId (fvFun jf d))
  | .cases cs => cs.alts.foldl (fun jf a => match a with
      | .alt _ _ k => jpFvs k jf
      | .default k => jpFvs k jf) jf
  | _ => jf

/-! ## Array operations -/

/-- Operations that can update their array argument (argument 1) in place. -/
def destructiveOps : List Name :=
  [`Array.set!, `Array.uset, `Array.push, `Array.pop, `Array.swapIfInBounds, `Array.swap]

/-- Operations that produce a new array nobody else has. -/
def freshOps : List Name :=
  [`Array.mkEmpty, `Array.emptyWithCapacity, `Array.replicate, `Array.range, `Array.mk,
   `List.toArray, `List.toArrayImpl]

/-- Operations that only look at their arrays. -/
def readOps : List Name :=
  [`Array.size, `Array.usize, `Array.get!Internal, `Array.getInternal, `Array.uget, `Array.toList]

/-! ## The analysis -/

/-- Summaries (met over all uses; `none` means no use seen yet) and what has been decided. -/
structure Sums where
  /-- Ownership of each function parameter. -/
  params : Std.HashMap Name (Array (Option AV)) := {}
  /-- Ownership of each function result. -/
  rets : Std.HashMap Name (Option AV) := {}
  /-- Ownership of each join point parameter. -/
  jps : Std.HashMap Key (Array (Option AV)) := {}
  /-- Did this pass change a summary? -/
  changed : Bool := false
  /-- Let bindings whose array operation may update in place. -/
  destr : Std.HashSet Key := {}
  /-- Call arguments to wrap in a lazy copy: (function, the call's `let`, argument position). -/
  shares : Std.HashSet (Name × FVarId × Nat) := {}
  /-- Parameters that some array update can reach (see `mutatedParams`). -/
  mutP : Std.HashMap Name (Array Bool) := {}
  /-- Functions whose parameters nothing is known about. -/
  esc : Std.HashSet Name := {}

/-- The analysis monad: the summaries, over `CoreM`. -/
abbrev OwnM := StateRefT Sums CoreM

/-- What is currently known to be owned, by variable (absent means `top`). -/
abbrev Env := Std.HashMap FVarId AV

/-- Meet `v` into a summary slot, noting a change. -/
def meetOpt (old : Option AV) (v : AV) : Option AV × Bool :=
  match old with
  | none => (some (v.cap maxDepth), true)
  | some o =>
    let n := (o.meet v).cap maxDepth
    (some n, n != o)

/-- Meet what a call passes into the summary of a function's parameter. -/
def noteParam (g : Name) (j : Nat) (v : AV) : OwnM Unit :=
  modify fun s =>
    match s.params[g]? with
    | none => s
    | some arr =>
      if h : j < arr.size then
        let (n, ch) := meetOpt arr[j] v
        { s with params := s.params.insert g (arr.set j n), changed := s.changed || ch }
      else s

/-- Meet what a jump passes into the summary of a join point's parameter. -/
def noteJp (f : Name) (j : FVarId) (i : Nat) (v : AV) : OwnM Unit :=
  modify fun s =>
    match s.jps[(f, j)]? with
    | none => s
    | some arr =>
      if h : i < arr.size then
        let (n, ch) := meetOpt arr[i] v
        { s with jps := s.jps.insert (f, j) (arr.set i n), changed := s.changed || ch }
      else s

/-- Meet what a function returns into the summary of its result. -/
def noteRet (f : Name) (v : AV) : OwnM Unit :=
  modify fun s =>
    let (n, ch) := meetOpt (s.rets.getD f none) v
    { s with rets := s.rets.insert f n, changed := s.changed || ch }

/-- The ownership of an argument. -/
def lookupAV (env : Env) (a : Arg .pure) : AV :=
  match a with
  | .fvar x => env.getD x .top
  | _ => .top

/-- How many times does variable `x` occur among `args`? -/
def occurrences (args : Array (Arg .pure)) (x : FVarId) : Nat :=
  args.foldl (fun n a => match a with | .fvar y => if y == x then n + 1 else n | _ => n) 0

/-- The ownership an argument can hand over: only if it is owned, appears once among the arguments,
and nothing after the instruction uses it. -/
def handOver (env : Env) (args : Array (Arg .pure)) (later : FVS) (a : Arg .pure) : AV :=
  match a with
  | .fvar x =>
    if occurrences args x == 1 && !later.contains x then env.getD x .top else .top
  | _ => .top

/-- Forget the ownership of every variable among the arguments. -/
def eraseArgs (env : Env) (args : Array (Arg .pure)) : Env :=
  args.foldl (fun e a => match a with | .fvar x => e.erase x | _ => e) env

mutual
/-- Walk `c` in function `f`, with `jf` the join point free variables. -/
partial def walk (f : Name) (jf : Std.HashMap FVarId FVS) (c : Code .pure) (env : Env) :
    OwnM Unit := do
  match c with
  | .let d k =>
    let later := fvCode jf k
    match ← step f d env later with
    | some env' => walk f jf k env'
    | none => pure ()  -- a call whose result is not known yet: the rest is unreached this pass
  | .fun d k =>
    let captured := fvFun jf d
    let env' := captured.fold (fun e x => e.erase x) env
    walk f jf d.value {}
    walk f jf k env'
  | .jp d k =>
    modify fun s => { s with jps := s.jps.insertIfNew (f, d.fvarId) (d.params.map fun _ => none) }
    let sum := (← get).jps.getD (f, d.fvarId) #[]
    -- Until some jump supplies information the body is unreached; analyzing it now would
    -- pessimistically report `top` to everything it calls.
    if sum.all Option.isSome then
      let jenv : Env := (d.params.zip sum).foldl (fun e (p, v) =>
        match v with
        | some av => if av.isTop then e else e.insert p.fvarId av
        | none => e) {}
      walk f jf d.value jenv
    walk f jf k env
  | .jmp j args =>
    let later := jf.getD j {}
    for a in args, i in [0:args.size] do
      noteJp f j i (handOver env args later a)
  | .return x => noteRet f (env.getD x .top)
  | .cases cs =>
    let av := env.getD cs.discr .top
    for a in cs.alts do
      match a with
      | .default k => walk f jf k env
      | .alt n ps k =>
        let later := fvCode jf k
        match av with
        | .con c fs =>
          if c == n && fs.size == ps.size && !later.contains cs.discr then
            let env' := (ps.zip fs).foldl (fun e (p, v) =>
              if v.isTop then e else e.insert p.fvarId v) (env.erase cs.discr)
            walk f jf k env'
          else walk f jf k (env.erase cs.discr)
        | _ => walk f jf k env
  | .unreach _ => pure ()
  | _ => pure ()

/-- One `let`: update what is owned, and the summaries it feeds. -/
partial def step (f : Name) (d : LetDecl .pure) (env : Env) (later : FVS) : OwnM (Option Env) := do
  match d.value with
  | .const c _ args =>
    if freshOps.contains c then
      return some ((eraseArgs env args).insert d.fvarId .own)
    else if destructiveOps.contains c then
      -- The array is argument 1, after the erased element type.
      match (args[1]? : Option (Arg .pure)) with
      | some (Arg.fvar a) =>
        let ok := env.getD a .top == .own && !later.contains a && occurrences args a == 1
        let env' := eraseArgs env args
        if ok then
          modify fun s => { s with destr := s.destr.insert (f, d.fvarId) }
          return some (env'.insert d.fvarId .own)
        else return some env'
      | _ => return some (eraseArgs env args)
    else if readOps.contains c then
      return some env
    else
      let envC ← getEnv
      match envC.find? c with
      | some (.ctorInfo v) =>
        let fields := args.extract v.numParams args.size
        let avs := fields.map (handOver env fields later)
        let env' := eraseArgs env args
        let cell := (AV.con c avs).cap maxDepth
        return some (if avs.all AV.isTop then env' else env'.insert d.fvarId cell)
      | _ =>
        match (← get).params[c]? with
        | some ps =>
          if ps.size == args.size then
            for a in args, j in [0:args.size] do
              let ho := handOver env args later a
              -- A shared array handed to a parameter that gets updated: pass a lazy copy instead, which
              -- is private to the callee (so the callee may update it in place) and copies only if it
              -- is written. This is what Lean's reference counts do at run time.
              let sums ← get
              let wanted := match a with
                | .fvar _ => ho.isTop && !sums.esc.contains c && (sums.mutP.getD c #[]).getD j false
                | _ => false
              if wanted then
                noteParam c j .own
                modify fun s => { s with shares := s.shares.insert (f, d.fvarId, j) }
              else noteParam c j ho
            let env' := eraseArgs env args
            match (← get).rets.getD c none with
            | some r => return some (if r.isTop then env' else env'.insert d.fvarId r)
            | none => return none
          else return some (eraseArgs env args)
        | none => return some (eraseArgs env args)
  | .proj _ i x =>
    match env.getD x .top with
    | .con c fs =>
      let v := fs.getD i .top
      if later.contains x then
        -- x lives on, so its field is now shared with this projection.
        return some ((env.insert x (.con c (fs.set! i .top))).insert d.fvarId .top)
      else
        return some (if v.isTop then env.erase x else (env.erase x).insert d.fvarId v)
    | _ => return some env
  | .fvar g args =>
    return some (eraseArgs (env.erase g) args)
  | _ => return some env
end

/-! ## Driver -/

/-- Constants referenced by `c`. -/
partial def consts (c : Code .pure) (acc : Std.HashSet Name) : Std.HashSet Name :=
  match c with
  | .let d k =>
    let acc := match d.value with | .const n _ _ => acc.insert n | _ => acc
    consts k acc
  | .fun d k => consts k (consts d.value acc)
  | .jp d k => consts k (consts d.value acc)
  | .cases cs => cs.alts.foldl (fun a al => match al with
      | .alt _ _ k => consts k a
      | .default k => consts k a) acc
  | _ => acc

/-- Calls that do not pass every parameter (partial or over-application) make a function escape. -/
partial def partialCalls (decls : Std.HashMap Name (Decl .pure)) (c : Code .pure)
    (acc : Std.HashSet Name) : Std.HashSet Name :=
  match c with
  | .let d k =>
    let acc := match d.value with
      | .const n _ args => match decls[n]? with
        | some g => if g.params.size == args.size then acc else acc.insert n
        | none => acc
      | _ => acc
    partialCalls decls k acc
  | .fun d k => partialCalls decls k (partialCalls decls d.value acc)
  | .jp d k => partialCalls decls k (partialCalls decls d.value acc)
  | .cases cs => cs.alts.foldl (fun a al => match al with
      | .alt _ _ k => partialCalls decls k a
      | .default k => partialCalls decls k a) acc
  | _ => acc

/-- Parameters of each function that an array update can reach: the parameter itself is the array of a
destructive operation, or is passed to a parameter of a function that is such. Only direct uses are
followed, so this can miss a parameter (no copy is then made) but never names a non-array. -/
partial def mutScan (pidx : Std.HashMap FVarId Nat) (mp : Std.HashMap Name (Array Bool))
    (c : Code .pure) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
  match c with
  | .let d k =>
    let acc := match d.value with
      | .const g _ args =>
        if destructiveOps.contains g then
          match (args[1]? : Option (Arg .pure)) with
          | some (Arg.fvar x) => match pidx[x]? with | some i => acc.insert i | none => acc
          | _ => acc
        else match mp[g]? with
          | some flags =>
            if flags.size == args.size then
              (args.toList.zip flags.toList).foldl (fun a (arg, fl) =>
                match arg with
                | .fvar x => if fl then (match pidx[x]? with | some i => a.insert i | none => a) else a
                | _ => a) acc
            else acc
          | none => acc
      | _ => acc
    mutScan pidx mp k acc
  | .fun d k => mutScan pidx mp k (mutScan pidx mp d.value acc)
  | .jp d k => mutScan pidx mp k (mutScan pidx mp d.value acc)
  | .cases cs => cs.alts.foldl (fun a al => match al with
      | .alt _ _ k => mutScan pidx mp k a
      | .default k => mutScan pidx mp k a) acc
  | _ => acc

/-- The fixpoint of `mutScan` over all functions. -/
def mutatedParams (decls : Std.HashMap Name (Decl .pure)) : Std.HashMap Name (Array Bool) := Id.run do
  let mut mp : Std.HashMap Name (Array Bool) :=
    decls.fold (fun m n d => m.insert n (d.params.map fun _ => false)) {}
  for _ in [0:20] do
    let mut changed := false
    for (n, d) in decls.toList do
      if let .code body := d.value then
        let pidx : Std.HashMap FVarId Nat :=
          (d.params.toList.zipIdx).foldl (fun m (p, i) => m.insert p.fvarId i) {}
        let hit := mutScan pidx mp body {}
        let old := mp.getD n #[]
        let new := old.mapIdx fun i b => b || hit.contains i
        if new != old then
          mp := mp.insert n new
          changed := true
    unless changed do break
  return mp

/-- Which `let`s may update an array in place, for the code reachable from `roots`? -/
def analyze (roots : Array Name) :
    CoreM (Std.HashSet Key × Std.HashSet (Name × FVarId × Nat)) := do
  -- Collect the reachable compiled functions.
  let mut decls : Std.HashMap Name (Decl .pure) := {}
  let mut todo := roots.toList
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if decls.contains n then continue
    if let some d ← getDeclAt? n .mono then
      if let .code body := d.value then
        decls := decls.insert n d
        for m in (consts body {}).toList do todo := m :: todo
  -- Roots are called from outside and values escape: nothing is known about their parameters.
  let mut escaping : Std.HashSet Name := {}
  for r in roots do escaping := escaping.insert r
  for (_, d) in decls.toList do
    if let .code body := d.value then escaping := partialCalls decls body escaping
  let startParams := decls.fold (fun m n d =>
      m.insert n (d.params.map fun _ => if escaping.contains n then some .top else none)) {}
  let start : Sums := { params := startParams, mutP := mutatedParams decls, esc := escaping }
  let (_, final) ← (do
    let mut fuel := 50
    while fuel > 0 do
      fuel := fuel - 1
      modify fun s => { s with changed := false, destr := {}, shares := {} }
      for (n, d) in decls.toList do
        if let .code body := d.value then
          let sums := (← get).params.getD n #[]
          if sums.all Option.isSome then
            let env : Env := (d.params.zip sums).foldl (fun e (p, v) =>
              match v with
              | some av => if av.isTop then e else e.insert p.fvarId av
              | none => e) {}
            walk n (jpFvs body) body env
      if !(← get).changed then break
    : OwnM Unit).run start
  return (final.destr, final.shares)

end Zempic.Own
