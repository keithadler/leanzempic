#!/usr/bin/env python3
"""Targeted differential fuzzer: hoisted buffers, in-place arrays, the Nat word/exact path, UTF-8 strings.

    python3 tools/fuzz2.py FIRST COUNT [FUNCTIONS] [FAMILIES]

FAMILIES is a comma list of: hoist (loops over unboxed buffers: UInt8/16/32/64, USize, Bool, Char, Nat),
nat (Nat and UInt arithmetic around 2^31, 2^63, 2^64 and beyond, also stored in Array Nat), str (UTF-8
strings with one- to four-byte characters, mid-character positions, extract/get/next/prev), arr (arrays
with snapshots and forks, nested arrays). Default: all four.

For each seed it writes build/fuzz2/ one Lean file per configuration and runs the program natively
(`lean --run`), then compiles it three ways and requires byte-identical output:

  d  default settings:      no fusion, GHC -O1, default RTS
  r  recommended settings:  `set_option zempic.fuse true`, tools/zghc (-O2, -A256m -O1g)
  f  fusion, plain RTS:     `set_option zempic.fuse true`, GHC -O1, default RTS

A mismatch keeps the files and prints the seed and the first differing line; `--minimize` is done by hand
with the FUNCTIONS and FAMILIES arguments (the same seed with fewer functions gives a prefix-independent
program, because every function draws from its own random stream).
"""
import os, random, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "build", "fuzz2")
NS = [0, 1, 2, 5, 13, 40, 120]

# ---------------------------------------------------------------- element types
TYPES = ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Bool", "Char", "Nat", "Nat", "Nat"]

def tn(T, x):
    """Nat view of an element expression."""
    if T == "Nat": return x
    return f"({x}).toNat"

BIGS = ["4294967295", "4294967296", "2147483648", "4611686018427387904", "9223372036854775807",
        "9223372036854775808", "18446744073709551615", "18446744073709551616", "18446744073709551617",
        "340282366920938463463374607431768211456", "3037000499", "3037000500", "4294967311"]

class Ctx:
    """Names in scope while a loop body is generated."""
    def __init__(self, r, T, big):
        self.r, self.T, self.big = r, T, big
        self.olds = []      # names of older versions of the array
        self.n = 0
    def fresh(self, p):
        self.n += 1
        return f"{p}{self.n}"

def idx(c, arr="a"):
    r = c.r
    return r.choice(["i", f"(i % ({arr}.size + 1))", f"(i % {arr}.size)", f"({arr}.size - 1)", f"({arr}.size / 2)", "(i + 1)",
                     f"{arr}.size", "(i * 7 % (" + arr + ".size + 2))", "0", str(r.randint(0, 5)), "(i / 2)", "(fuel - i)"])

def nat_atom(c, arr="a"):
    r = c.r
    ch = r.randint(0, 9)
    if ch == 0: return "i"
    if ch == 1: return "acc"
    if ch == 2: return f"{arr}.size"
    if ch == 3: return str(r.randint(0, 300))
    if ch == 4: return tn(c.T, f"{arr}[{idx(c, arr)}]!")
    if ch == 5: return tn(c.T, f"({arr}.getD {idx(c, arr)} {dflt(c.T)})")
    if ch == 6: return "n"
    if ch == 7 and c.big: return r.choice(BIGS)
    return "(i + 1)"

def nat_expr(c, arr="a", d=0):
    r = c.r
    if d >= 2 or r.random() < 0.3: return nat_atom(c, arr)
    x, y = nat_expr(c, arr, d + 1), nat_expr(c, arr, d + 1)
    op = r.choice(["+", "+", "*", "-", "/", "%", "*"] if c.big else ["+", "-", "*", "%", "/"])
    if op == "%": return f"({x} % ({y} + 1))"
    if op == "*" and not c.big: return f"({x} * {r.randint(1,9)} + {y})"
    return f"({x} {op} {y})"

def dflt(T):
    return {"Bool": "false", "Char": "'x'", "Nat": "0"}.get(T, "0")

def val(c, arr="a"):
    """An expression of the element type."""
    T, r = c.T, c.r
    e = nat_expr(c, arr)
    if T == "Nat":
        ch = r.randint(0, 5)
        if c.big and ch == 0: return f"({arr}[{idx(c, arr)}]! * {arr}[{idx(c, arr)}]! + i)"
        if c.big and ch == 1: return f"({arr}[{idx(c, arr)}]! * {r.choice(BIGS)} + {e})"
        if c.big and ch == 2: return f"({arr}[{idx(c, arr)}]! - {r.choice(BIGS)})"
        if c.big and ch == 3: return f"({arr}[{idx(c, arr)}]! <<< {r.randint(0, 70)})"
        if c.big and ch == 4: return f"({arr}[{idx(c, arr)}]! + {r.choice(BIGS)})"
        return e
    if T == "Bool": return r.choice([f"({e} % {r.randint(2,5)} == 0)", f"(!{arr}[{idx(c, arr)}]!)", f"({e} < {r.randint(0,40)})", "(i % 2 == 0)"])
    if T == "Char":
        return r.choice([f"(Char.ofNat ({e} % 300 + 30))", f"(Char.ofNat ({e} % 70000))", f"(Char.ofNat (55290 + {e} % 12))", f"{arr}[{idx(c, arr)}]!"])
    ch = r.randint(0, 4)
    if ch == 0: return f"({arr}[{idx(c, arr)}]! + {T}.ofNat {e})"
    if ch == 1: return f"({arr}[{idx(c, arr)}]! * {r.randint(2,9)} + {T}.ofNat i)"
    if ch == 2: return f"({T}.ofNat {r.choice(BIGS) if c.big else e})"
    if ch == 3: return f"({arr}[{idx(c, arr)}]! - {arr}[{idx(c, arr)}]!)"
    return f"({T}.ofNat {e})"

def cond(c, arr="a"):
    r = c.r
    return r.choice(["i % 3 == 0", "i % 2 == 1", f"{nat_expr(c, arr)} % 3 == 1", f"{arr}.size % 2 == 0", f"{nat_expr(c, arr)} < {nat_expr(c, arr)}",
                     f"i < {arr}.size", "acc % 5 < 2"])

def digest_arr(T, x):
    return f"({x}.foldl (fun h v => (h * 31 + {tn(T, 'v')}) % 2305843009213693951) 7 + {x}.size)"

# One body statement. Returns list of lines (let style: shadow the array name; mut style: assign).
def stmt(c, mut):
    r, T = c.r, c.T
    pre = (lambda e: f"a := {e}") if mut else (lambda e: f"let a := {e}")
    accs = (lambda e: f"acc := {e}") if mut else (lambda e: f"let acc := {e}")
    M = r.choice(["1000000007", "2305843009213693951", "340282366920938463463374607431768211297"]) if c.big else "1000000007"
    k = r.randint(0, 17)
    if k <= 2: return [pre(f"a.set! {idx(c)} {val(c)}")]
    if k == 3: return [pre(f"a.push {val(c)}")]
    if k == 4: return [pre("a.pop")]
    if k == 5: return [pre(f"a.swapIfInBounds {idx(c)} {idx(c)}")]
    if k in (6, 7): return [accs(f"(acc * {r.randint(2,40)} + {tn(T, f'a[{idx(c)}]!')}) % {M}")]
    if k == 8: return [accs(f"(acc + {r.randint(1,9)} * {tn(T, f'(a.getD {idx(c)} {dflt(T)})')}) % {M}")]
    if k == 9:
        o = c.fresh("o"); c.olds.append(o); return [f"let {o} := a"]
    if k == 10 and c.olds:
        o = r.choice(c.olds)
        return [accs(f"(acc * 3 + {tn(T, f'{o}[{idx(c, o)}]!')} + {o}.size * 5) % {M}")]
    if k == 11:
        f = c.fresh("f")
        e = r.choice([f"a.set! {idx(c)} {val(c)}", f"a.push {val(c)}", "a.pop", f"a.swapIfInBounds {idx(c)} {idx(c)}"])
        return [f"let {f} := {e}", accs(f"(acc * 7 + {tn(T, f'{f}[{idx(c, f)}]!')} + {f}.size + {tn(T, f'a[{idx(c)}]!')}) % {M}")]
    if k == 12:
        return [pre(f"if {cond(c)} then a.push {val(c)} else a.set! {idx(c)} {val(c)}")]
    if k == 13:
        return [pre(f"if {cond(c)} then a.pop else a.swapIfInBounds {idx(c)} {idx(c)}")]
    if k == 14: return [pre(f"poke{c.tag} a {idx(c)} {val(c)}")]
    if k == 15 and c.olds:   # the old version is written, the new one read: persistent update
        o = r.choice(c.olds); f = c.fresh("p")
        return [f"let {f} := {o}.set! {idx(c, o)} {val(c, o)}", accs(f"(acc + {tn(T, f'{f}[{idx(c, f)}]!')} * 3 + {tn(T, f'a[{idx(c)}]!')}) % {M}")]
    if k == 16: return [accs(f"(acc * 5 + b.size + {tn(T, f'b[{idx(c, 'b')}]!')}) % {M}")]
    if k == 17: return [accs(f"(acc + a.size * 11) % {M}")]
    return [accs(f"(acc + {r.randint(1,9)}) % {M}")]

def fill_expr(c, k, off):
    return val(c, "a") if False else None

def mk_fn(r, T, big, cap, kind):
    """Helper building an Array T of length k; several ways, so the buffer is unboxed or not."""
    name = f"mk{cap}"
    c = Ctx(r, T, big)
    elem = {"UInt8": "UInt8", "UInt16": "UInt16", "UInt32": "UInt32", "UInt64": "UInt64", "USize": "USize", "Bool": "Bool", "Char": "Char", "Nat": "Nat"}[T]
    if T == "Nat": ev = r.choice(["(i * 3 + off)", "(i * i + off)", "(2 ^ 62 + i * off)", "(18446744073709551615 - i + off)", "(i * 4294967296 + off)", "(9223372036854775800 + i)"] if big else ["(i * 3 + off)", "(i * i + off)"])
    elif T == "Bool": ev = "((i + off) % 3 == 0)"
    elif T == "Char": ev = "(" + r.choice(["Char.ofNat (97 + (i + off) % 26)", "Char.ofNat (200 + (i + off) * 37 % 3000)", "Char.ofNat (128512 + (i + off) % 40)"]) + ")"
    else: ev = f"({T}.ofNat (i * {r.randint(3, 250)} + off))"
    if kind == "push":
        return name, (f"def {name} (k off : Nat) : Array {elem} := Id.run do\n  let mut a : Array {elem} := Array.mkEmpty {cap}\n"
                      f"  for i in [0:k] do a := a.push {ev}\n  return a\n")
    if kind == "map":
        return name, f"def {name} (k off : Nat) : Array {elem} := (Array.range k).map (fun i => {ev})\n"
    if kind == "append":
        return name, (f"def {name} (k off : Nat) : Array {elem} := Id.run do\n  let mut a : Array {elem} := Array.mkEmpty {cap}\n"
                      f"  for i in [0:k / 2] do a := a.push {ev}\n  let mut b : Array {elem} := Array.mkEmpty {cap + 1}\n"
                      f"  for i in [k / 2:k] do b := b.push {ev}\n  return a ++ b\n")
    if kind == "extract":
        return name, (f"def {name} (k off : Nat) : Array {elem} := Id.run do\n  let mut a : Array {elem} := Array.mkEmpty {cap}\n"
                      f"  for i in [0:k + 3] do a := a.push {ev}\n  return a.extract 2 (k + 2)\n")
    return name, (f"def {name} (k off : Nat) : Array {elem} := (List.range k).map (fun i => {ev}) |>.toArray\n")

HOIST_FN = 0
def fam_hoist(r, k, cap0):
    T = r.choice(TYPES)
    big = T == "Nat" and r.random() < 0.7
    elem = T
    tag = f"_{k}"
    c = Ctx(r, T, big); c.tag = tag
    helpers = []
    kinds = ["push", "push", "push", "map", "append", "extract", "list"]
    mka, mkaSrc = mk_fn(r, T, big, cap0, r.choice(kinds))
    mkb, mkbSrc = mk_fn(r, T, big, cap0 + 1, r.choice(kinds))
    helpers += [mkaSrc, mkbSrc]
    hc = Ctx(r, T, big); hc.tag = tag
    helpers.append(f"def poke{tag} (a : Array {elem}) (i : Nat) (v : {elem}) : Array {elem} := a.set! i v\n")
    form = r.choice(["rec", "rec", "do", "dowhile"])
    nst = r.randint(2, 7)
    out = []
    out += helpers
    n_body = []
    mut = form != "rec"
    for _ in range(nst):
        n_body += stmt(c, mut)
    ind = "    " if True else ""
    if form == "rec":
        exitc = r.choice(["", f"    if acc % {r.randint(7, 40)} == 3 then (acc, a) else\n", f"    if a.size > {r.randint(30, 200)} then (acc, a.pop) else\n"])
        body = "\n".join("    " + l for l in n_body)
        call = r.choice(["lp{t} a b (i + 1) fuel acc", "lp{t} a a (i + 1) fuel acc", "lp{t} a (a.push {v}) (i + 1) fuel acc".replace("{v}", val(c))]).replace("{t}", tag)
        out.append(f"partial def lp{tag} (a b : Array {elem}) (i fuel acc : Nat) : Nat × Array {elem} :=\n  if i < fuel then\n"
                   f"    let n := fuel\n{exitc}{body}\n    {call}\n  else (acc, a)\n")
        entry = (f"def f{k} (n : Nat) : Nat :=\n  let z := n / 1000\n  let (x, a) := lp{tag} ({mka} (n % 40 + 2) {r.randint(0, 300)}) ({mkb} (n % 9 + 1) 3) z (n * {r.randint(1,4)} + {r.randint(0,6)}) z\n"
                 f"  x + {digest_arr(T, 'a')}")
    else:
        body = "\n".join("      " + l for l in n_body)
        loop = (f"  for i in [z:fuel] do\n      let n := fuel\n{body}\n" if form == "do" else
                f"  let mut i := z\n  while i < fuel do\n      let n := fuel\n{body}\n      i := i + 1\n")
        brk = r.choice(["", f"      if acc % {r.randint(7,40)} == 3 then break\n"]) if True else ""
        if form == "do":
            loop = loop.rstrip("\n") + "\n" + brk
        out.append(f"def lp{tag} (a0 b : Array {elem}) (z fuel : Nat) : Nat × Array {elem} := Id.run do\n  let mut a := a0\n  let mut acc := z\n{loop}  return (acc, a)\n")
        entry = (f"def f{k} (n : Nat) : Nat :=\n  let z := n / 1000\n  let (x, a) := lp{tag} ({mka} (n % 40 + 2) {r.randint(0, 300)}) ({mkb} (n % 9 + 1) 3) z (n * {r.randint(1,4)} + {r.randint(0,6)})\n"
                 f"  x + {digest_arr(T, 'a')}")
    out.append(entry)
    return "\n".join(out)

# ---------------------------------------------------------------- Nat / fixed-width arithmetic
def fam_nat(r, k, cap0):
    L = []
    pool = []     # Nat variables
    lits = BIGS + ["0", "1", "2", "3", "255", "256", "65535", "65536", "1000000007"]
    L.append("  let z := n / 1000")
    def atom():
        ch = r.random()
        if pool and ch < 0.6: return r.choice(pool)
        if ch < 0.8: return f"({r.choice(lits)} + z)"
        if ch < 0.9: return "n"
        return f"({r.choice(lits)} - z)"
    for j in range(r.randint(8, 18)):
        x, y = atom(), atom()
        op = r.randint(0, 27)
        e = {
            0: f"{x} + {y}", 1: f"{x} - {y}", 2: f"{x} * {y}", 3: f"{x} / {y}", 4: f"{x} % {y}",
            5: f"{x} <<< ({r.randint(0, 70)} + z)", 6: f"{x} >>> ({r.randint(0, 70)} + z)",
            7: f"{x} &&& {y}", 8: f"{x} ||| {y}", 9: f"{x} ^^^ {y}",
            10: f"({x} % 1000) ^ {r.randint(0, 40)}", 11: f"Nat.gcd {x} {y}", 12: f"min {x} {y}", 13: f"max {x} {y}",
            14: f"Nat.log2 {x}", 15: f"if {x} < {y} then {x} else {y} + 1", 16: f"Nat.succ {x}", 17: f"Nat.pred {x}",
            18: f"(UInt64.ofNat {x}).toNat", 19: f"(UInt64.ofNat {x} + UInt64.ofNat {y}).toNat", 20: f"(UInt64.ofNat {x} * UInt64.ofNat {y}).toNat",
            21: f"(UInt32.ofNat {x} * UInt32.ofNat {y}).toNat", 22: f"(USize.ofNat {x} - USize.ofNat {y}).toNat",
            23: f"if {x} == {y} then 1 else if {x} ≤ {y} then 2 else 3", 24: f"(if Nat.testBit {x} {r.randint(0, 70)} then 1 else 0) + {y}",
            25: f"({x} * {y}) % {r.choice(lits[:-4])} ", 26: f"Nat.lcm ({x} % 100000) ({y} % 100000)",
            27: f"(UInt8.ofNat {x}).toNat + (UInt16.ofNat {y}).toNat * 3",
        }[op]
        L.append(f"  let v{j} := {e}")
        pool.append(f"v{j}")
    # also an Int block
    ints = []
    for j in range(r.randint(2, 5)):
        x = r.choice(pool); y = r.choice(pool)
        sgn = r.choice(["", "-"])
        io = r.choice([f"(Int.ofNat {x} {r.choice(['+','-','*'])} {sgn}Int.ofNat {y})", f"(-(Int.ofNat {x}) / Int.ofNat ({y} % 1000 + 1))",
                       f"(-(Int.ofNat {x}) % Int.ofNat ({y} % 1000 + 1))", f"(Int.tdiv (-(Int.ofNat {x})) (Int.ofNat ({y} % 977)))", f"(Int.fmod (Int.ofNat {x}) (-(Int.ofNat ({y} % 977 + 1))))"])
        L.append(f"  let w{j} := {io}")
        ints.append(f"w{j}")
    # store in an Array Nat (word buffer), update, swap, read back
    L.append(f"  let mut arr : Array Nat := Array.mkEmpty {cap0}")
    L.append("  for i in [z:" + str(r.randint(3, 9)) + "] do")
    L.append(f"    arr := arr.push ({r.choice(pool)} + i * {r.choice(['1', '4294967296', '9223372036854775807', '18446744073709551615'])})")
    for j in range(r.randint(1, 4)):
        L.append(f"  arr := arr.set! ({r.randint(0, 6)}) ({r.choice(pool)} * {r.choice(pool)})")
        L.append(f"  arr := arr.swapIfInBounds ({r.randint(0, 6)}) ({r.randint(0, 6)})")
    L.append("  let arr2 := arr.map (fun x => x * x + 1)")
    ret = " + ".join([f"{p} % 1000000000000000000000000000057" for p in pool[-6:]] + [f"({q}).natAbs % 1000000000000000000000000000057" for q in ints] + [f"({q}).toNat" for q in ints[:2]]
                     + ["arr.foldl (fun h v => (h * 3 + v) % 1000000000000000000000000000057) 0", "arr2.foldl (· + ·) 0 % 1000000000000000000000000000057"])
    out = [f"def f{k} (n : Nat) : Nat := Id.run do\n" + "\n".join(L) + f"\n  return {ret}\n"]
    # a hash-style loop that crosses the word boundary part way
    m = r.choice(["6364136223846793005", "1103515245", "4294967311", "31", "1000003"])
    out.append(f"def g{k} (n : Nat) : Nat := Id.run do\n  let mut h := {r.randint(1, 99)} + n / 1000\n  let mut v : Array Nat := Array.mkEmpty {cap0 + 50}\n"
               f"  for i in [0:n % 60 + 5] do\n    h := (h * {m} + i) % {r.choice(['18446744073709551629', '36893488147419103232', '9223372036854775837', '340282366920938463463374607431768211297'])}\n"
               f"    v := v.push h\n    if i % 3 == 0 then v := v.set! (i / 3) (v[i / 3]! * 2 + h)\n  return h + v.foldl (fun a b => (a + b) % 1000000000000000000000000000057) 0\n")
    out.append(f"def h{k} (n : Nat) : Nat := g{k} n + f{k} (n + 1)\n")
    return "\n".join(out)

# ---------------------------------------------------------------- strings
FRAGS = ['"a"', '"é"', '"€"', '"😀"', '"abc"', '"héllo"', '"日本語"', '""', '"\\n"', '"ß"', '"a😀b"', '"\\x00x"', '"  trim me  "', '"1,2,,3"', '"x😀y😀z"', '"Ünï"', '"𝔘𝔫"']
CHARS = ["'a'", "'é'", "'€'", "'😀'", "'\\n'", "'z'", "'ß'", "' '", "','", "'日'", "'\\x00'", "'Z'", "'0'"]

def fam_str(r, k, cap0):
    L = ["  let z := n / 1000", f"  let mut s : String := {r.choice(FRAGS)}", f"  let mut t : String := {r.choice(FRAGS)}", "  let mut acc : Nat := z",
         "  let mut p : String.Pos.Raw := ⟨z⟩"]
    def S(): return r.choice(["s", "t", "(s ++ t)"])
    def pos():
        return r.choice(["p", "⟨acc % (s.utf8ByteSize + 2)⟩", f"⟨{r.randint(0, 9)}⟩", "⟨i⟩", "⟨s.utf8ByteSize⟩", "⟨s.utf8ByteSize + z⟩", "⟨i % (t.utf8ByteSize + 1)⟩", "(s.next p)", "(t.next ⟨i⟩)"])
    def dg(x):
        return f"acc := (acc * 131 + dig {x}) % 2305843009213693951"
    def st():
        j = r.randint(0, 42)
        a_ = {
            0: "s := s.push " + r.choice(CHARS), 1: "s := s ++ " + r.choice(FRAGS), 2: "t := t.push " + r.choice(CHARS),
            3: f"s := (s.drop {r.randint(0, 3)}).copy", 4: f"s := (s.take {r.randint(1, 9)}).copy", 5: f"t := t.dropRight {r.randint(0, 3)}",
            6: f"t := t.takeRight {r.randint(0, 6)}", 7: f"s := String.Pos.Raw.extract s {pos()} {pos()}", 8: f"t := String.Pos.Raw.extract {S()} {pos()} {pos()}",
            9: f"acc := acc + (s.get {pos()}).toNat", 10: f"acc := acc + (s.get {pos()}).toNat + 1",
            11: "p := s.next p", 12: "p := s.prev p", 13: f"p := ⟨(p.byteIdx + {r.randint(0, 5)}) % (s.utf8ByteSize + 3)⟩",
            14: f"s := s.set {pos()} {r.choice(CHARS)}", 15: f"s := s.modify {pos()} Char.toUpper",
            16: f"acc := acc + (s.posOf {r.choice(CHARS)}).byteIdx", 17: f"acc := acc + (s.revPosOf {r.choice(CHARS)}).elim 3 (·.byteIdx)",
            18: f"acc := acc + (s.splitOn {r.choice(['\",\"', '\"😀\"', '\"é\"', '\"ab\"', '\"\\\\n\"'])}).length", 19: f"s := s.replace {r.choice(['\"a\"', '\"😀\"', '\"é\"', '\"bc\"'])} {r.choice(FRAGS)}",
            20: "s := s.toUpper", 21: "t := t.toLower", 22: "s := s.trim", 23: f"acc := acc + (if s.startsWith {r.choice(FRAGS)} then 5 else 2) + (if t.endsWith {r.choice(FRAGS)} then 3 else 1)",
            24: "acc := acc + s.length * 3 + t.utf8ByteSize", 25: "s := String.mk s.toList.reverse", 26: f"s := s.map (fun c => if c.toNat % 2 == 0 then c else Char.ofNat (c.toNat + {r.randint(1, 300)}))",
            27: f"acc := acc + (if s.any (· == {r.choice(CHARS)}) then 1 else 0) + (if t.all Char.isAlpha then 2 else 0)",
            28: "s := s.capitalize", 29: f"t := (s.splitOn {r.choice(['\",\"', '\"x\"'])}).foldl (· ++ ·) \"\"", 30: "t := s",
            31: "s := s ++ s", 32: f"acc := acc + (s.posOf {r.choice(CHARS)}).byteIdx + 1", 33: "acc := acc + (s.front.toNat) + s.back.toNat",
            34: f"s := (s.takeWhile (· != {r.choice(CHARS)})).copy", 35: f"t := (t.dropWhile (· != {r.choice(CHARS)})).copy", 36: "acc := acc + (if s < t then 1 else 0) + (if s == t then 2 else 0)",
            37: "acc := acc + s.utf8ByteSize * 3", 38: "s := String.singleton (Char.ofNat (acc % 70000)) ++ s",
            39: f"s := (s.intercalate [t, {r.choice(FRAGS)}])", 40: "acc := acc + (t.toList.map Char.toNat).foldl (· + ·) 0",
            41: f"acc := acc + (s.get (s.next ⟨i⟩)).toNat + (t.get (t.prev ⟨i + {r.randint(0, 4)}⟩)).toNat", 42: "s := s.dropRightWhile Char.isWhitespace",
        }[j]
        return [a_, dg("s"), dg("t")] if j in (0, 1, 3, 4, 7, 14, 19, 26, 29, 31, 34) else [a_]
    for _ in range(r.randint(2, 4)):
        L.append(f"  for i in [z:{r.randint(2, 7)}] do")
        for _ in range(r.randint(2, 6)):
            for l in st(): L.append("    " + l)
        L.append("    if s.length > 40 then s := (s.take 20).copy")
    L += ["  acc := (acc * 131 + dig s) % 2305843009213693951", "  acc := (acc * 131 + dig t) % 2305843009213693951", "  return acc + p.byteIdx"]
    return f"def f{k} (n : Nat) : Nat := Id.run do\n" + "\n".join(L) + "\n"

# ---------------------------------------------------------------- arrays with aliasing, nested arrays, library functions
def fam_arr(r, k, cap0):
    L = ["  let z := n / 1000", f"  let mut a : Array Nat := Array.mkEmpty {cap0}", f"  let mut g : Array (Array Nat) := Array.mkEmpty {cap0 + 1}",
         f"  let mut u : Array UInt8 := Array.mkEmpty {cap0 + 2}", "  let mut acc := z"]
    L.append(f"  for i in [z:n % 30 + {r.randint(2, 6)}] do\n    a := a.push (i * {r.randint(2, 9)} + z)\n    u := u.push (UInt8.ofNat (i * 37))\n    g := g.push (Array.range (i % 4 + 1))")
    def st():
        j = r.randint(0, 24)
        return {
            0: "g := g.set! (i % (g.size + 1)) (g[i % (g.size + 1)]!.push i)",
            1: "let inner := g[i % (g.size + 1)]!\n    g := g.set! (i % (g.size + 1)) #[]\n    g := g.set! (i % (g.size + 1)) (inner.push acc)",
            2: "g := g.modify (i % (g.size + 1)) (·.push 77)", 3: "a := a.modify (i % (a.size + 1)) (· + 5)",
            4: "let h := g\n    g := g.map (·.push 1)\n    acc := acc + h.size * 5 + (h.foldl (fun s x => s + x.size) 0)",
            5: "a := a.reverse", 6: f"a := a.extract {r.randint(0, 2)} (a.size - {r.randint(0, 2)})", 7: "a := a ++ a.map (· * 2)",
            8: "a := a.qsort (· < ·)", 9: "a := a.filter (· % 3 != 0)", 10: "acc := acc + (a.foldl (· + ·) 0) % 1000 + a.size",
            11: "a := (a.zip u).map fun (x, y) => x + y.toNat", 12: "u := u.map (· + 7)", 13: "u := u.set! (i % (u.size + 1)) 200",
            14: "acc := acc + (u.foldl (fun s x => s + x.toNat) 0)", 15: "if a.size > 25 then a := a.extract 0 10",
            16: "let b := a.push 1\n    acc := acc + b.size + a.size + b[b.size - 1]!", 17: "a := a.insertIdxIfInBounds (i % (a.size + 1)) 9",
            18: "a := a.eraseIdxIfInBounds (i % (a.size + 1))", 19: "acc := acc + (a.contains 5).toNat + (if a.any (· > 20) then 3 else 0) + (a.findIdx? (· > 10)).getD 99",
            20: "a := a.mapIdx fun ix x => x + ix", 21: "u := u.swapIfInBounds 0 (u.size / 2)", 22: "if u.size > 20 then u := u.pop.pop",
            23: "let (l, rr) := a.partition (· % 2 == 0)\n    a := rr ++ l", 24: "a := a.modify 0 (· + acc)",
        }[j]
    for _ in range(r.randint(2, 4)):
        L.append(f"  for i in [z:{r.randint(2, 8)}] do")
        for _ in range(r.randint(2, 5)): L.append("    " + st())
    L.append("  return acc + (a.foldl (fun h v => (h * 31 + v) % 1000000007) 7) + a.size + u.foldl (fun h v => (h * 31 + v.toNat) % 1000000007) 5 + g.foldl (fun s x => s * 3 + x.size) 0")
    return f"def f{k} (n : Nat) : Nat := Id.run do\n" + "\n".join(L) + "\n"

FAMS = {"hoist": fam_hoist, "nat": fam_nat, "str": fam_str, "arr": fam_arr}

PRELUDE = """import Zempic

set_option linter.deprecated false
set_option linter.unusedVariables false

def dig (s : String) : Nat := s.foldl (fun h c => (h * 1000003 + c.toNat) % 2305843009213693951) (s.utf8ByteSize + 11)

"""

def generate(seed, nfun, fams, cfg):
    """cfg: 'd' default, 'r' or 'f' with fusion."""
    fns, roots = [], []
    cap = 3
    for k in range(nfun):
        r = random.Random(seed * 1000 + k)       # every function has its own stream
        fam = fams[(seed + k) % len(fams)] if len(fams) > 1 else fams[0]
        fam = r.choice(fams)
        src = FAMS[fam](r, k, cap)
        cap += 6
        fns.append(f"-- {fam}\n" + src)
        roots.append(f"h{k}" if fam == "nat" else f"f{k}")
    mod = f"Fz{seed}{cfg}"
    fuse = "set_option zempic.fuse true\n\n" if cfg in "rf" else ""
    calls = "\n".join(f"  for n in {NS} do IO.println s!\"{k} {{n}} {{{rt} n}}\"" for k, rt in enumerate(roots))
    lean = (PRELUDE.replace("import Zempic\n\n", "import Zempic\n\n" + fuse) + "\n\n".join(fns) +
            f"\n\ndef main : IO Unit := do\n{calls}\n\n#zempic {' '.join(roots)} to \"build/fuzz2/{mod}.hs\"\n")
    hcalls = "\n".join(f"  mapM_ (\\n -> putStrLn (\"{k} \" ++ show n ++ \" \" ++ show (z_{rt} (fromInteger n :: Natural)))) ns" for k, rt in enumerate(roots))
    hs = f"import {mod}\nimport Numeric.Natural (Natural)\n\nmain :: IO ()\nmain = do\n  let ns = {NS} :: [Integer]\n" + hcalls + "\n"
    return mod, lean, hs

def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, **kw)

def env():
    return dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.path.expanduser("~/.ghcup/bin") + ":" + os.environ["PATH"])

GHC_CLEAN = None
def plain_ghc(args):
    clean = ":".join(p for p in os.environ["PATH"].split(":") if "/.elan/" not in p)
    e = dict(os.environ, PATH=os.path.expanduser("~/.ghcup/bin") + ":" + clean)
    return run(["nice", "ghc", "-O1", "-i" + os.path.join(ROOT, "runtime"), "-rtsopts"] + args, cwd=ROOT, env=e, timeout=1800)

def one(seed, nfun, fams, cfgs="drf"):
    os.makedirs(OUT, exist_ok=True)
    want = None
    res = {}
    for cfg in cfgs:
        mod, lean, hs = generate(seed, nfun, fams, cfg)
        lp = os.path.join(OUT, mod + ".lean"); hp = os.path.join(OUT, mod + "Main.hs")
        open(lp, "w").write(lean); open(hp, "w").write(hs)
        if want is None:
            p = run(["nice", "lake", "env", "lean", "--run", lp], cwd=ROOT, env=env(), timeout=900)
            so = p.stdout.decode("utf8", "replace")
            if p.returncode != 0:
                return "lean", (so + p.stderr.decode("utf8", "replace"))[-1500:]
            want = [l for l in so.splitlines() if re.fullmatch(r"\d+ \d+ \d+", l)]
            if len(want) != nfun * len(NS):
                return "lean", f"{len(want)} result lines\n" + so[-800:]
        else:
            p = run(["nice", "lake", "env", "lean", lp], cwd=ROOT, env=env(), timeout=900)
            if p.returncode != 0:
                return "emit-" + cfg, (p.stdout + p.stderr).decode("utf8", "replace")[-1500:]
        exe = os.path.join(OUT, mod + ".exe")
        od = os.path.join(OUT, "o" + mod)
        if cfg == "r":
            g = run(["nice", os.path.join(ROOT, "tools", "zghc"), "-v0", "-i" + OUT, "-outputdir", od, hp, "-o", exe], cwd=ROOT, timeout=1800)
        else:
            g = plain_ghc(["-v0", "-i" + OUT, "-outputdir", od, hp, "-o", exe])
        if g.returncode != 0:
            return "ghc-" + cfg, (g.stdout + g.stderr).decode("utf8", "replace")[-2500:]
        h = run([exe], timeout=600)
        got = [l for l in h.stdout.decode("utf8", "replace").splitlines()]
        if h.returncode != 0 or got != want:
            bad = next((f"line {n}: lean `{a}` vs haskell `{b}`" for n, (a, b) in enumerate(zip(want, got)) if a != b),
                       f"length {len(want)} vs {len(got)}; rc {h.returncode}; {h.stderr.decode('utf8','replace')[-300:]}")
            return "mismatch-" + cfg, bad
        for f in (exe,):
            os.remove(f)
        subprocess.run(["rm", "-rf", od])
    return "ok", ""

if __name__ == "__main__":
    first = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    nfun = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    fams = (sys.argv[4] if len(sys.argv) > 4 else "hoist,nat,str,arr").split(",")
    cfgs = os.environ.get("FUZZ_CFGS", "drf")
    bad = 0
    for seed in range(first, first + count):
        # FUZZ_ROTATE=1: one configuration per seed (d, r, f in turn), three times as many seeds per hour
        kind, info = one(seed, nfun, fams, "drf"[seed % 3] if os.environ.get("FUZZ_ROTATE") else cfgs)
        print(f"seed {seed}: {kind}" + (f"  {info}" if info else ""), flush=True)
        bad += kind != "ok"
    print(f"fuzz2: {count - bad}/{count} seeds agreed with Lean")
    sys.exit(1 if bad else 0)
