#!/usr/bin/env python3
"""Differential fuzzer: random Lean programs, run by Lean and through leanzempic, compared.

    python3 tools/fuzz.py [first_seed] [how_many_seeds] [functions_per_seed]

For each seed it writes build/fuzz/Fuzz<seed>.lean (random functions plus a main that prints their
results), runs it with `lean --run`, compiles the same file's #zempic output with GHC, runs that,
and requires the two outputs to be identical and non-empty. A mismatch keeps the files and prints
the seed so the failure can be replayed and minimized.

The programs are loops with several mutable variables (Nat, UInt8, UInt32, Array Nat, String),
conditionals and nested loops, so they exercise loop state in MProd cells, fixed-width wraparound,
array updates (and with them the ownership analysis), and string building. They also take
snapshots and forks of the array and the string (`snap := arr`, then mutating both), which is what
makes an unsound in-place update visible. An earlier generator without those never caught a
deliberately broken ownership analysis.
"""
import os, random, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "build", "fuzz")
NS = [0, 1, 7, 33, 100]
# Even seeds alias whole arrays and strings (`snap := arr`), which makes the loop array shared and
# keeps the analysis conservative. Odd seeds never alias, so the loop array stays uniquely owned and
# the in-place path is actually used; they still fork (`let f := arr.set! ..`, then use both).
ALIAS = True

def stmts(r, depth, indent, loopvar, arrOK=True):
    """A list of random statements; loopvar names the innermost loop counter."""
    pad = "  " * indent
    out = []
    for _ in range(r.randint(2, 6)):
        k = r.randint(0, 28)
        i = loopvar
        if k == 0:   out.append(f"{pad}a := (a * {r.randint(2,9)} + {i}) % {r.choice([97,1009,100003])}")
        elif k == 1: out.append(f"{pad}b := b * {r.randint(1,250)} + {i}.toUInt8")
        elif k == 2: out.append(f"{pad}c := (c ^^^ (c <<< {r.randint(1,31)})) + {i}.toUInt32")
        elif k == 3: out.append(f"{pad}c := (c >>> {r.randint(1,31)}) ||| (c <<< {r.randint(1,31)})")
        elif k == 4: out.append(f"{pad}arr := arr.push (a % {r.choice([10,1000,65537])})")
        elif k == 5: out.append(f"{pad}if arr.size > 0 then arr := arr.set! ({i} % arr.size) (a % {r.randint(2,999)})")
        elif k == 6: out.append(f"{pad}t := t + arr.getD ({i} % {r.randint(1,9)}) 0")
        elif k == 7: out.append(f"{pad}s := s.push (Char.ofNat (97 + a % 26))")
        elif k == 8: out.append(f"{pad}t := t + s.length * {r.randint(1,5)}")
        elif k == 9: out.append(f"{pad}a := a + b.toNat")
        elif k == 10: out.append(f"{pad}t := t + c.toUInt8.toNat")
        elif k == 11: out.append(f"{pad}if arr.size > 1 then arr := arr.swapIfInBounds 0 (arr.size - 1)")
        elif k == 12: out.append(f"{pad}if arr.size > 3 then arr := arr.pop")
        elif k == 13: out.append(f"{pad}b := b / ({r.randint(0,5)} : UInt8)")
        elif k == 14: out.append(f"{pad}t := t + (c % {r.randint(1,9)}).toNat")
        elif k in (17, 20) and not ALIAS: out.append(f"{pad}a := a + {i} % {r.randint(2,11)}")
        elif k == 17: out.append(f"{pad}snap := arr")
        elif k == 18: out.append(f"{pad}t := t + snap.size * 7 + snap.getD ({i} % 5) 0")
        elif k == 19: out.append(f"{pad}snap := snap.push (a % 100)")
        elif k == 20: out.append(f"{pad}ss := s")
        elif k == 21: out.append(f"{pad}t := t + ss.length * 11 + (ss.toList.map Char.toNat).foldl (· + ·) 0")
        elif k == 22: out.append(f"{pad}ss := ss.push 'z'")
        elif k == 23 and arrOK: out.append(f"{pad}if snap.size > 0 then snap := snap.set! ({i} % snap.size) (b.toNat)")
        elif k in (24, 25, 26, 27, 28) and not ALIAS: out.append(f"{pad}a := a + {i} % {r.randint(2,11)}")
        elif k in (24, 25, 26, 27, 28):
            n = r.randint(0, 10**6)   # unique names, so forks never shadow each other
            if k == 24:
                out.append(f"{pad}let f{n} := arr.set! ({i} % (arr.size + 1)) (a % 50)")
                out.append(f"{pad}t := t + f{n}.getD 0 0 + arr.getD 0 0 + f{n}.size")
            elif k == 25:
                out.append(f"{pad}let f{n} := arr.push (a % 7)")
                out.append(f"{pad}t := t + f{n}.size * 3 + arr.size + f{n}.getD ({i} % 4) 0")
            elif k == 26:
                out.append(f"{pad}let f{n} := s.push 'q'")
                out.append(f"{pad}t := t + f{n}.length + s.length * 2")
            elif k == 27:
                out.append(f"{pad}let f{n} := arr.pop")
                out.append(f"{pad}t := t + f{n}.size + arr.getD ({i} % 3) 0")
            else:
                out.append(f"{pad}let f{n} := arr.swapIfInBounds 0 ({i} % (arr.size + 1))")
                out.append(f"{pad}t := t + f{n}.getD 0 0 + arr.getD 0 0")
        elif k == 15 and depth < 2:
            cond = r.choice(["a % 3 == 0", "b < 100", "c % 2 == 1", "arr.size % 2 == 0", "t % 5 < 2"])
            out.append(f"{pad}if {cond} then")
            out += stmts(r, depth + 1, indent + 1, loopvar)
            if r.random() < 0.5:
                out.append(f"{pad}else")
                out += stmts(r, depth + 1, indent + 1, loopvar)
        elif k == 16 and depth < 2:
            v = f"j{depth}"
            out.append(f"{pad}for {v} in [0:{r.randint(1,4)}] do")
            out += stmts(r, depth + 1, indent + 1, v)
        else: out.append(f"{pad}a := a + {i} % {r.randint(2,11)}")
    return out

def post_forks(r):
    """After the loop: fork the (by then, linearly built) array and string and use both versions."""
    opts = [
        ["  let g{n} := arr.set! 0 (a % 50)", "  t := t + g{n}.getD 0 0 + arr.getD 0 0 + g{n}.size"],
        ["  let g{n} := arr.push (a % 7)", "  t := t + g{n}.size * 3 + arr.size + g{n}.getD 1 0"],
        ["  let g{n} := arr.pop", "  t := t + g{n}.size + arr.getD 0 0"],
        ["  let g{n} := arr.swapIfInBounds 0 (arr.size / 2)", "  t := t + g{n}.getD 0 0 + arr.getD 0 0"],
        ["  let g{n} := s.push 'q'", "  t := t + g{n}.length + s.length * 2"],
        ["  let g{n} := (arr.set! 0 1).push 2", "  t := t + g{n}.size + arr.size + g{n}.getD 0 0 + arr.getD 0 0"],
    ]
    out = []
    for n in range(r.randint(1, 3)):
        for line in r.choice(opts):
            out.append(line.replace("{n}", str(n)))
    return out

def function(r, k):
    lines = [f"def f{k} (n : Nat) : Nat := Id.run do",
             f"  let mut a : Nat := {r.randint(0,50)}",
             f"  let mut b : UInt8 := {r.randint(0,255)}",
             f"  let mut c : UInt32 := {r.randint(1,4000000000)}",
             "  let mut arr : Array Nat := #[]",
             "  let mut s : String := \"\"",
             "  let mut snap : Array Nat := #[7]",   # not #[]: Lean merges two identical #[] into one shared array
             "  let mut ss : String := \"\"",
             "  let mut t : Nat := 0",
             f"  for i in [0:n % {r.randint(10,60)} + {r.randint(2,6)}] do"]
    lines += stmts(r, 0, 2, "i")
    if not ALIAS:
        lines += post_forks(r)
    lines.append("  return t + a + b.toNat + c.toNat + arr.foldl (· + ·) 0 + arr.size + s.length +"
                 " snap.foldl (· + ·) 0 + snap.size * 3 + ss.length * 5")
    return "\n".join(lines)

def generate(seed, nfun):
    global ALIAS
    ALIAS = seed % 2 == 0
    r = random.Random(seed)
    mod = f"Fuzz{seed}"
    fns = [function(r, k) for k in range(nfun)]
    roots = " ".join(f"f{k}" for k in range(nfun))
    calls = "\n".join(f"  for n in {NS} do IO.println s!\"{k} {{n}} {{f{k} n}}\"" for k in range(nfun))
    lean = ("import Zempic\n\n" + "\n\n".join(fns) +
            f"\n\ndef main : IO Unit := do\n{calls}\n\n#zempic {roots} to \"build/fuzz/{mod}.hs\"\n")
    hcalls = "\n".join(f"  mapM_ (\\n -> putStrLn (\"{k} \" ++ show n ++ \" \" ++ show (z_f{k} (fromIntegral n)))) ns" for k in range(nfun))
    hs = (f"import {mod}\nimport Numeric.Natural (Natural)\n\nmain :: IO ()\nmain = do\n"
          f"  let ns = {NS} :: [Integer]\n" + hcalls.replace("(fromIntegral n)", "(fromInteger n :: Natural)") + "\n")
    return mod, lean, hs

def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

def one(seed, nfun):
    os.makedirs(OUT, exist_ok=True)
    mod, lean, hs = generate(seed, nfun)
    lp = os.path.join(OUT, mod + ".lean")
    hp = os.path.join(OUT, mod + "Main.hs")
    open(lp, "w").write(lean)
    open(hp, "w").write(hs)
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
    p = run(["lake", "env", "lean", "--run", lp], cwd=ROOT, env=env, timeout=600)
    if p.returncode != 0 or not p.stdout.strip():
        return "lean", (p.stdout + p.stderr)[-1500:]
    # lean also prints warnings on stdout; the results are the `k n value` lines
    want = "\n".join(l for l in p.stdout.splitlines() if re.fullmatch(r"\d+ \d+ \d+", l))
    if not want:
        return "lean", p.stdout[-1500:]
    exe = os.path.join(OUT, mod + ".exe")
    g = run([os.path.join(ROOT, "tools", "zghc"), "-v0", "-i" + OUT, "-outputdir", os.path.join(OUT, "o" + str(seed)),
             hp, "-o", exe], cwd=ROOT, timeout=900)
    if g.returncode != 0:
        return "ghc", (g.stdout + g.stderr)[-2500:]
    h = run([exe], timeout=300)
    got = h.stdout.strip()
    if not got or got != want:
        wl, gl = want.split("\n"), got.split("\n")
        bad = next((f"line {n}: lean `{a}` vs haskell `{b}`" for n, (a, b) in enumerate(zip(wl, gl)) if a != b),
                   f"length {len(wl)} vs {len(gl)}")
        return "mismatch", bad
    return "ok", ""

if __name__ == "__main__":
    first = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    nfun = int(sys.argv[3]) if len(sys.argv) > 3 else 12
    bad = 0
    for seed in range(first, first + count):
        kind, info = one(seed, nfun)
        print(f"seed {seed}: {kind}" + (f"  {info}" if info else ""), flush=True)
        bad += kind != "ok"
    print(f"fuzz: {count - bad}/{count} seeds agreed with Lean")
    sys.exit(1 if bad else 0)
