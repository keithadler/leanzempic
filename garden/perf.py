#!/usr/bin/env python3
"""Garden performance: native Lean (C backend, compiled) against leanzempic+GHC at a large n.

    python3 garden/perf.py [name ...]     (needs the correctness run first: build/garden/<name>/Out)

Prints best-of-3 wall-clock seconds for each and the ratio (>1 means leanzempic is slower)."""
import os, subprocess, sys, time, re
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from programs import P
from run import ROOT, B, lake_env, lean, sysenv, split_imports, sh

# RTS options baked into the Haskell program (PERF_RTS="-A256m -O1g" to measure the tuned setting)
RTS = os.environ.get("PERF_RTS", "-A128m")

# program -> n to use (chosen so the native run takes roughly 0.05 to 2 s)
N = {
 "list_mergesort": 300000, "array_qsort": 300000, "hashmap": 3000000, "struct_update": 5000000,
  "string_build": 1000000, "state_monad": 3000000, "tuples": 5000000,
 "closures": 1000000, "bignum": 3000, "gcd_pow": 2000000, "uint64_hash": 3000000, "bytearray": 5000000,
 "for_loop_ctl": 30000000, "while_loop": 30000000, "option_chain": 5000000, 
 "int_arith": 3000000, "float_math": 5000000, "array_funcs": 2000000, "array_2d_loop": 600,
 "matrix_mul": 60, "string_split": 1000000, "string_chars": 1000000, "nat_repr": 500000,
 "list_funcs": 1000000, "typeclass": 3000000, "hashmap_str": 1500000, "hashset": 2000000,
 "functor_tree": 200000, "array_misc": 3000, "uint_conv": 30000000, "nested_loops_break": 8000,
 "list_misc": 3000, "deriving": 3000000, "sum_type": 3000000, "prod_arrays": 300000,
 "shared_rare_write": 20000, "shared_always_write": 10000, "shared_twice": 1000000,
 "string_sort_unique": 300000,  "int_repr": 1000000, "parser_monad": 1000000,
 "subtype_index": 15000000, "usize_loop": 15000000, "mutual_rec": 3000, "wf_recursion": 1000000,
}

def native(name, n):
    d = os.path.join(B, name)
    imps, body = split_imports(P[name])
    open(f"{d}/native.lean", "w").write("\n".join(imps) + "\n" + body +
        "\n\ndef main (args : List String) : IO Unit := IO.println (entry (args.headD \"1\").toNat!)\n")
    rc, out = sh(f"{lean} -c {d}/native.c {d}/native.lean", env=lake_env)
    if rc != 0: return None, out[:200]
    leanc = lean.replace("/bin/lean", "/bin/leanc")
    rc, out = sh(f"{leanc} -O3 -o {d}/native {d}/native.c", env=lake_env)
    return (None, out[:200]) if rc != 0 else (f"{d}/native", "")

def hs(name):
    d = os.path.join(B, name)
    open(f"{d}/PMain.hs", "w").write("import Out\nimport System.Environment\nmain :: IO ()\nmain = do\n  (n : _) <- getArgs\n  print (z_entry (fromInteger (read n)))\n")
    if os.path.exists(f"{d}/pm"): os.remove(f"{d}/pm")  # a changed RTS option alone does not relink
    rc, out = sh(f"ghc -O2 -rtsopts '-with-rtsopts={RTS}' -i{ROOT}/runtime -i{d} -outputdir {d}/op -o {d}/pm {d}/PMain.hs +RTS -M6g -RTS", env=sysenv)
    return (None, out[:200]) if rc != 0 else (f"{d}/pm", "")

def best(cmd, n, reps=3):
    b, res = 1e9, ""
    for _ in range(reps):
        t = time.time(); r = subprocess.run([cmd, str(n)], capture_output=True, text=True, env=sysenv, timeout=20); dt = time.time() - t
        b = min(b, dt); res = r.stdout.strip()
    return b, res

def one(name):
    n = N[name]
    nb, e1 = native(name, n)
    hb, e2 = hs(name)
    if not nb or not hb: return name, n, None, None, None, "build: " + (e1 or e2)
    try:
        t1, r1 = best(nb, n); t2, r2 = best(hb, n)
    except subprocess.TimeoutExpired:
        return name, n, None, None, None, 'timed out (>20 s); lower n'
    return name, n, t1, t2, r1 == r2 and r1 != "", ""

if __name__ == "__main__":
    names = sys.argv[1:] or [k for k in N if os.path.isdir(os.path.join(B, k, "Out"))]
    with ThreadPoolExecutor(1) as ex: res = list(ex.map(one, names))
    print(f"{'program':22} {'n':>9} {'lean C':>8} {'zempic':>8} {'ratio':>6}  same")
    rows = []
    for name, n, t1, t2, same, err in res:
        if t1 is None: print(f"{name:22} {n:>9}  {err[:100]}"); continue
        rows.append((t2 / t1, name))
        print(f"{name:22} {n:>9} {t1:8.3f} {t2:8.3f} {t2/t1:6.2f}  {'yes' if same else 'NO'}")
