#!/usr/bin/env python3
"""Garden driver: for each program in programs.py, run it under native Lean, compile it with
leanzempic + GHC, and compare. Prints one line per program.

    python3 garden/run.py [name ...]        (default: all)

Statuses: OK (outputs equal), NATIVE (my program does not run under Lean), EMIT (leanzempic cannot
compile it; the message is shown), GHC (generated Haskell does not compile), DIFF (outputs differ),
RUNERR (the Haskell program crashed)."""
import os, subprocess, sys, re, json
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from programs import P

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
B = os.path.join(ROOT, "build", "garden")
NS = [0, 1, 2, 5, 10, 25]

def sh(cmd, env=None, cwd=ROOT, timeout=600):
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True, cwd=cwd, env=env, timeout=timeout)
    return r.returncode, r.stdout + r.stderr

lake_env = dict(os.environ)
for line in subprocess.run(["lake", "env", "printenv"], capture_output=True, text=True, cwd=ROOT).stdout.splitlines():
    if "=" in line:
        k, v = line.split("=", 1)
        if k in ("LEAN_PATH", "LEAN_SYSROOT", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"): lake_env[k] = v
lean = subprocess.run(["lake", "env", "which", "lean"], capture_output=True, text=True, cwd=ROOT).stdout.strip()
sysenv = dict(os.environ)
sysenv["PATH"] = ":".join(p for p in os.environ["PATH"].split(":") if "elan" not in p)

def split_imports(src):
    imps = [l for l in src.splitlines() if l.startswith("import ")]
    body = "\n".join(l for l in src.splitlines() if not l.startswith("import "))
    return imps, body

def one(name):
    d = os.path.join(B, name); os.makedirs(d, exist_ok=True)
    imps, body = split_imports(P[name])
    head = "import Zempic\n" + "\n".join(imps) + "\n"
    prn = "\n".join(f'  IO.println s!"{n} {{entry {n}}}"' for n in NS)
    open(f"{d}/{name}.lean", "w").write(head + body + "\n\ndef main : IO Unit := do\n" + prn + "\n")
    open(f"{d}/emit.lean", "w").write(head + body + f'\n\n#zempic entry to "build/garden/{name}/Out.hs"\n')
    rc, out = sh(f"{lean} --run {d}/{name}.lean", env=lake_env)
    want = "\n".join(l for l in out.splitlines() if re.match(r"^\d+ \d+$", l.strip())).strip()
    if rc != 0 or not want.startswith("0 "):
        return name, "NATIVE", out.strip().splitlines()[:2]
    rc, out = sh(f"{lean} {d}/emit.lean", env=lake_env)
    if rc != 0 or "wrote" not in out:
        msgs = [l.strip() for l in out.splitlines() if l.strip()]
        i = next((k for k, l in enumerate(msgs) if "unsupported" in l), 0)
        return name, "EMIT", msgs[i:i + 4]
    prn_hs = "\n".join(f'  putStrLn ("{n} " ++ show (z_entry {n}))' for n in NS)
    open(f"{d}/Main.hs", "w").write("import Out\nimport Numeric.Natural\nmain :: IO ()\nmain = do\n" + prn_hs + "\n")
    rc, out = sh(f"ghc -O2 -i{ROOT}/runtime -i{d} -outputdir {d}/o -o {d}/m {d}/Main.hs", env=sysenv)
    if rc != 0:
        errs = [l for l in out.splitlines() if "error" in l.lower()]
        i = next((k for k, l in enumerate(out.splitlines()) if "error" in l.lower()), 0)
        return name, "GHC", out.splitlines()[i:i + 4]
    rc, got = sh(f"{d}/m", env=sysenv)
    if rc != 0:
        return name, "RUNERR", got.strip().splitlines()[:2]
    if got.strip() != want:
        return name, "DIFF", [f"lean: {want.splitlines()}", f"hs:   {got.strip().splitlines()}"]
    return name, "OK", []

if __name__ == "__main__":
    names = sys.argv[1:] or sorted(P)
    with ThreadPoolExecutor(4) as ex:
        res = list(ex.map(one, names))
    counts = {}
    for name, st, info in res:
        counts[st] = counts.get(st, 0) + 1
        print(f"{st:7} {name}")
        for l in info: print(f"          {l[:200]}")
    print(counts)
    json.dump([(n, s, i) for n, s, i in res], open(os.path.join(B, "results.json"), "w"), indent=1)
