#!/usr/bin/env python3
"""Real-world comparison driver.   python3 bench/realworld/run.py build [name ...]
                                    python3 bench/realworld/run.py bench [name ...]
build: native Lean (C, leanc -O3), leanzempic default (no fusion, -A128m) and recommended (zempic.fuse, -A256m -O1g).
bench: interleaved best-of-5 wall/CPU/peak RSS (via /usr/bin/time -l), output compared.  Writes out/results.json."""
import os, subprocess, sys, json, time, re, resource, shutil
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
OUT = f"{HERE}/out"
NAMES = ["binarytrees", "const_fold", "deriv", "qsort", "rbmap", "unionfind"]
CANDIDATES = NAMES + ["rbmap_checkpoint", "nat_repr"]
SIZES = json.load(open(f"{HERE}/sizes.json")) if os.path.exists(f"{HERE}/sizes.json") else {}
REPS = int(os.environ.get("REPS", "5"))
CFG = {"default": ("", "-A128m"), "recommended": ("set_option zempic.fuse true\n", "-A256m -O1g")}

def sh(cmd, env=None, cwd=ROOT, timeout=1200):
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True, cwd=cwd, env=env, timeout=timeout)
    return r.returncode, r.stdout + r.stderr

lake_env = dict(os.environ)
for line in subprocess.run(["lake", "env", "printenv"], capture_output=True, text=True, cwd=ROOT).stdout.splitlines():
    if "=" in line:
        k, v = line.split("=", 1)
        if k in ("LEAN_PATH", "LEAN_SYSROOT", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"): lake_env[k] = v
lean = subprocess.run(["lake", "env", "which", "lean"], capture_output=True, text=True, cwd=ROOT).stdout.strip()
leanc = lean.replace("/bin/lean", "/bin/leanc")
sysenv = dict(os.environ); sysenv["PATH"] = ":".join(p for p in os.environ["PATH"].split(":") if "elan" not in p)

def build(name):
    d = f"{OUT}/{name}"; os.makedirs(d, exist_ok=True)
    body = open(f"{HERE}/src/{name}.lean").read()
    res = {}
    open(f"{d}/native.lean", "w").write(body + '\n\ndef main (args : List String) : IO Unit :=\n  IO.println (entry (args.headD "1").toNat!)\n')
    rc, out = sh(f"{lean} -c {d}/native.c {d}/native.lean", env=lake_env)
    if rc == 0: rc, out = sh(f"{leanc} -O3 -o {d}/native {d}/native.c", env=lake_env)
    res["native"] = "OK" if rc == 0 else "FAIL: " + out[-600:]
    for cfg, (opt, rts) in CFG.items():
        c = f"{d}/{cfg}"; os.makedirs(c, exist_ok=True)
        open(f"{c}/emit.lean", "w").write("import Zempic\n" + opt + body + f'\n\n#zempic entry to "{c}/Out.hs"\n')
        rc, out = sh(f"{lean} {c}/emit.lean", env=lake_env)
        if rc != 0 or "wrote" not in out:
            msgs = [l.strip() for l in out.splitlines() if l.strip()]
            i = next((k for k, l in enumerate(msgs) if "unsupported" in l), 0)
            res[cfg] = "EMIT: " + " | ".join(msgs[i:i+4]); continue
        open(f"{c}/Main.hs", "w").write("import Out\nimport System.Environment\nmain :: IO ()\nmain = do\n  (n : _) <- getArgs\n  print (z_entry (fromInteger (read n)))\n")
        if os.path.exists(f"{c}/m"): os.remove(f"{c}/m")
        rc, out = sh(f"ghc -O2 -rtsopts '-with-rtsopts={rts}' -i{ROOT}/runtime -i{c} -outputdir {c}/o -o {c}/m {c}/Main.hs +RTS -M6g -RTS", env=sysenv)
        if rc != 0:
            L = out.splitlines(); i = next((k for k, l in enumerate(L) if "error" in l.lower()), 0)
            res[cfg] = "GHC: " + " | ".join(L[i:i+5]); continue
        res[cfg] = "OK"
    return name, res

def timed(cmd):
    """One run under /usr/bin/time -l; returns (wall, user+sys cpu, peak MB, stdout)."""
    t = time.time()
    r = subprocess.run(["/usr/bin/time", "-l"] + cmd, capture_output=True, text=True, env=sysenv, timeout=120)
    wall = time.time() - t
    m = re.search(r"([\d.]+)\s+real\s+([\d.]+)\s+user\s+([\d.]+)\s+sys", r.stderr)
    rss = re.search(r"(\d+)\s+maximum resident set size", r.stderr)
    return (float(m.group(1)) if m else wall, float(m.group(2)) + float(m.group(3)) if m else None,
            int(rss.group(1)) / 1048576 if rss else None, r.stdout.strip(), r.returncode)

def bench(name, status):
    n = str(SIZES[name]); d = f"{OUT}/{name}"
    exes = {"native": f"{d}/native"}
    for cfg in CFG:
        if status[name].get(cfg) == "OK": exes[cfg] = f"{d}/{cfg}/m"
    runs = {k: [] for k in exes}
    for _ in range(REPS):                       # interleaved
        for k, e in exes.items(): runs[k].append(timed([e, n]))
    row = {"n": SIZES[name], "load": os.getloadavg()}
    for k, rs in runs.items():
        outs = {r[3] for r in rs}
        row[k] = {"wall": min(r[0] for r in rs), "cpu": min(r[1] for r in rs), "mb": max(r[2] for r in rs),
                  "all_wall": [round(r[0], 3) for r in rs], "out": sorted(outs)[0][:60], "stable": len(outs) == 1,
                  "rc": [r[4] for r in rs]}
    return row

if __name__ == "__main__":
    mode = sys.argv[1]; names = sys.argv[2:] or NAMES
    sp = f"{OUT}/status.json"
    if mode == "build":
        os.makedirs(OUT, exist_ok=True)
        st = json.load(open(sp)) if os.path.exists(sp) else {}
        for n in names:
            _, st[n] = build(n); print(n, st[n], flush=True)
        json.dump(st, open(sp, "w"), indent=1)
    elif mode == "bench":
        st = json.load(open(sp)); rp = f"{OUT}/results.json"
        res = json.load(open(rp)) if os.path.exists(rp) else {}
        for n in names:
            res[n] = bench(n, st); print(n, json.dumps(res[n]), flush=True)
            json.dump(res, open(rp, "w"), indent=1)
