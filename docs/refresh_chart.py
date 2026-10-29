#!/usr/bin/env python3
"""Re-measure every row of the benchmark chart and redraw it. Run this after any change that can move
performance, and commit the new docs/chart-data.json, bench-chart.svg and bench-chart.png with it.

    python3 docs/refresh_chart.py            (about 15 minutes; keep the machine quiet)

Each row is the Haskell output's run time over compiled Lean's, once with default settings (no list
fusion, -A128m) and once with the recommended ones (list fusion on, -A256m -O1g). One native time per row
(the faster of the measurements). Nothing here is typed in by hand: every number comes from a run in this
script, and a row whose answers differ from Lean's aborts the refresh."""
import datetime, json, os, re, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
SYS = ":".join(p for p in os.environ["PATH"].split(":") if "elan" not in p)
TUNED_RTS = "-A256m -O1g"

# garden programs: name -> (label, n)
GARDEN = {
    "float_math": ("Float loop", 5000000), "int_arith": ("Int arithmetic", 3000000),
    "functor_tree": ("Tree map and sum", 200000), "struct_update": ("Record update loop", 5000000),
    "list_mergesort": ("List merge sort", 300000), "hashmap": ("HashMap inserts", 3000000),
    "string_chars": ("String iteration", 1000000), "list_funcs": ("List functions", 1000000),
    "array_funcs": ("Array map/filter/fold", 2000000), "array_misc": ("Shared array, insertion sort", 3000),
    "uint64_hash": ("List of UInt8, hashed", 3000000), "tuples": ("Tuple-state fold", 5000000),
    "option_chain": ("Option chain", 5000000),
}
# examples/Arrays.lean: index in its function list -> (label, n)
ARRAYS = {0: ("Sieve (Bool array)", 5000000), 1: ("Prefix sums (Nat array)", 10000000),
          2: ("Array map and fold", 3000000), 3: ("Reverse by swaps", 2000000), 4: ("Push and pop stack", 5000000)}

def run(cmd, env=None, check=True):
    e = dict(os.environ); e.update(env or {})
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True, env=e)
    if check and r.returncode != 0:
        sys.exit(f"command failed: {cmd}\n{r.stdout[-800:]}{r.stderr[-800:]}")
    return r.stdout + r.stderr

def best(cmd, reps=3):
    """Best wall-clock seconds of reps runs, and the output."""
    b, out = 1e9, ""
    for _ in range(reps):
        t = time.time()
        r = subprocess.run(cmd, shell=True, capture_output=True, text=True, env=dict(os.environ, PATH=SYS))
        b = min(b, time.time() - t); out = r.stdout.strip()
    return b, out

def garden(cfg):
    """Garden rows for one configuration: name -> (native s, haskell s)."""
    fuse = "1" if cfg == "tuned" else "0"
    names = " ".join(GARDEN)
    out = run(f"python3 garden/run.py {names}", {"GARDEN_FUSE": fuse, "GARDEN_OPT": "-O1"})
    if "'OK': %d" % len(GARDEN) not in out:
        sys.exit("garden correctness failed:\n" + out[-1500:])
    rts = TUNED_RTS if cfg == "tuned" else "-A128m"
    out = run(f"python3 garden/perf.py {names}", {"PERF_RTS": rts})
    d = {}
    for l in out.splitlines():
        m = re.match(r"^(\w+)\s+(\d+)\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)\s+(yes|NO)", l)
        if m:
            if m.group(6) != "yes": sys.exit(f"answers differ for {m.group(1)}")
            d[m.group(1)] = (float(m.group(3)), float(m.group(4)))
    missing = [n for n in GARDEN if n not in d]
    if missing: sys.exit(f"no timing for {missing}:\n{out[-1500:]}")
    return d

def main():
    print("building ...", flush=True)
    run("lake build Zempic bench fusion arrays aesbench")
    for target in ("Main", "FusionMain", "ArraysMain"):
        for stale in (target, target + "T"):                      # a changed RTS option alone does not relink
            if os.path.exists(f"build/{stale}"): os.remove(f"build/{stale}")
        run(f"bench/build.sh {target}", {"PATH": SYS})                                  # default settings
        run(f"bench/build.sh {target} {target}T", {"PATH": SYS, "ZEMPIC_RTS": TUNED_RTS})  # tuned RTS
    rows = []
    print("garden, default settings ...", flush=True); plain = garden("plain")
    print("garden, recommended settings ...", flush=True); tuned = garden("tuned")
    for k, (label, n) in GARDEN.items():
        nat = min(plain[k][0], tuned[k][0])
        rows.append({"label": label, "native_s": nat, "default_s": plain[k][1], "tuned_s": tuned[k][1],
                     "default": round(plain[k][1] / nat, 3), "tuned": round(tuned[k][1] / nat, 3)})
    print("bench rows ...", flush=True)
    def bench_row(label, native_cmd, hs_cmd, hs_cmd_t):
        nt, nout = best(native_cmd); h, hout = best(hs_cmd); ht, htout = best(hs_cmd_t)
        if not (nout and nout == hout == htout): sys.exit(f"answers differ for {label}: {nout!r} {hout!r} {htout!r}")
        rows.append({"label": label, "native_s": nt, "default_s": h, "tuned_s": ht,
                     "default": round(h / nt, 3), "tuned": round(ht / nt, 3)})
    bench_row("Nat sum loop", ".lake/build/bin/bench 0", "build/Main 0", "build/MainT 0")
    bench_row("Fused list pipeline", ".lake/build/bin/fusion lean 20000000", "build/FusionMain fused 20000000",
              "build/FusionMainT fused 20000000")
    for i, (label, n) in ARRAYS.items():
        bench_row(label, f".lake/build/bin/arrays {n} {i}", f"build/ArraysMain {n} {i}", f"build/ArraysMainT {n} {i}")
    out = run("bench/aes/run.sh 300000", {"PATH": SYS})
    m = re.search(r"Lean C: ([\d.]+) s, leanzempic: ([\d.]+) s", out)
    if not m: sys.exit("AES run failed:\n" + out[-800:])
    nat, hs = float(m.group(1)), float(m.group(2))
    rows.append({"label": "Proved AES-256", "native_s": nat, "default_s": hs, "tuned_s": hs,
                 "default": round(hs / nat, 3), "tuned": round(hs / nat, 3)})
    meta = {"commit": run("git rev-parse --short HEAD").strip(), "date": datetime.date.today().isoformat(),
            "machine": "Apple M3", "dirty": bool(run("git status --porcelain").strip())}
    old = {}
    try: old = {r["label"]: r for r in json.load(open("docs/chart-data.json")).get("rows", [])}
    except Exception: pass
    json.dump({"meta": meta, "rows": rows}, open("docs/chart-data.json", "w"), indent=1)
    os.chdir("docs"); run("python3 make_chart.py"); os.chdir(ROOT)
    print(f"\nchart refreshed at {meta['commit']} ({meta['date']}). Changes against the previous data:")
    for r in sorted(rows, key=lambda r: r["tuned"]):
        o = old.get(r["label"])
        mark = ""
        if o is None: mark = "  (new row)"
        elif abs(r["tuned"] - o["tuned"]) / max(o["tuned"], 1e-9) > 0.10:
            mark = f"  (was {o['tuned']:.2f})"
        print(f"  {r['label']:32} default {r['default']:6.2f}  recommended {r['tuned']:6.2f}{mark}")

if __name__ == "__main__":
    main()
