#!/usr/bin/env python3
"""RTS-option sweep over the built real-world programs (run `run.py build` first).

    python3 bench/realworld/rts.py REPS PROGRAMS LABEL=@/CONFIG[::RTS FLAGS] ...

PROGRAMS is a comma list or `all`; `@` stands for out/<program>, CONFIG is `default` or `recommended`.
Runs are interleaved, repeated REPS times; each cell is the fewest instructions retired (billions), the
largest peak resident set (MB) and the least CPU seconds, from /usr/bin/time -l. Flags after `::` are
passed as `+RTS ... -RTS` and override the -with-rtsopts baked into the binary. Example:

    python3 bench/realworld/rts.py 3 all rec=@/recommended/m low='@/recommended/m::-A64m'"""
import json, os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sizes = json.load(open(f"{HERE}/sizes.json"))
ALL = ["binarytrees", "const_fold", "deriv", "qsort", "rbmap", "rbmap_checkpoint", "unionfind"]
reps = int(sys.argv[1]); progs = ALL if sys.argv[2] == "all" else sys.argv[2].split(",")
cfgs = []
for a in sys.argv[3:]:
    label, rest = a.split("=", 1); exe, _, fl = rest.partition("::"); cfgs.append((label, exe, fl.split()))

def run(exe, flags, n):
    cmd = ["/usr/bin/time", "-l", exe, str(n)] + (["+RTS"] + flags + ["-RTS"] if flags else [])
    r = subprocess.run(cmd, capture_output=True, text=True)
    ins = int(re.search(r"(\d+)\s+instructions retired", r.stderr).group(1))
    rss = int(re.search(r"(\d+)\s+maximum resident", r.stderr).group(1)) / 1048576
    m = re.search(r"([\d.]+)\s+real\s+([\d.]+)\s+user\s+([\d.]+)\s+sys", r.stderr)
    return ins, rss, float(m.group(2)) + float(m.group(3)), r.stdout.strip()

for p in progs:
    res = {l: [] for l, _, _ in cfgs}
    for _ in range(reps):
        for l, e, fl in cfgs: res[l].append(run(e.replace("@", f"{HERE}/out/{p}"), fl, sizes[p]))
    outs = {x[3] for v in res.values() for x in v}
    cells = [f"{l}: {min(x[0] for x in v) / 1e9:.2f}G {max(x[1] for x in v):.0f}MB {min(x[2] for x in v):.2f}s" for l, v in res.items()]
    print(p.ljust(17), " | ".join(cells), "" if len(outs) == 1 else "OUTPUT DIFFERS", flush=True)
