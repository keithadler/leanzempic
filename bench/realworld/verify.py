#!/usr/bin/env python3
"""Independent check: decode each program's packed Nat at upstream's own argument and compare with the
upstream .expected.out file.  Prints OK/MISMATCH per program (uses out/<name>/native)."""
import os, re, subprocess
H = os.path.dirname(os.path.abspath(__file__)); B = 1 << 40
def digits(x):
    d = []
    while x: d.append(x % B); x //= B
    return d[::-1]
ok = True
for p in ["binarytrees", "const_fold", "deriv", "qsort", "rbmap", "rbmap_checkpoint", "unionfind"]:
    a = open(f"{H}/upstream/{p}.lean.args").read().split()[0]
    if p == "const_fold": a = "1"          # reps=1 reproduces upstream's single tree of depth 15
    got = int(subprocess.run([f"{H}/out/{p}/native", a], capture_output=True, text=True).stdout)
    exp = open(f"{H}/upstream/{p}.lean.expected.out").read() if os.path.exists(f"{H}/upstream/{p}.lean.expected.out") else None
    if p == "binarytrees":
        want = [int(x) for x in re.findall(r"check: (\d+)", exp)]       # stretch, 6 depths, long
        res = digits(got) == want
    elif p == "const_fold": res = digits(got) == [int(x) for x in exp.split()]   # upstream arg 15 = depth 15
    elif p == "deriv": res = digits(got) == [int(x) for x in re.findall(r"count: (\d+)", exp)]
    elif p == "qsort": res = got == int(a) ** 2 and exp.strip() == ""      # all n*n arrays sorted; upstream prints nothing
    elif p == "rbmap": res = got == int(exp.split()[0])
    elif p == "rbmap_checkpoint":     # no upstream expected file; "10001 10000" is upstream's own main run natively at "100000 10"
        res = digits(got) == [10001, 10000]
    elif p == "unionfind": res = got == int(exp.split()[1])
    else: res = None                                                         # no expected file upstream
    print(f"{p:12} arg {a:>6} packed->{'OK' if res else ('no upstream expected file' if res is None else 'MISMATCH')}")
