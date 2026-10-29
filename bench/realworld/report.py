#!/usr/bin/env python3
"""Print the results table (markdown) from out/results.json."""
import json, os
H = os.path.dirname(os.path.abspath(__file__)); r = json.load(open(f"{H}/out/results.json"))
C = "https://github.com/leanprover/lean4/blob/f72c35b3f637c8c6571d353742168ab66cc22c00/tests/bench/"
print("| program | n | native wall s (CPU) | default wall s (CPU), ratio | recommended wall s (CPU), ratio | peak MB native / default / recommended | output identical |")
print("|---|---|---|---|---|---|---|")
for p, v in r.items():
    n = v["native"]; d = v["default"]; t = v["recommended"]
    same = all(x["out"] == n["out"] and x["stable"] for x in (d, t))
    print(f"| [{p}]({C}{p}.lean) | {v['n']} | {n['wall']:.2f} ({n['cpu']:.2f}) | {d['wall']:.2f} ({d['cpu']:.2f}), {d['wall']/n['wall']:.2f}x | "
          f"{t['wall']:.2f} ({t['cpu']:.2f}), {t['wall']/n['wall']:.2f}x | {n['mb']:.0f} / {d['mb']:.0f} / {t['mb']:.0f} | {'yes' if same else 'NO'} |")
print("\nload averages at the start of each program's runs (1/5/15 min): " + "; ".join(f"{p} {v['load'][0]:.1f}/{v['load'][1]:.1f}/{v['load'][2]:.1f}" for p, v in r.items()))
