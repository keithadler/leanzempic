#!/usr/bin/env python3
"""Draw bench-chart.svg and bench-chart.png from chart-data.json (needs rsvg-convert for the PNG).

Each row is the run time of the Haskell output divided by the run time of compiled Lean (the faster of
two measurements), once with default settings and once with the recommended ones (list fusion on,
-A256m -O1g). Left of the line is faster than Lean's C backend."""
import json, math, subprocess
data = json.load(open("chart-data.json"))
meta = data.get("meta", {}) if isinstance(data, dict) else {}
rows = sorted(data["rows"] if isinstance(data, dict) else data, key=lambda r: r["tuned"])
W, rh = 1600, 62
top = 250
H = top + rh * len(rows) + 150
x0, x1 = 700, 1520
lo, hi = math.log10(0.07), math.log10(40)
X = lambda r: x0 + (math.log10(r) - lo) / (hi - lo) * (x1 - x0)
BG, FG, MUTE, GRID = "#0f172a", "#e2e8f0", "#94a3b8", "#334155"
FAST, SLOW, FAST_D, SLOW_D = "#2dd4bf", "#fb923c", "#2dd4bf55", "#fb923c55"

def label(r):
    if abs(r - 1) < 0.06: return "level"
    return f"{1/r:.1f}x faster" if r < 1 else (f"{r:.1f}x slower" if r < 10 else f"{r:.0f}x slower")

o = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" font-family="Helvetica Neue, Helvetica, Arial, sans-serif">',
     f'<rect width="{W}" height="{H}" fill="{BG}"/>',
     f'<text x="80" y="92" font-size="46" font-weight="700" fill="{FG}">Lean through GHC, against Lean\'s C backend</text>',
     f'<text x="80" y="136" font-size="26" fill="{MUTE}">Run time relative to compiled Lean. Left of the line is faster.</text>',
     # legend
     f'<rect x="80" y="166" width="38" height="14" rx="3" fill="{FAST_D}"/><rect x="80" y="166" width="38" height="14" rx="3" fill="none" stroke="{FAST}" stroke-width="1.5" opacity=".6"/>',
     f'<text x="130" y="180" font-size="23" fill="{MUTE}">default settings</text>',
     f'<rect x="360" y="162" width="38" height="22" rx="3" fill="{FAST}"/>',
     f'<text x="410" y="180" font-size="23" fill="{FG}">recommended: list fusion on, -A256m -O1g</text>']
for r, lab in [(0.1, "10x faster"), (0.3, "3x"), (1, "same"), (3, "3x"), (10, "10x slower"), (30, "30x")]:
    x = X(r)
    o.append(f'<line x1="{x:.1f}" y1="{top-12}" x2="{x:.1f}" y2="{top+rh*len(rows)}" stroke="{FG if r==1 else GRID}" stroke-width="{3 if r==1 else 1.5}"/>')
    o.append(f'<text x="{x:.1f}" y="{top-24}" font-size="20" text-anchor="middle" fill="{FG if r==1 else MUTE}">{lab}</text>')
for i, row in enumerate(rows):
    y = top + i * rh
    o.append(f'<text x="660" y="{y+rh/2+8:.1f}" font-size="26" text-anchor="end" fill="{FG}">{row["label"]}</text>')
    one = X(1)
    for k, (key, h, dy, fillF, fillS, bold) in enumerate([("default", 14, 9, FAST_D, SLOW_D, False), ("tuned", 22, 26, FAST, SLOW, True)]):
        r = row[key]
        xr = X(r)
        col = (fillF if r < 1 else fillS)
        if abs(r - 1) < 0.06:
            o.append(f'<rect x="{one-4:.1f}" y="{y+dy:.1f}" width="8" height="{h}" fill="{FG}"/>')
            tx, anc = one + 18, "start"
        else:
            xa, xb = min(xr, one), max(xr, one)
            o.append(f'<rect x="{xa:.1f}" y="{y+dy:.1f}" width="{xb-xa:.1f}" height="{h}" rx="3" fill="{col}"/>')
            tx, anc = (xr - 10, "end") if r < 1 else (xr + 10, "start")
        if bold:
            # inside the bar, dark text, when the bar is long on the faster side; else beside it
            if r < 1 and (one - xr) > 190:
                o.append(f'<text x="{one-12:.1f}" y="{y+dy+17:.1f}" font-size="21" font-weight="700" text-anchor="end" fill="{BG}">{label(r)}</text>')
            else:
                c = FAST if r < 0.94 else (FG if abs(r-1) < 0.06 else SLOW)
                o.append(f'<text x="{tx:.1f}" y="{y+dy+17:.1f}" font-size="21" font-weight="700" text-anchor="{anc}" fill="{c}">{label(r)}</text>')
        elif abs(row["default"] - row["tuned"]) / max(row["tuned"], 1e-9) > 0.12:
            o.append(f'<text x="{tx:.1f}" y="{y+dy+12:.1f}" font-size="16" text-anchor="{anc}" fill="{MUTE}">{label(r)}</text>')
fy = top + rh * len(rows) + 52
stamp = f" Measured {meta['date']} at commit {meta['commit']}." if meta else ""
o.append(f'<text x="80" y="{fy}" font-size="21" fill="{MUTE}">Apple M3, Lean 4.29.1, GHC 9.14.1 -O2, best of 3, pure programs only.{stamp}</text>')
o.append(f'<text x="80" y="{fy+30}" font-size="21" fill="{MUTE}">Not everything improves: list merge sort slows with fusion, and a shared array mutated in a loop is still about 5x behind.</text>')
o.append(f'<text x="80" y="{fy+78}" font-size="26" font-weight="700" fill="{FG}">leanzempic</text>')
o.append(f'<text x="262" y="{fy+78}" font-size="26" fill="{MUTE}">Apache-2.0  github.com/keithadler/leanzempic</text>')
o.append('</svg>')
open("bench-chart.svg", "w").write("\n".join(o))
subprocess.run(["rsvg-convert", "-w", str(W), "-h", str(H), "bench-chart.svg", "-o", "bench-chart.png"], check=True)
print("wrote bench-chart.png", W, H)
