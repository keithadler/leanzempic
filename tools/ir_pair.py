#!/usr/bin/env python3
"""Ir (valgrind) comparison of one garden program: native Lean (C backend, leanc -O3) against the Haskell
output, both at one n. Linux fallback for the instructions-retired numbers; needs a prior
`python3 garden/run.py NAME` so that build/garden/NAME/Out.hs exists, and an ir.sh that prints the best-of-3
callgrind instruction count (IR_SH, default /home/user/ir.sh).

    python3 tools/ir_pair.py NAME N [RTS options, default "-A256m -O1g"]
    OUT_DIR=/dir/with/an/older/Out.hs for the emitter side of the A/B
    RT_DIR=/path/to/other/runtime TAG=base python3 tools/ir_pair.py NAME N   # A/B against another runtime
"""
import os, subprocess, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "garden"))
from programs import P
from run import ROOT, B, lake_env, lean, sysenv, split_imports, sh

name, n = sys.argv[1], sys.argv[2]
rts = sys.argv[3] if len(sys.argv) > 3 else "-A256m -O1g"
IR = os.environ.get("IR_SH", "/home/user/ir.sh")
RT = os.environ.get("RT_DIR", f"{ROOT}/runtime")  # runtime to build against (the baseline checkout's, for a before number)
TAG = os.environ.get("TAG", "op")
HD = os.environ.get("OUT_DIR", None)  # directory holding Out.hs (default: the garden build directory of NAME)
d = os.path.join(B, name)
os.makedirs(d, exist_ok=True)
hd = HD or d
imps, body = split_imports(P[name])
open(f"{d}/native.lean", "w").write("\n".join(imps) + "\n" + body +
    "\n\ndef main (args : List String) : IO Unit := IO.println (entry (args.headD \"1\").toNat!)\n")
rc, out = sh(f"{lean} -c {d}/native.c {d}/native.lean", env=lake_env); assert rc == 0, out
leanc = lean.replace("/bin/lean", "/bin/leanc")
rc, out = sh(f"{leanc} -O3 -o {d}/native {d}/native.c", env=lake_env); assert rc == 0, out
open(f"{hd}/PMain.hs", "w").write("import Out\nimport System.Environment\nmain :: IO ()\nmain = do\n  (n : _) <- getArgs\n  print (z_entry (fromInteger (read n)))\n")
if os.path.exists(f"{hd}/pm"): os.remove(f"{hd}/pm")
rc, out = sh(f"ghc -O2 -rtsopts '-with-rtsopts={rts}' -i{RT} -i{hd} -outputdir {hd}/{TAG} -o {hd}/pm {hd}/PMain.hs +RTS -M2g -RTS", env=sysenv); assert rc == 0, out
a = subprocess.run([f"{d}/native", n], capture_output=True, text=True).stdout.strip()
b = subprocess.run([f"{hd}/pm", n], capture_output=True, text=True).stdout.strip()
ni = int(subprocess.run([IR, f"{d}/native", n], capture_output=True, text=True).stdout.strip())
hi = int(subprocess.run([IR, f"{hd}/pm", n], capture_output=True, text=True).stdout.strip())
print(f"{name:16} n={n:>8} native {ni/1e6:10.1f} M  zempic {hi/1e6:10.1f} M  ratio {hi/ni:5.2f}  same={a==b} ({a})")
