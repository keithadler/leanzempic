#!/usr/bin/env python3
"""Count how often the hoisted workers of a garden program actually run.

    python3 tools/hoist_count.py NAME [N]      (after: python3 garden/run.py NAME)
    python3 tools/hoist_count.py --check       (builds the programs in YES and NO below and checks them)

A hoisted loop (`f_h`, see "Hoisted buffers" in SOUNDNESS.md) only runs when the array it is handed is a live
unboxed buffer; otherwise the wrapper falls back to the ordinary code and the program still gives the right
answer, so a garden program can pass without ever running the hoisted worker. This script wraps every `_h`
worker of the generated Fast and Exact modules in a counter, runs the program at N (default 25) and prints the
number of worker calls per module. A program meant to exercise a hoisted loop must report a count above zero in
the Fast module. Prints `NAME fast=<calls> exact=<calls> ro=<calls>`; exits 1 if all are zero. Workers that
write the array (`_h`) and workers of functions that only read it (`_hr`, see `hoistReadOnly`) are counted apart:
`fast` and `exact` are the writing ones, `ro` the read-only ones in both modules."""
import os, re, shutil, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sysenv = dict(os.environ); sysenv["PATH"] = ":".join(p for p in os.environ["PATH"].split(":") if "elan" not in p)

# Programs whose hoisted workers must run (a scan that stops finding them loses the speedup silently: the
# answers stay right) and programs that must run as the ordinary code (a scan that hoists them gives wrong answers).
YES = ["hoist_qsort_uint8", "hoist_qsort_uint64", "hoist_qsort_usize", "hoist_qsort_nat", "hoist_qsort_bool",
       "hoist_set_uint8", "hoist_set_nat", "hoist_set_bool", "hoist_shared_uint32", "hoist_shared_nat",
       "hoist_shared_bool", "hoist_cell_loop_uint8", "hoist_cell_loop_nat", "hoist_cell_two_uint8",
       "hoist_cell_two_nat", "hoist_cell_second_uint8", "hoist_cell_second_nat", "hoist_cell_move_uint8",
       "hoist_cell_move_nat", "hoist_cell_movejp_uint8", "hoist_cell_movejp_nat", "hoist_cell_jpok_uint8",
       "hoist_cell_jpok_nat", "hoist_map_nat"]
# Programs whose read-only workers (`_hr`) must run, and programs that must have none.
RO_YES = ["hoist_fold_nat"]
RO_NO = ["hoist_map_mixed", "hoist_fold_alias"]
NO = ["hoist_escape_uint8", "hoist_escape_nat", "hoist_escape_bool", "hoist_push_uint8", "hoist_push_nat",
      "hoist_push_bool", "hoist_pop_uint8", "hoist_pop_nat", "hoist_pop_bool", "hoist_persist_uint8",
      "hoist_persist_nat", "hoist_persist_bool", "hoist_join_uint8", "hoist_join_nat", "hoist_join_bool",
      "hoist_cell_push_uint8", "hoist_cell_push_nat",
      "hoist_cell_pop_uint8", "hoist_cell_persist_uint8", "hoist_cell_call_uint8", "hoist_cell_join_uint8",
      "hoist_cell_twice_uint8", "hoist_cell_jpshare_uint8", "hoist_map_mixed", "hoist_fold_alias"]

# the subset CI checks (GARDEN_SET=ci)
RO_YES_CI = ["hoist_fold_nat"]
RO_NO_CI = ["hoist_fold_alias"]
YES_CI = ["hoist_qsort_uint8", "hoist_set_nat", "hoist_set_bool", "hoist_cell_loop_uint8", "hoist_cell_second_uint8",
          "hoist_cell_move_nat", "hoist_cell_jpok_uint8", "hoist_shared_bool", "hoist_map_nat"]
NO_CI = ["hoist_escape_uint8", "hoist_push_nat", "hoist_cell_push_uint8", "hoist_cell_join_uint8", "hoist_join_uint8", "hoist_map_mixed", "hoist_fold_alias"]

def count(name, n="25"):
    """(fast calls, exact calls, answer, read-only calls) of the hoisted workers of garden program `name` at size n."""
    src = f"{ROOT}/build/garden/{name}"; dst = f"{ROOT}/build/hcount/{name}"
    shutil.rmtree(dst, ignore_errors=True); os.makedirs(f"{dst}/Out", exist_ok=True)
    shutil.copy(f"{src}/Out.hs", dst)
    open(f"{dst}/HCount.hs", "w").write("""module HCount where
import Data.IORef
import System.IO.Unsafe
fastCtr, exactCtr :: IORef Int
fastCtr = unsafePerformIO (newIORef 0)
{-# NOINLINE fastCtr #-}
exactCtr = unsafePerformIO (newIORef 0)
{-# NOINLINE exactCtr #-}
roCtr :: IORef Int
roCtr = unsafePerformIO (newIORef 0)
{-# NOINLINE roCtr #-}
tick :: IORef Int -> a -> a
tick r x = unsafePerformIO (modifyIORef' r (+ 1) >> return x)
{-# NOINLINE tick #-}
""")
    for mod, ctr in (("Fast", "fastCtr"), ("Exact", "exactCtr")):
        text = open(f"{src}/Out/{mod}.hs").read()
        out = []; wrappers = []
        for l in text.split("\n"):
            m = re.match(r"^(\S+_hr?) ::(.*)$", l)
            if m: out.append(f"{m.group(1)}0 ::{m.group(2)}"); sig = (m.group(1), m.group(2)); continue
            m = re.match(r"^(\S+_hr?) (!hb.*) =$", l)
            if m:
                args = [a.lstrip("!") for a in m.group(2).split()]
                out.append(f"{m.group(1)}0 {m.group(2)} =")
                c = "roCtr" if m.group(1).endswith("_hr") else ctr
                wrappers.append(f"{sig[0]} ::{sig[1]}\n{sig[0]} {' '.join(args)} = HCount.tick HCount.{c} ({sig[0]}0 {' '.join(args)})\n")
                continue
            out.append(l)
        body = "\n".join(out).replace("import Zempic.Runtime", "import qualified HCount\nimport Zempic.Runtime", 1)
        open(f"{dst}/Out/{mod}.hs", "w").write(body + "\n" + "\n".join(wrappers))
    open(f"{dst}/Main.hs", "w").write("""import Out
import HCount
import Data.IORef
main :: IO ()
main = do
  print (z_entry %s)
  f <- readIORef fastCtr
  e <- readIORef exactCtr
  r <- readIORef roCtr
  putStrLn ("fast=" ++ show f ++ " exact=" ++ show e ++ " ro=" ++ show r)
""" % n)
    r = subprocess.run(f"ghc -O1 -i{ROOT}/runtime -i{dst} -outputdir {dst}/o -o {dst}/m {dst}/Main.hs", shell=True,
                       capture_output=True, text=True, env=sysenv, cwd=dst)
    if r.returncode != 0: sys.exit(r.stdout[-1500:] + r.stderr[-1500:])
    r = subprocess.run(f"{dst}/m", shell=True, capture_output=True, text=True, env=sysenv)
    lines = r.stdout.strip().splitlines()
    m = re.match(r"fast=(\d+) exact=(\d+) ro=(\d+)", lines[-1])
    return int(m.group(1)), int(m.group(2)), lines[0], int(m.group(3))

if __name__ == "__main__":
    if sys.argv[1] == "--check":
        # YES/NO lists above; builds the garden programs first
        ci = os.environ.get("GARDEN_SET") == "ci"
        yes, no = (YES_CI, NO_CI) if ci else (YES, NO)
        ryes, rno = (RO_YES_CI, RO_NO_CI) if ci else (RO_YES, RO_NO)
        names = list(dict.fromkeys(yes + no + ryes + rno))
        r = subprocess.run([sys.executable, f"{ROOT}/garden/run.py"] + names, capture_output=True, text=True)
        if not r.stdout.strip().endswith("{'OK': %d}" % len(names)):
            sys.exit("garden programs did not all agree:\n" + r.stdout[-1500:])
        bad = []
        for nm in names:
            fast, exact, _, ro = count(nm)
            if nm in yes and fast == 0: bad.append(f"{nm}: fast={fast} (expected > 0)")
            if nm in no and fast > 0: bad.append(f"{nm}: fast={fast} (expected 0)")
            if nm in ryes and ro == 0: bad.append(f"{nm}: ro={ro} (expected > 0)")
            if nm in rno and ro > 0: bad.append(f"{nm}: ro={ro} (expected 0)")
        if bad: sys.exit("hoisting expectations failed:\n" + "\n".join(bad))
        print(f"ok hoisting ({len(yes)} programs run their hoisted loops, {len(no)} run the ordinary code; "
              f"{len(ryes)} run read-only hoisted loops, {len(rno)} none)")
        sys.exit(0)
    fast, exact, ans, ro = count(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "25")
    print(sys.argv[1], f"fast={fast} exact={exact} ro={ro}", "(answer " + ans + ")")
    sys.exit(0 if (fast, exact, ro) != (0, 0, 0) else 1)
