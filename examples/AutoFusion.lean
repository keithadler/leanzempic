import Zempic

set_option zempic.fuse true

-- Ordinary Lean list code. No Zempic.Fuse in sight.
/-- Ordinary list code; `zempic.fuse` rewrites it into a fused pipeline. -/
def pipeAuto (n : Nat) : Nat :=
  ((List.range n).map (fun x => x * x % 1000)).filter (fun y => y % 3 != 0) |>.foldl (· + ·) 0

/-- Print `pipeAuto` of the argument. -/
def main (args : List String) : IO Unit :=
  IO.println (pipeAuto ((args.headD "5000000").toNat!))

#zempic pipeAuto to "build/AutoFusion.hs"
