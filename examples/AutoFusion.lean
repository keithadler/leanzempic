import Zempic

set_option zempic.fuse true

-- Ordinary Lean list code. No Zempic.Fuse in sight.
def pipeAuto (n : Nat) : Nat :=
  ((List.range n).map (fun x => x * x % 1000)).filter (fun y => y % 3 != 0) |>.foldl (· + ·) 0

def main (args : List String) : IO Unit :=
  IO.println (pipeAuto ((args.headD "5000000").toNat!))

#zempic pipeAuto to "build/AutoFusion.hs"
