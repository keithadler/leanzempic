import Zempic

-- Lean-idiomatic pipeline (Lean specializes each stage; intermediate lists are built).
def pipeLean (n : Nat) : Nat :=
  ((List.range n).map (fun x => x * x % 1000)).filter (fun y => y % 3 != 0) |>.foldl (· + ·) 0

-- Same pipeline through the fusible combinators.
def pipeFused (n : Nat) : Nat :=
  Zempic.Fuse.foldl (fun a b => a + b) 0
    (Zempic.Fuse.filter (fun y => y % 3 != 0)
      (Zempic.Fuse.map (fun x => x * x % 1000) (Zempic.Fuse.range n)))

def main (args : List String) : IO Unit := do
  let n := (args.getD 1 "5000000").toNat!
  match args.headD "lean" with
  | "fused" => IO.println (pipeFused n)
  | _ => IO.println (pipeLean n)

#zempic pipeFused pipeLean to "build/Fusion.hs"
