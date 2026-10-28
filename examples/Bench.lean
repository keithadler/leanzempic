import Zempic

/-- Sum loop. -/
def sumTo (acc : Nat) : Nat → Nat
  | 0 => acc
  | n+1 => sumTo (acc + n + 1) n

/-- Collatz steps with a fuel bound. -/
def collatz (fuel n steps : Nat) : Nat :=
  match fuel with
  | 0 => steps
  | f+1 =>
    if n ≤ 1 then steps
    else if n % 2 == 0 then collatz f (n / 2) (steps + 1)
    else collatz f (3 * n + 1) (steps + 1)

/-- Total Collatz steps over `1..i`. -/
def collatzAll (i acc : Nat) : Nat :=
  match i with
  | 0 => acc
  | k+1 => collatzAll k (acc + collatz 1000 (k+1) 0)

/-- A list of `n` small numbers. -/
def mkList (n : Nat) (acc : List Nat) : List Nat :=
  match n with
  | 0 => acc
  | k+1 => mkList k ((k * 7 % 13) :: acc)

/-- Sum of a list. -/
def sumL : List Nat → Nat → Nat
  | [], a => a
  | x::xs, a => sumL xs (a + x)

/-- Build and sum a list. -/
def listWork (n : Nat) : Nat := sumL (mkList n []) 0

/-- Workload selector: 0 sum loop, 1 collatz, otherwise list. -/
def runBench (which : Nat) : Nat :=
  match which with
  | 0 => sumTo 0 200000000
  | 1 => collatzAll 1000000 0
  | _ => listWork 5000000

/-- Run the workload named on the command line. -/
def main (args : List String) : IO Unit :=
  IO.println (runBench ((args.headD "2").toNat?.getD 2))

#zempic runBench to "build/Bench.hs"
