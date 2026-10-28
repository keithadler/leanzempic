import Zempic
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

def sumTo (acc : Nat) : Nat → Nat
  | 0 => acc
  | n+1 => sumTo (acc + n + 1) n

def sumL : List Nat → Nat → Nat
  | [], a => a
  | x::xs, a => let y := x + a; sumL xs y

def collatz (fuel n steps : Nat) : Nat :=
  match fuel with
  | 0 => steps
  | f+1 => if n ≤ 1 then steps else if n % 2 == 0 then collatz f (n / 2) (steps + 1) else collatz f (3 * n + 1) (steps + 1)

open Lean in
#zempic fact sumTo sumL collatz to "build/Examples.hs"
