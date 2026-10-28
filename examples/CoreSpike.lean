import Zempic

/-- Factorial. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Sum of `1..n` onto `acc`. -/
def sumTo (acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => sumTo (acc + n + 1) n

/-- Collatz steps with a fuel bound. -/
def collatz (fuel n steps : Nat) : Nat :=
  match fuel with
  | 0 => steps
  | f + 1 =>
    if n ≤ 1 then steps
    else if n % 2 == 0 then collatz f (n / 2) (steps + 1)
    else collatz f (3 * n + 1) (steps + 1)

#zempic fact sumTo collatz to "build/CoreSpike.hs" mode core
