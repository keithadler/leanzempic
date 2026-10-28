# Benchmarks (2026-10-28, Apple M3, Lean 4.29.1, GHC 9.14.1 -O2)

Best of 3 wall-clock, same source functions (`examples/Bench.lean`).

| Workload | Lean C backend | leanzempic (Any + Natural) | Hand-typed Haskell (Word) |
|---|---|---|---|
| sum loop, 2e8 iterations | 0.42 s | 1.39 s | 0.12 s user |
| collatz over 1..1e6 | 0.33 s | 1.88 s | 0.16 s |
| build + sum 5e6-element list | 0.08 s | 0.29 s | not written |

Outputs agree on all three.

**Reading:** v0.1 is 3.5x to 5.7x slower than Lean. Cause: every value is a boxed
`Any`, and `Natural` is arbitrary precision, so GHC cannot unbox or run
worker/wrapper. The hand-typed column is not generated; it is the ceiling that
typed emission (small-Nat fast path with overflow check, `Word` for fixed-width,
real field types) is aiming at: about 2.5x to 3.5x faster than Lean on the two
loops. Fusion is untested.

Reproduce: `lake build bench && cd bench && ghc -O2 -i../runtime -i../build -o ../build/hsbench Main.hs`.
