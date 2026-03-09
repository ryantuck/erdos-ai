import Mathlib.Data.Nat.Totient

open Nat

/--
Erdős Problem #1003 [Er85e]:

Are there infinitely many solutions to φ(n) = φ(n+1), where φ is the Euler
totient function?

Erdős says that, presumably, for every k ≥ 1 the equation
φ(n) = φ(n+1) = ⋯ = φ(n+k) has infinitely many solutions.

Erdős, Pomerance, and Sárközy proved that the number of n ≤ x with
φ(n) = φ(n+1) is at most x / exp((log x)^{1/3}).
-/
theorem erdos_problem_1003 :
    Set.Infinite {n : ℕ | Nat.totient n = Nat.totient (n + 1)} :=
  sorry
