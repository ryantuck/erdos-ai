import Mathlib.Data.Nat.Totient

open Nat

/--
Erdős Problem #1003 [Er85e]:

Are there infinitely many solutions to φ(n) = φ(n+1), where φ is the Euler
totient function?

This problem is OPEN (erdosproblems.com, page edition 31 October 2025).

Erdős [Er85e] says that, presumably, for every k ≥ 1 the equation
φ(n) = φ(n+1) = ⋯ = φ(n+k) has infinitely many solutions.

Erdős, Pomerance, and Sárközy [EPS87] proved that the number of n ≤ x with
φ(n) = φ(n+1) is at most x / exp((log x)^{1/3}).

See [946] for the analogous question with the divisor function.
Related OEIS sequence: A001274.

References:
- [Er85e] Erdős, P., Some problems and results in number theory. Number theory
  and combinatorics. Japan 1984 (Tokyo, Okayama and Kyoto, 1984) (1985), 65-87.
- [EPS87] Erdős, P., Pomerance, C., and Sárközy, A., On locally repeated values
  of arithmetic functions. III. Proc. Amer. Math. Soc. (1987), 1-7.
-/
theorem erdos_problem_1003 :
    Set.Infinite {n : ℕ | Nat.totient n = Nat.totient (n + 1)} :=
  sorry

/--
Erdős Problem #1003, chain variant [Er85e]:

Erdős says that, presumably, for every k ≥ 1 the equation
φ(n) = φ(n+1) = ⋯ = φ(n+k) has infinitely many solutions.

The condition is encoded as φ(n) = φ(n+i) for all i ≤ k (the case i = 0 is
trivial); the case k = 1 recovers the main statement above.
-/
theorem erdos_problem_1003.variants.consecutive :
    ∀ k : ℕ, 1 ≤ k →
      Set.Infinite {n : ℕ | ∀ i : ℕ, i ≤ k → Nat.totient n = Nat.totient (n + i)} :=
  sorry
