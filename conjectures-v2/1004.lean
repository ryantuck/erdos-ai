import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Real

/--
Erdős Problem #1004 [Er85e]:

Let c > 0. If x is sufficiently large then does there exist n ≤ x such that the
values of φ(n+k) are all distinct for 1 ≤ k ≤ (log x)^c, where φ is the Euler
totient function?

This problem is OPEN (erdosproblems.com, snapshot accessed 2026-03-06).
The statement below asserts the implicit conjecture, i.e. the affirmative
answer to the question.

Erdős, Pomerance, and Sárközy [EPS87] proved that if φ(n+k) are all distinct
for 1 ≤ k ≤ K then K ≤ n / exp(c (log n)^{1/3}) for some constant c > 0.

See [945] for the analogous problem with the divisor function.

References:
- [Er85e] Erdős, P., Some problems and results in number theory. Number theory
  and combinatorics. Japan 1984 (Tokyo, Okayama and Kyoto, 1984) (1985), 65-87.
- [EPS87] Erdős, P., Pomerance, C., and Sárközy, A., On locally repeated values
  of arithmetic functions. III. Proc. Amer. Math. Soc. (1987), 1-7.
-/
theorem erdos_problem_1004 :
    ∀ c : ℝ, 0 < c →
      ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ →
        ∃ n : ℕ, n ≤ x ∧
          ∀ j k : ℕ, 1 ≤ j → j ≤ ⌊(Real.log (x : ℝ)) ^ c⌋₊ →
            1 ≤ k → k ≤ ⌊(Real.log (x : ℝ)) ^ c⌋₊ →
            j ≠ k → Nat.totient (n + j) ≠ Nat.totient (n + k) :=
  sorry

/--
Erdős Problem #1004, upper-bound variant [EPS87]:

Erdős, Pomerance, and Sárközy proved that if the values φ(n+k) are all
distinct for 1 ≤ k ≤ K then K ≤ n / exp(c (log n)^{1/3}) for some constant
c > 0.

The bound is asymptotic: as literally stated it fails for very small n (e.g.
n = 1, K = 2 has φ(2) = 1 ≠ 2 = φ(3) but 2 > 1/exp(0) = 1), so it is
formalized here for all sufficiently large n, with the constant c uniform.
-/
theorem erdos_problem_1004.variants.eps87_upper_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ K : ℕ,
        (∀ j k : ℕ, 1 ≤ j → j ≤ K → 1 ≤ k → k ≤ K →
          j ≠ k → Nat.totient (n + j) ≠ Nat.totient (n + k)) →
        (K : ℝ) ≤ (n : ℝ) / Real.exp (c * (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3)) :=
  sorry
