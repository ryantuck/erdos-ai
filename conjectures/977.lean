import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

noncomputable section

/-- The greatest prime divisor of n, or 0 if n ≤ 1. -/
def greatestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactors.sup id

/--
Erdős Problem #977 [Er65b]:
If P(m) denotes the greatest prime divisor of m, is it true that
P(2^n - 1) / n → ∞ as n → ∞?

This was proved by Stewart [St13], who showed that
P(2^n - 1) ≫ n^{1 + 1/(104 log log n)} for all sufficiently large n.
-/
theorem erdos_problem_977 :
    Tendsto (fun n : ℕ => (greatestPrimeFactor (2 ^ n - 1) : ℝ) / (n : ℝ))
      atTop atTop :=
  sorry

end
