import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

/--
Erdős Problem #387 [ErGr76b,p.351] [Er78g,p.315] [ErGr80,p.74]:

Is there an absolute constant c > 0 such that, for all 1 ≤ k < n, the
binomial coefficient C(n, k) has a divisor in (cn, n]?

Erdős once conjectured the stronger statement with c = 1 - k/n (i.e., a
divisor in (n-k, n]), but this was disproved by Schinzel. Guy reports that
Erdős conjectured the statement holds for any c < 1 when n is sufficiently
large.
-/
theorem erdos_problem_387 :
    ∃ c : ℝ, 0 < c ∧
      ∀ n k : ℕ, 1 ≤ k → k < n →
        ∃ d : ℕ, d ∣ Nat.choose n k ∧
          c * (n : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ (n : ℝ) :=
  sorry
