import Mathlib.Data.Nat.Factors
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Basic

open Finset Classical

noncomputable section

/-!
# Erdős Problem #452

Let ω(n) count the number of distinct prime factors of n. What is the size
of the largest interval I ⊆ [x, 2x] such that ω(n) > log log n for all n ∈ I?

Erdős [Er37] proved that the density of integers n with ω(n) > log log n is 1/2.
The Chinese remainder theorem implies there is such an interval with
|I| ≥ (1+o(1)) log x / (log log x)².
It could be true that there is such an interval of length (log x)^k for
arbitrarily large k.
-/

/-- The number of distinct prime factors of n (ω(n) in analytic number theory). -/
noncomputable def erdos452_omega (n : ℕ) : ℕ :=
  (Nat.primeFactorsList n).toFinset.card

/--
Erdős Problem #452 [ErGr80, p.90]:

For every k > 0, for all sufficiently large x, there exists an interval
[a, a + L] ⊆ [x, 2x] with L ≥ (log x)^k such that ω(n) > log log n
for all integers n in [a, a + L].
-/
theorem erdos_problem_452 :
    ∀ k : ℝ, 0 < k →
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      ∃ a L : ℕ, x ≤ a ∧ a + L ≤ 2 * x ∧
        (Real.log (x : ℝ)) ^ k ≤ (L : ℝ) ∧
        ∀ n ∈ Finset.Icc a (a + L),
          (erdos452_omega n : ℝ) > Real.log (Real.log (n : ℝ)) :=
  sorry

end
