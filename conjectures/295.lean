import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Rat.Cast.Defs

open BigOperators Finset

/--
Erdős Problem #295 [ErGr80]:

Let N ≥ 1 and let k(N) denote the smallest k such that there exist distinct integers
N ≤ n₁ < n₂ < ⋯ < nₖ with 1/n₁ + 1/n₂ + ⋯ + 1/nₖ = 1.

Is it true that k(N) − (e−1)·N → ∞ as N → ∞?

Erdős and Straus proved −c < k(N) − (e−1)·N ≪ N / log N for some constant c > 0.
-/
theorem erdos_problem_295 :
    ∀ M : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ n) →
        (∀ n ∈ S, 0 < n) →
        ∑ n ∈ S, (1 : ℚ) / ↑n = 1 →
        (S.card : ℝ) - (Real.exp 1 - 1) * ↑N ≥ M :=
  sorry
