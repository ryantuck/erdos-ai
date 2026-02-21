import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Finset

/--
Erdős Problem #286 [ErGr80, p.33] (Proved by Croot [Cr01]):

Let k ≥ 2. Is it true that there exists an interval I of width (e-1+o(1))k
and integers n₁ < ⋯ < nₖ ∈ I such that
  1 = 1/n₁ + ⋯ + 1/nₖ?

The answer is yes. For every ε > 0, for all sufficiently large k, there
exist k distinct positive integers in an interval of width at most
(e - 1 + ε)k whose reciprocals sum to 1.
-/
theorem erdos_problem_286 :
    ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∃ S : Finset ℕ,
      S.card = k ∧
      (∀ n ∈ S, 0 < n) ∧
      (∃ a : ℕ, ∀ n ∈ S, a ≤ n ∧ (n : ℝ) ≤ (a : ℝ) + (Real.exp 1 - 1 + ε) * (k : ℝ)) ∧
      S.sum (fun n => (1 : ℚ) / ↑n) = 1 :=
  sorry
