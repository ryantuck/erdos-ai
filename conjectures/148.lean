import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

open BigOperators Real Filter

/-!
# Erdős Problem #148

Let F(k) be the number of solutions to 1 = 1/n₁ + ⋯ + 1/nₖ where
1 ≤ n₁ < n₂ < ⋯ < nₖ are distinct positive integers.
Find good estimates for F(k).

The current best known bounds are
  2^{c^{k/log k}} ≤ F(k) ≤ c₀^{(1/5 + o(1))·2^k}
where c > 0 is some absolute constant and c₀ = 1.26408⋯ is the Vardi constant.
The lower bound is due to Konyagin [Ko14] and the upper bound to
Elsholtz and Planitzer [ElPl21].
-/

/-- F(k) is the number of k-element sets of positive integers
    whose unit fractions sum to 1: 1/n₁ + ⋯ + 1/nₖ = 1. -/
noncomputable def egyptianFractionCount (k : ℕ) : ℕ :=
  Set.ncard {S : Finset ℕ | S.card = k ∧ (∀ n ∈ S, 0 < n) ∧
    ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = 1}

/-- Konyagin lower bound [Ko14]:
    There exists an absolute constant c > 0 such that
    2^{c^{k/log k}} ≤ F(k) for all sufficiently large k. -/
theorem egyptianFractionCount_konyagin_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      (2 : ℝ) ^ (c ^ ((k : ℝ) / Real.log k)) ≤
        (egyptianFractionCount k : ℝ) :=
  sorry

/-- Elsholtz–Planitzer upper bound [ElPl21]:
    There exists a constant c₀ > 1 (the Vardi constant, c₀ ≈ 1.26408) such that
    for every ε > 0, F(k) ≤ c₀^{(1/5 + ε)·2^k} for all sufficiently large k. -/
theorem egyptianFractionCount_elsholtz_planitzer_upper_bound :
    ∃ c₀ : ℝ, 1 < c₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      (egyptianFractionCount k : ℝ) ≤
        c₀ ^ ((1 / 5 + ε) * (2 : ℝ) ^ (k : ℕ)) :=
  sorry

/-- Erdős Problem #148 [ErGr80, p.32]:
    Find good estimates for F(k), the number of representations of 1
    as a sum of exactly k distinct unit fractions.

    The open problem is to close the gap between the known bounds. This
    conjecture asserts that the correct order of magnitude is exponential
    in 2^k: there exist constants 1 < c₁ ≤ c₂ such that
    c₁^{2^k} ≤ F(k) ≤ c₂^{2^k} for all sufficiently large k.
    In particular, the Konyagin lower bound should be improvable to
    exponential in 2^k to match the Elsholtz–Planitzer upper bound. -/
theorem erdos_problem_148 :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ 1 < c₂ ∧ ∀ᶠ k : ℕ in atTop,
      c₁ ^ ((2 : ℝ) ^ (k : ℕ)) ≤ (egyptianFractionCount k : ℝ) ∧
      (egyptianFractionCount k : ℝ) ≤ c₂ ^ ((2 : ℝ) ^ (k : ℕ)) :=
  sorry
