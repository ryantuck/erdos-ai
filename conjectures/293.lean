import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open BigOperators Real Filter Finset Classical

/-!
# Erdős Problem #293

Let k ≥ 1 and let v(k) be the minimal integer which does not appear as some nᵢ
in a solution to 1 = 1/n₁ + ⋯ + 1/nₖ with 1 ≤ n₁ < ⋯ < nₖ.
Estimate the growth of v(k).

Known bounds:
- v(k) ≫ k! (Bleicher–Erdős [BlEr75])
- v(k) ≥ e^{ck²} for some c > 0 (van Doorn–Tang [vDTa25b])
- v(k) ≤ k · c₀^{2^k} where c₀ ≈ 1.26408 is the Vardi constant

It may be that v(k) grows doubly exponentially in √k or even k.
-/

/-- A positive integer n appears in a k-term Egyptian fraction representation of 1
    if there exists a k-element set S of distinct positive integers with n ∈ S
    such that ∑_{m ∈ S} 1/m = 1. -/
def AppearsInKTermEgyptian (k n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.card = k ∧ n ∈ S ∧ (∀ m ∈ S, 0 < m) ∧
    ∑ m ∈ S, (1 : ℚ) / (m : ℚ) = 1

/-- v(k) is the smallest positive integer that does not appear in any representation
    of 1 as a sum of exactly k distinct unit fractions. -/
noncomputable def erdos293_v (k : ℕ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ¬AppearsInKTermEgyptian k n}

/-- Bleicher–Erdős lower bound [BlEr75]:
    There exists a constant c > 0 such that v(k) ≥ c · k! for all k ≥ 1. -/
theorem erdos293_bleicher_erdos_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      c * (Nat.factorial k : ℝ) ≤ (erdos293_v k : ℝ) :=
  sorry

/-- van Doorn–Tang lower bound [vDTa25b]:
    There exists a constant c > 0 such that v(k) ≥ e^{ck²} for all
    sufficiently large k. -/
theorem erdos293_van_doorn_tang_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      Real.exp (c * (k : ℝ) ^ 2) ≤ (erdos293_v k : ℝ) :=
  sorry

/-- Upper bound: v(k) ≤ k · c₀^{2^k} where c₀ is the Vardi constant (≈ 1.26408).
    There exists c₀ > 1 such that v(k) ≤ k · c₀^{2^k} for all k ≥ 1. -/
theorem erdos293_upper_bound :
    ∃ c₀ : ℝ, 1 < c₀ ∧ ∀ k : ℕ, 1 ≤ k →
      (erdos293_v k : ℝ) ≤ (k : ℝ) * c₀ ^ ((2 : ℝ) ^ (k : ℕ)) :=
  sorry

/--
Erdős Problem #293 [ErGr80, p.35]:

Conjecture: v(k) grows doubly exponentially in k. That is, there exists a
constant c > 0 such that v(k) ≥ e^{e^{ck}} for all sufficiently large k.

(A weaker form conjectures doubly exponential growth in √k.)
-/
theorem erdos_problem_293 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      Real.exp (Real.exp (c * (k : ℝ))) ≤ (erdos293_v k : ℝ) :=
  sorry
