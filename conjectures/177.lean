import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Real

noncomputable section

/-!
# Erdős Problem #177

Find the smallest h(d) such that there exists a function f : ℕ → {-1,1}
such that, for every d ≥ 1,
  max_{P_d} |∑_{n ∈ P_d} f(n)| ≤ h(d),
where P_d ranges over all finite arithmetic progressions with common
difference d.

Known bounds:
- Lower: h(d) ≫ d^{1/2} (Roth [Ro64])
- Upper: h(d) ≤ d^{8+ε} is achievable for every ε > 0 (Beck [Be17])
- Van der Waerden's theorem implies h(d) → ∞.
- Cantor, Erdős, Schreiber, and Straus proved h(d) ≪ d!.
-/

/--
Erdős Problem #177 - Lower bound (Roth [Ro64]):
For any ±1 coloring of ℕ and any d ≥ 1, there exists a finite arithmetic
progression of common difference d with discrepancy at least c·√d.
That is, h(d) ≫ d^{1/2}.
-/
theorem erdos_problem_177_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℕ → ℤ,
    (∀ n, f n = 1 ∨ f n = -1) →
    ∀ d : ℕ, 0 < d →
    ∃ a k : ℕ, 0 < k ∧
      c * Real.sqrt (↑d) ≤ |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| :=
  sorry

/--
Erdős Problem #177 - Upper bound (Beck [Be17]):
For every ε > 0, there exists a ±1 coloring f of ℕ such that for every
d ≥ 1 and every finite AP of common difference d with k terms,
|∑ f| ≤ d^{8+ε}. That is, h(d) ≤ d^{8+ε}.
-/
theorem erdos_problem_177_upper :
    ∀ ε : ℝ, 0 < ε →
    ∃ f : ℕ → ℤ,
    (∀ n, f n = 1 ∨ f n = -1) ∧
    ∀ d : ℕ, 0 < d → ∀ a k : ℕ, 0 < k →
      |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| ≤ (↑d : ℝ) ^ ((8 : ℝ) + ε) :=
  sorry

end
