import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Finset

/-!
# Erdős Problem #284 (Proved)

Let f(k) be the maximal value of n₁ such that there exist n₁ < n₂ < ⋯ < nₖ
with 1 = 1/n₁ + ⋯ + 1/nₖ. Is it true that f(k) = (1+o(1)) k/(e-1)?

The upper bound f(k) ≤ (1+o(1)) k/(e-1) is trivial since for any u ≥ 1 we have
∑_{u ≤ n ≤ eu} 1/n = 1 + o(1), and hence if f(k) = u then k ≥ (e-1-o(1))u.

Essentially solved by Croot [Cr01], who showed that for any N > 1 there exists
some k ≥ 1 and N < n₁ < ⋯ < nₖ ≤ (e+o(1))N with 1 = ∑ 1/nᵢ.
-/

/-- f(k) is the maximal value of the minimum element in any set of k distinct positive
    integers whose reciprocals sum to 1. -/
noncomputable def erdos284_f (k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ S : Finset ℕ, S.card = k ∧ (∀ n ∈ S, 0 < n) ∧
    S.sum (fun n => (1 : ℚ) / ↑n) = 1 ∧ m ∈ S ∧ ∀ n ∈ S, m ≤ n}

/--
Erdős Problem #284 (Proved) [ErGr80]:

f(k) = (1+o(1)) k/(e-1), where f(k) is the maximal minimum element in any
representation of 1 as a sum of k distinct unit fractions.

Equivalently, f(k) · (e-1) / k → 1 as k → ∞.
-/
theorem erdos_problem_284 :
    Tendsto (fun k => (erdos284_f k : ℝ) * (Real.exp 1 - 1) / (k : ℝ))
      atTop (nhds 1) :=
  sorry
