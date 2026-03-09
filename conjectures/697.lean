import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Classical Filter Finset Real

noncomputable section

/-!
# Erdős Problem #697

Let δ(m,α) denote the density of the set of integers which are divisible by some
d ≡ 1 (mod m) with 1 < d < exp(m^α). Does there exist some β ∈ (1,∞) such that
lim_{m→∞} δ(m,α) is 0 if α < β and 1 if α > β?

This was proved by Hall with β = 1/log 2.

Reference: [Er79e]
https://www.erdosproblems.com/697
-/

/-- Count of integers n ∈ {1, ..., N} divisible by some d ≡ 1 (mod m)
    with 1 < d < exp(m^α). -/
noncomputable def countDiv697 (m : ℕ) (α : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n =>
    ∃ d : ℕ, d ∣ (n + 1) ∧ d % m = 1 ∧ 1 < d ∧ (d : ℝ) < Real.exp ((m : ℝ) ^ α))).card

/-- The natural density δ(m, α) of the set of positive integers divisible by
    some d ≡ 1 (mod m) with 1 < d < exp(m^α). -/
noncomputable def delta697 (m : ℕ) (α : ℝ) : ℝ :=
  limUnder atTop (fun N : ℕ => (countDiv697 m α (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))

/--
Erdős Problem #697 [Er79e]:

There exists β ∈ (1, ∞) such that for all α:
- if α < β then δ(m, α) → 0 as m → ∞
- if α > β then δ(m, α) → 1 as m → ∞
-/
theorem erdos_problem_697 :
    ∃ β : ℝ, 1 < β ∧
      (∀ α : ℝ, 0 < α → α < β →
        Filter.Tendsto (fun m : ℕ => delta697 m α) atTop (nhds 0)) ∧
      (∀ α : ℝ, α > β →
        Filter.Tendsto (fun m : ℕ => delta697 m α) atTop (nhds 1)) :=
  sorry

end
