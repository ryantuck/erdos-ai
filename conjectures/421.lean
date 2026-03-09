import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset

/--
A strictly increasing sequence d : ℕ → ℕ has **natural density 1** if
|{i : d(i) ≤ N}| / N → 1 as N → ∞, i.e., for every ε > 0, eventually
the count of terms up to N is at least (1 - ε) · N.
-/
def HasDensityOne (d : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((Finset.range N).filter (fun i => d i ≤ N)).card ≥ (1 - ε) * (N : ℝ)

/--
A sequence d has **distinct consecutive products** if for any two
intervals [u₁, v₁] and [u₂, v₂] (with u ≤ v), equality of the
products ∏_{u ≤ i ≤ v} d(i) implies the intervals are the same.
-/
def DistinctConsecutiveProducts (d : ℕ → ℕ) : Prop :=
  ∀ u₁ v₁ u₂ v₂ : ℕ,
    u₁ ≤ v₁ → u₂ ≤ v₂ →
      ∏ i ∈ Finset.Icc u₁ v₁, d i = ∏ i ∈ Finset.Icc u₂ v₂, d i →
        u₁ = u₂ ∧ v₁ = v₂

/--
Erdős Problem #421 [ErGr80, p.84]:

Is there a sequence 1 ≤ d₁ < d₂ < ⋯ with density 1 such that all
products ∏_{u ≤ i ≤ v} dᵢ are distinct?

A construction of Selfridge shows that there exists such a sequence of
density > 1/e - ε for any ε > 0.
-/
theorem erdos_problem_421 :
    ∃ d : ℕ → ℕ,
      StrictMono d ∧
      (∀ i, 1 ≤ d i) ∧
      HasDensityOne d ∧
      DistinctConsecutiveProducts d :=
  sorry
