import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Classical Finset Filter

/-- A number is 3-smooth if it is of the form 2^k * 3^l for some k, l ≥ 0. -/
def IsThreeSmooth (n : ℕ) : Prop :=
  ∃ k l : ℕ, n = 2 ^ k * 3 ^ l

/-- A finite set of natural numbers has bounded ratio C: the largest element
    is at most C times the smallest. -/
def HasBoundedRatio (s : Finset ℕ) (C : ℕ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, y ≤ C * x

/-- The set of natural numbers that can be represented as a sum of distinct
    3-smooth numbers with bounded ratio C. -/
def BoundedSmoothRepresentable (C : ℕ) : Set ℕ :=
  { n | ∃ s : Finset ℕ, s.Nonempty ∧
    (∀ x ∈ s, IsThreeSmooth x) ∧
    HasBoundedRatio s C ∧
    s.sum id = n }

/-- A set S ⊆ ℕ has natural density 0: the proportion of elements
    in {0, …, N−1} belonging to S tends to 0 as N → ∞. -/
noncomputable def HasDensityZero (S : Set ℕ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => ((Finset.range N).filter (· ∈ S)).card / (N : ℝ))
    Filter.atTop (nhds 0)

/--
Erdős Problem #845 [Er92b,p.239] [ErLe96,p.838] — DISPROVED

Let C > 0. Is it true that the set of integers of the form
  n = b₁ + ⋯ + bₜ  with b₁ < ⋯ < bₜ
where bᵢ = 2^{kᵢ} · 3^{lᵢ} for 1 ≤ i ≤ t and bₜ ≤ C · b₁
has density 0?

This was disproved by van Doorn and Everts, who showed that with C = 6,
every positive integer can be written as such a sum (so the set has
density 1, not 0).
-/
theorem erdos_problem_845 :
    ∃ C : ℕ, 0 < C ∧ ¬ HasDensityZero (BoundedSmoothRepresentable C) :=
  sorry
