import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Set Filter BigOperators Classical

/-- The set of all sums of exactly `k` elements from `A` (with repetition allowed). -/
def exactSumset339 (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (f : Fin k → ℕ), (∀ i, f i ∈ A) ∧ n = ∑ i, f i}

/-- `A ⊆ ℕ` is an additive basis of order `r` if every sufficiently large natural number
    is the sum of at most `r` elements from `A` (with repetition). -/
def IsAdditiveBasis339 (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ k ≤ r, n ∈ exactSumset339 A k

/-- The set of integers representable as the sum of exactly `r` distinct elements from `A`. -/
def distinctExactSumset339 (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (s : Finset ℕ), ↑s ⊆ A ∧ s.card = r ∧ s.sum id = n}

/-- The lower density of A ⊆ ℕ:
    d_*(A) = liminf_{N→∞} |A ∩ {0, 1, ..., N-1}| / N -/
noncomputable def lowerDensity339 (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/--
Erdős Problem #339 [ErGr80, p.52]:

Let A ⊆ ℕ be a basis of order r. Must the set of integers representable as the
sum of exactly r distinct elements from A have positive lower density?

The answer is yes, as proved by Hegyvári, Hennecart, and Plagne [HHP03].
-/
theorem erdos_problem_339 :
    ∀ (A : Set ℕ) (r : ℕ),
      IsAdditiveBasis339 A r →
      0 < lowerDensity339 (distinctExactSumset339 A r) :=
  sorry
