import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn

open Classical Nat Real Filter

noncomputable section

/-- The set of positive integers n for which the normalised prime gap
  (p_{n+1} - p_n) / log n is less than c. -/
def primeGapDensitySet (c : ℝ) : Set ℕ :=
  {n : ℕ | 0 < n ∧
    ((nth Nat.Prime (n + 1) : ℝ) - (nth Nat.Prime n : ℝ)) / Real.log (n : ℝ) < c}

/-- The upper density of A ⊆ ℕ:
  d*(A) = limsup_{N→∞} |A ∩ {1, ..., N}| / N -/
noncomputable def upperDensity234 (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/-- The lower density of A ⊆ ℕ:
  d_*(A) = liminf_{N→∞} |A ∩ {1, ..., N}| / N -/
noncomputable def lowerDensity234 (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/-- A set has natural density d if its upper and lower densities both equal d. -/
def hasNaturalDensity234 (A : Set ℕ) (d : ℝ) : Prop :=
  upperDensity234 A = d ∧ lowerDensity234 A = d

/--
Erdős Problem #234 [Er55c, Er61]:

For every c ≥ 0 the density f(c) of integers n for which
  (p_{n+1} - p_n) / log n < c
exists and is a continuous function of c.

Here p_n denotes the n-th prime. The conjecture asserts two things:
1. For each c ≥ 0, the natural density of {n : (p_{n+1} - p_n) / log n < c} exists.
2. The resulting function c ↦ f(c) is continuous.

See also [5].
-/
theorem erdos_problem_234 :
    ∃ f : ℝ → ℝ,
      (∀ c : ℝ, 0 ≤ c → hasNaturalDensity234 (primeGapDensitySet c) (f c)) ∧
      Continuous f :=
  sorry

end
