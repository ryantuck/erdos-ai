import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators Finset

/--
A finite set A of natural numbers has **distinct subset reciprocal sums** if
for any two subsets S₁, S₂ ⊆ A, equality of ∑_{n ∈ S} 1/n implies S₁ = S₂.
-/
def DistinctSubsetReciprocalSums (A : Finset ℕ) : Prop :=
  ∀ S₁ ∈ A.powerset, ∀ S₂ ∈ A.powerset,
    ∑ n ∈ S₁, (1 : ℚ) / (n : ℚ) = ∑ n ∈ S₂, (1 : ℚ) / (n : ℚ) → S₁ = S₂

/--
R(N) is the size of the largest A ⊆ {1, …, N} such that all subset
reciprocal sums ∑_{n ∈ S} 1/n are distinct for S ⊆ A.
-/
noncomputable def R (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    DistinctSubsetReciprocalSums A ∧ A.card = k}

/--
Erdős Problem #321 [ErGr80, p.43]:

What is the size of the largest A ⊆ {1, …, N} such that all sums
∑_{n ∈ S} 1/n are distinct for S ⊆ A?

Let R(N) be the maximal such size. Bleicher and Erdős [BlEr75, BlEr76b] showed:

  (N / log N) ∏_{i=3}^{k} logᵢ N ≤ R(N) ≤ (1/log 2) logᵣ N · (N / log N) ∏_{i=3}^{r} logᵢ N

The lower bound is valid for any k ≥ 4 with logₖ N ≥ k, and the upper bound
for any r ≥ 1 with log₂ᵣ N ≥ 1 (where logᵢ denotes the i-fold iterated
logarithm).

This formalizes the (weaker) statement that R(N) grows faster than any
power of log N but is o(N).
-/
theorem erdos_problem_321_upper :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        (R N : ℝ) ≤ ε * (N : ℝ) :=
  sorry

theorem erdos_problem_321_lower :
    ∀ C : ℝ, 0 < C →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        (R N : ℝ) ≥ C * Real.log (N : ℝ) :=
  sorry
