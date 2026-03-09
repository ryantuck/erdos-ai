import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Bounds.Basic

open BigOperators Finset

/--
An infinite strictly increasing sequence of positive naturals with bounded gaps:
a : ℕ → ℕ is strictly increasing, starts at index 0, and there exists a constant C
such that a(i+1) - a(i) ≤ C for all i.
-/
structure BoundedGapSequence where
  a : ℕ → ℕ
  strictMono : StrictMono a
  pos : ∀ i, 0 < a i
  boundedGaps : ∃ C : ℕ, ∀ i, a (i + 1) - a i ≤ C

/--
Erdős Problem #299 [ErGr80, p.36]:

Is there an infinite sequence a₁ < a₂ < ⋯ such that aᵢ₊₁ - aᵢ = O(1) and no
finite sum of 1/aᵢ is equal to 1?

The answer is no: no such sequence exists. This follows from the positive solution
to Erdős Problem #298 by Bloom [Bl21].
-/
theorem erdos_problem_299 (seq : BoundedGapSequence) :
    ∃ F : Finset ℕ, F.Nonempty ∧
      ∑ i ∈ F, (1 : ℚ) / (seq.a i : ℚ) = 1 :=
  sorry
