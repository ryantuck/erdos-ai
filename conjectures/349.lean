import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

open Finset

/--
A sequence `a : ℕ → ℤ` is **complete** if every sufficiently large positive
integer can be written as a sum of distinct terms of the sequence.
-/
def IsCompleteSequence (a : ℕ → ℤ) : Prop :=
  ∃ N : ℤ, ∀ m : ℤ, N ≤ m →
    ∃ (S : Finset ℕ), (S.sum a = m) ∧ (∀ i ∈ S, ∀ j ∈ S, a i = a j → i = j)

/--
Erdős Problem #349 [ErGr80, p.57]:

For what values of t, α ∈ (0, ∞) is the sequence ⌊tαⁿ⌋ complete?

It is conjectured that the sequence ⌊tαⁿ⌋ is complete for all t > 0 and all
1 < α < (1 + √5)/2 (the golden ratio).
-/
theorem erdos_problem_349 :
    ∀ (t α : ℝ),
      0 < t →
      1 < α →
      α < (1 + Real.sqrt 5) / 2 →
      IsCompleteSequence (fun n => ⌊t * α ^ n⌋) :=
  sorry
