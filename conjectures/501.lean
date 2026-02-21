import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Set.Card

open MeasureTheory Set

/-
Erdős Problem #501 [Er61] [ErHa71]:

For every x ∈ ℝ, let A_x ⊂ ℝ be a bounded set with outer measure < 1.
Must there exist an infinite independent set, that is, some infinite X ⊆ ℝ
such that x ∉ A_y for all x ≠ y ∈ X?

If the sets A_x are closed and have measure < 1, then must there exist an
independent set of size 3?

Erdős and Hajnal proved the existence of arbitrarily large finite independent
sets (under the assumptions in the first problem). Hechler showed the answer
to the first question is no, assuming the continuum hypothesis. Newelski,
Pawlikowski, and Seredyński proved that if all the A_x are closed with
measure < 1 then there is an infinite independent set.
-/

/-- A set X is independent with respect to a family of sets A if for all
distinct x, y ∈ X, we have x ∉ A y. -/
def IndependentFamily (A : ℝ → Set ℝ) (X : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → x ∉ A y

/-- Part 1: If each A_x is bounded with outer measure < 1, must there exist
an infinite independent set? -/
theorem erdos_problem_501_part1 :
    ∀ A : ℝ → Set ℝ,
      (∀ x : ℝ, Bornology.IsBounded (A x) ∧ volume (A x) < 1) →
      ∃ X : Set ℝ, X.Infinite ∧ IndependentFamily A X :=
  sorry

/-- Part 2: If each A_x is closed with measure < 1, must there exist an
independent set of size 3? -/
theorem erdos_problem_501_part2 :
    ∀ A : ℝ → Set ℝ,
      (∀ x : ℝ, IsClosed (A x) ∧ volume (A x) < 1) →
      ∃ x y z : ℝ, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
        IndependentFamily A {x, y, z} :=
  sorry
