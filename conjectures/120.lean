import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Image

open MeasureTheory Set

/--
Erdős Problem #120 (The Erdős Similarity Problem) [Er74b, Er81b, Er83d, Er90, Er97f]:

Let A ⊆ ℝ be an infinite set. Must there be a set E ⊂ ℝ of positive Lebesgue measure
which does not contain any set of the shape aA + b for some a, b ∈ ℝ with a ≠ 0?

In other words, for every infinite A ⊆ ℝ, there exists a measurable set E with
μ(E) > 0 such that no affine copy of A is contained in E.

This is known to be true when A is unbounded or dense in some interval. Steinhaus
proved it is false whenever A is a finite set.
-/
theorem erdos_problem_120 :
    ∀ A : Set ℝ, A.Infinite →
      ∃ E : Set ℝ, MeasurableSet E ∧
        volume E ≠ 0 ∧
        ∀ a b : ℝ, a ≠ 0 →
          ¬((fun x => a * x + b) '' A ⊆ E) :=
  sorry
