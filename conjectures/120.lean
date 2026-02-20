import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

open MeasureTheory Set

/--
Erdős Similarity Problem (Problem #120) [Er74b, Er81b, Er83d, Er90, Er97f, Va99 2.46] — OPEN

Let A ⊆ ℝ be an infinite set. Must there be a set E ⊂ ℝ of positive Lebesgue measure
which does not contain any affine image of A of the form aA + b = {a·x + b | x ∈ A}
for some a, b ∈ ℝ with a ≠ 0?

Known partial results:
- True if A is unbounded or dense in some interval.
- It suffices to prove this when A = {a₁ > a₂ > ⋯} is a countable strictly monotone
  sequence converging to 0.
- Steinhaus: the statement is FALSE for finite sets A.
- The case A = {1, 1/2, 1/4, ...} remains open (Green's problem list, #94).

See surveys by Svetic [Sv00] and Jung–Lai–Mooroogen [JLM24] for an overview of progress.
-/
theorem erdos_problem_120 :
    ∀ A : Set ℝ, A.Infinite →
    ∃ E : Set ℝ, MeasurableSet E ∧ 0 < volume E ∧
      ∀ (a b : ℝ), a ≠ 0 → ¬((fun x => a * x + b) '' A ⊆ E) :=
  sorry
