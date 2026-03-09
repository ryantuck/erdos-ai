import Mathlib.Data.Real.Basic
import Mathlib.Order.RelClasses

/--
Erdős Problem #194 [ErGr79, ErGr80]:

Let k ≥ 3. Must any linear ordering of ℝ contain a monotone k-term arithmetic
progression, that is, some x₁ < ⋯ < xₖ (in the ordering) which forms an
increasing or decreasing k-term arithmetic progression in the usual order?

The answer is no, even for k = 3, as shown by Ardal, Brown, and Jungić.
Formally: there exists a strict total order on ℝ such that no 3-term arithmetic
progression is monotone with respect to it.
-/
theorem erdos_problem_194 :
    ∃ (r : ℝ → ℝ → Prop) (_ : IsStrictTotalOrder ℝ r),
      ∀ (a d : ℝ), d ≠ 0 →
        ¬((r a (a + d) ∧ r (a + d) (a + 2 * d)) ∨
          (r (a + 2 * d) (a + d) ∧ r (a + d) a)) :=
  sorry
