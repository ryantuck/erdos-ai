import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs

open Filter Real Finset

noncomputable section

/-!
# Erdős Problem #839

Let 1 ≤ a₁ < a₂ < ⋯ be a sequence of integers such that no aᵢ is the sum
of consecutive aⱼ for j < i. Is it true that

  limsup aₙ/n = ∞?

Or even

  lim (1/log x) ∑_{aₙ < x} 1/aₙ = 0?

A problem of Erdős [Er78f][Er92c].
-/

/-- A sequence a : ℕ → ℕ is "sum-of-consecutive-free" if no term equals
    the sum of a contiguous block of earlier terms. That is, for all i,
    aᵢ ≠ aⱼ + aⱼ₊₁ + ⋯ + aₖ for any j ≤ k < i. -/
def SumOfConsecutiveFree839 (a : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, ∀ j k : ℕ, j ≤ k → k < i →
    a i ≠ ∑ l ∈ Finset.Icc j k, a l

/--
Erdős Problem #839 (Part 1) [Er78f][Er92c]:

Let 1 ≤ a₁ < a₂ < ⋯ be a strictly increasing sequence of positive integers
such that no aᵢ is the sum of consecutive aⱼ for j < i.
Then limsup aₙ/n = ∞.

Formulated as: for every M, there are infinitely many n with aₙ/n > M.
-/
theorem erdos_problem_839_part1 (a : ℕ → ℕ) (ha_pos : ∀ n, 1 ≤ a n)
    (ha_mono : StrictMono a) (ha_free : SumOfConsecutiveFree839 a) :
    ∀ M : ℝ, ∃ᶠ n in atTop, M < (a n : ℝ) / (n : ℝ) :=
  sorry

/--
Erdős Problem #839 (Part 2, stronger) [Er78f][Er92c]:

Let 1 ≤ a₁ < a₂ < ⋯ be a strictly increasing sequence of positive integers
such that no aᵢ is the sum of consecutive aⱼ for j < i.
Then lim_{x → ∞} (1/log x) ∑_{aₙ < x} 1/aₙ = 0.
-/
theorem erdos_problem_839_part2 (a : ℕ → ℕ) (ha_pos : ∀ n, 1 ≤ a n)
    (ha_mono : StrictMono a) (ha_free : SumOfConsecutiveFree839 a) :
    Tendsto (fun x : ℕ =>
      (∑ n ∈ (Finset.range x).filter (fun n => a n < x), (1 / (a n : ℝ))) /
      Real.log (x : ℝ))
      atTop (nhds 0) :=
  sorry

end
