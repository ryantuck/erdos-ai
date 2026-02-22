import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Filter

/--
Count of pairs (i,j) with 1 ≤ j ≤ k, 0 ≤ i ≤ j, and a(i) + a(j) ≤ n.
Used in the recursive definition of the Rosen sequence.
-/
def rosenPairCount (a : ℕ → ℕ) (k n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1),
    if j = 0 then 0
    else ((Finset.range (j + 1)).filter fun i => a i + a j ≤ n).card

/--
Total count of pairs (i,j) with i ≤ j, j ≥ 1, from the full infinite
sequence, such that a(i) + a(j) ≤ x. For a strictly increasing sequence
on ℕ, a(j) ≥ j, so restricting j ≤ x suffices.
-/
def rosenPairCountTotal (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (x + 1),
    if j = 0 then 0
    else ((Finset.range (j + 1)).filter fun i => a i + a j ≤ x).card

/--
The Rosen sequence property: a(0) = 0, the sequence is strictly increasing,
and each a(k+1) is the smallest integer n such that the pair count with
respect to the first k+1 terms is strictly less than n.
-/
def IsRosenSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ StrictMono a ∧
  ∀ k, (∀ m, m < a (k + 1) → m ≤ rosenPairCount a k m) ∧
       rosenPairCount a k (a (k + 1)) < a (k + 1)

/--
Erdős Problem #954 [Er77c, p.71]:

Let 0 = a₀ < a₁ < a₂ < ⋯ be the sequence defined by a₀ = 0 and aₖ₊₁ is
the smallest integer n for which the number of pairs (i,j) with
0 ≤ i ≤ j ≤ k, j ≥ 1, and aᵢ + aⱼ ≤ n is strictly less than n.

The sequence begins 0, 1, 3, 5, 9, 13, 17, 24, 31, 38, 45, ... (OEIS A390642).

Is the total pair count R(x) = #{(i,j) : i ≤ j, j ≥ 1, aᵢ + aⱼ ≤ x}
equal to x + O(x^{1/4 + o(1)})?

By construction R(x) ≥ x always. Erdős and Rosen could not even prove
whether R(x) ≤ (1 + o(1))x.
-/
theorem erdos_problem_954_conjecture :
    ∀ a : ℕ → ℕ, IsRosenSequence a →
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ (x : ℕ) in atTop,
          abs ((rosenPairCountTotal a x : ℝ) - (x : ℝ)) ≤
            C * (x : ℝ) ^ ((1 : ℝ) / 4 + ε) :=
  sorry
