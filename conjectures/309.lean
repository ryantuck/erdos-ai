import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Classical Finset BigOperators Filter Real

/--
A positive integer `k` is representable as a sum of distinct unit fractions with
denominators from `{1, ..., N}` if there exists a subset `S ⊆ {1, ..., N}` such
that `∑_{n ∈ S} 1/n = k`.
-/
def IsRepresentableUnitFractionSum (N : ℕ) (k : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n ∧ n ≤ N) ∧
    ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = (k : ℚ)

/--
`countRepresentableIntegers N` counts the number of positive integers that can be
represented as sums of distinct unit fractions with denominators from `{1, ..., N}`.
-/
noncomputable def countRepresentableIntegers (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun k => 0 < k ∧ IsRepresentableUnitFractionSum N k)).card

/--
Erdős Problem #309 (DISPROVED) [ErGr80]:

Let N ≥ 1. How many integers can be written as the sum of distinct unit fractions
with denominators from {1, ..., N}? Erdős conjectured that there are o(log N) such
integers. This was disproved.

The trivial upper bound is F(N) ≤ log N + O(1). Yokota [Yo97] proved that
F(N) ≥ log N − O(log log N), establishing that F(N) = Θ(log N).

We formalize the negation of the original conjecture: there exists a positive
constant c such that F(N) ≥ c · log N for all sufficiently large N.
-/
theorem erdos_problem_309 :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (N : ℕ) in atTop,
      c * Real.log (N : ℝ) ≤ (countRepresentableIntegers N : ℝ) :=
  sorry
