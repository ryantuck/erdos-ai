import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Real

noncomputable section

/-- The largest prime factor of a natural number n. Returns 0 if n ≤ 1. -/
def largestPrimeFactor382 (n : ℕ) : ℕ :=
  n.factorization.support.sup id

/-- An interval [u, v] has its largest prime factor appearing with exponent ≥ 2
    in the factorization of the product ∏_{u ≤ m ≤ v} m. -/
def HasSquaredLargestPrime382 (u v : ℕ) : Prop :=
  let P := ∏ m ∈ Finset.Icc u v, m
  let p := largestPrimeFactor382 P
  u ≤ v ∧ 0 < p ∧ 1 < P.factorization p

/--
Erdős Problem #382 (Part 1) [ErGr80]:

Let u ≤ v be such that the largest prime dividing ∏_{u ≤ m ≤ v} m appears with
exponent at least 2. Is it true that v - u = v^{o(1)}?

This means: for every ε > 0, for all sufficiently large v, if the interval [u,v]
has its largest prime factor appearing with exponent ≥ 2, then v - u ≤ v^ε.
-/
theorem erdos_problem_382a :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ u v : ℕ, N₀ ≤ v →
      HasSquaredLargestPrime382 u v →
      ((v : ℝ) - (u : ℝ)) ≤ (v : ℝ) ^ ε :=
  sorry

/--
Erdős Problem #382 (Part 2) [ErGr80]:

Can v - u be arbitrarily large? That is, for every k, do there exist u ≤ v
with v - u ≥ k such that the largest prime dividing ∏_{u ≤ m ≤ v} m appears
with exponent at least 2?
-/
theorem erdos_problem_382b :
    ∀ k : ℕ, ∃ u v : ℕ, k ≤ v - u ∧ HasSquaredLargestPrime382 u v :=
  sorry

end
