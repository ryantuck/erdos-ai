import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #930

Is it true that, for every r, there is a k such that if I₁, ..., Iᵣ are disjoint
intervals of consecutive integers, all of length at least k, then
∏_{1 ≤ i ≤ r} ∏_{m ∈ Iᵢ} m is not a perfect power?

Erdős and Selfridge [ErSe75] proved that the product of consecutive integers is
never a power (the case r = 1). The condition that the intervals be large in terms
of r is necessary for r = 2 — see the constructions in [363].
-/

/-- The product of consecutive positive integers from `a + 1` to `a + len`. -/
def prodInterval (a len : ℕ) : ℕ := ∏ i ∈ Finset.range len, (a + 1 + i)

/-- A positive integer `n` is a perfect power if there exist `b ≥ 1` and `e ≥ 2`
    with `n = b ^ e`. -/
def IsPerfectPower (n : ℕ) : Prop :=
  ∃ b e : ℕ, 1 ≤ b ∧ 2 ≤ e ∧ n = b ^ e

/--
Erdős Problem #930 [Er76d]:

For every r, there exists k such that for any r pairwise disjoint intervals of
consecutive integers, each of length at least k, the product of all elements
across all intervals is not a perfect power.

We model the r intervals by their starting points a₁ < ... < aᵣ and lengths
l₁, ..., lᵣ. The i-th interval is {aᵢ+1, ..., aᵢ+lᵢ}. Disjointness is
expressed by requiring aᵢ + lᵢ ≤ aⱼ for i < j (i.e. the intervals are ordered
and non-overlapping).
-/
theorem erdos_problem_930 (r : ℕ) :
    ∃ k : ℕ, ∀ (a l : ℕ → ℕ),
      (∀ i < r, k ≤ l i) →
      (∀ i j, i < j → j < r → a i + l i ≤ a j) →
      ¬ IsPerfectPower (∏ i ∈ Finset.range r, prodInterval (a i) (l i)) :=
  sorry
