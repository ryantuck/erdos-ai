import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

/-!
# Erdős Problem #880

Let A ⊂ ℕ be an additive basis of order k. Let B = {b₁ < b₂ < ⋯} be the set
of integers which are the sum of k or fewer distinct a ∈ A. Is it true that
b_{n+1} - b_n = O(1)?

A problem of Burr and Erdős [Er98]. Hegyvári, Hennecart, and Plagne [HHP07]
showed the answer is yes for k = 2 (in fact with b_{n+1} - b_n ≤ 2 for
sufficiently large n) but no for k ≥ 3.
-/

/-- A set A ⊆ ℕ is an additive basis of order k if every sufficiently large
    natural number can be written as a sum of at most k elements from A
    (with repetition allowed). -/
def IsAdditiveBasis880 (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ (l : List ℕ), l.length ≤ k ∧ (∀ x ∈ l, x ∈ A) ∧ l.sum = n

/-- The set of natural numbers expressible as the sum of at most k distinct
    elements of A. -/
def DistinctSumSet880 (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (S : Finset ℕ), (∀ x ∈ S, x ∈ A) ∧ S.card ≤ k ∧ S.sum id = n}

/--
Erdős Problem #880, Part 1 (Hegyvári–Hennecart–Plagne [HHP07]):

If A is an additive basis of order 2, then the distinct sum set B of A (sums of
at most 2 distinct elements) has gaps bounded by 2 for all sufficiently large
elements: for large enough b ∈ B, the next element of B is at most b + 2.
-/
theorem erdos_problem_880_k2 (A : Set ℕ) (hA : IsAdditiveBasis880 A 2) :
    ∃ N₀ : ℕ, ∀ b ∈ DistinctSumSet880 A 2, b ≥ N₀ →
    ∃ b' ∈ DistinctSumSet880 A 2, b < b' ∧ b' ≤ b + 2 :=
  sorry

/--
Erdős Problem #880, Part 2 (Hegyvári–Hennecart–Plagne [HHP07]):

For every k ≥ 3, there exists an additive basis A of order k whose distinct sum
set has unbounded gaps.
-/
theorem erdos_problem_880_k3 :
    ∀ k : ℕ, k ≥ 3 →
    ∃ A : Set ℕ, IsAdditiveBasis880 A k ∧
    ∀ C : ℕ, ∃ b ∈ DistinctSumSet880 A k,
      ∀ b' ∈ DistinctSumSet880 A k, b < b' → b + C < b' :=
  sorry
