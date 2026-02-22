import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort

open Finset

noncomputable section

/-!
# Erdős Problem #867

Is it true that if A = {a₁ < ⋯ < aₜ} ⊆ {1, …, N} has no solutions to
  a_i + a_{i+1} + ⋯ + a_j ∈ A  (with i < j, at least two terms)
then |A| ≤ N/2 + O(1)?

A finitary version of Problem #839. Taking A = (N/2, N] ∩ ℕ shows
|A| ≥ N/2 - O(1) is possible. This has been DISPROVED: Coppersmith and
Phillips [CoPh96] proved the maximum |A| satisfies
  (13/24)N - O(1) ≤ |A| ≤ (2/3 - 1/512)N + log N.
-/

/-- A finite set A of natural numbers is "consecutive-sum-free" if, when its
    elements are listed in increasing order as a₁ < a₂ < ⋯ < aₜ, no sum of
    two or more consecutive elements (a_i + a_{i+1} + ⋯ + a_j with i < j)
    lies in A. -/
def ConsecutiveSumFree867 (A : Finset ℕ) : Prop :=
  let s := A.sort (· ≤ ·)
  ∀ i j : ℕ, i < j → j < s.length →
    (∑ k ∈ Finset.Icc i j, s.getD k 0) ∉ A

/--
Erdős Problem #867 (disproved) [Er92c]:

If A = {a₁ < ⋯ < aₜ} ⊆ {1, …, N} has no sum of two or more consecutive
elements in A, then |A| ≤ N/2 + C for some absolute constant C.
-/
theorem erdos_problem_867 :
    ∃ C : ℕ, ∀ N : ℕ, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
    ConsecutiveSumFree867 A →
    A.card ≤ N / 2 + C :=
  sorry

end
