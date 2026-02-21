import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset

/--
Erdős Problem #484 (a conjecture of Roth, proved by Erdős–Sárközy–Sós [ESS89]):

There exists an absolute constant c > 0 such that, whenever {1, …, N} is
k-coloured (and N is large enough depending on k), there are at least cN
integers in {1, …, N} representable as a monochromatic sum, i.e., as a + b
where a, b ∈ {1, …, N} lie in the same colour class and a ≠ b.

Erdős, Sárközy, and Sós proved this and showed that in fact at least
N/2 - O(N^{1 - 1/2^{k+1}}) even numbers are of this form.
-/
theorem erdos_problem_484 :
    ∃ c : ℝ, 0 < c ∧
    ∀ k : ℕ, 0 < k →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ χ : ℕ → Fin k,
    ∃ S ⊆ Finset.Icc 1 N,
      (S.card : ℝ) ≥ c * (N : ℝ) ∧
      ∀ n ∈ S, ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N,
        a ≠ b ∧ χ a = χ b ∧ a + b = n :=
  sorry
