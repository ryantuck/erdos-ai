import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #843

Are the squares Ramsey 2-complete? That is, is it true that, in any 2-colouring
of the square numbers, every sufficiently large n ∈ ℕ can be written as a
monochromatic sum of distinct squares?

A problem of Burr and Erdős [BuEr85]. Proved by Conlon, Fox, and Pham [CFP21],
who showed that the set of k-th powers contains a sparse Ramsey r-complete
subsequence for every r, k ≥ 2.
-/

/-- A set A ⊆ ℕ is Ramsey r-complete if for every r-colouring of A,
    every sufficiently large natural number can be written as a sum of
    distinct monochromatic elements of A. -/
def IsRamseyComplete (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ c : ℕ → Fin r, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ (S : Finset ℕ) (a : Fin r),
      (↑S : Set ℕ) ⊆ A ∧
      (∀ s ∈ S, c s = a) ∧
      S.sum id = n

/--
Erdős Problem #843 [BuEr85][Er92b][Er95]:

The set of perfect squares is Ramsey 2-complete. That is, for any
2-colouring of the squares, every sufficiently large natural number
can be written as a monochromatic sum of distinct squares.

Proved by Conlon, Fox, and Pham [CFP21].
-/
theorem erdos_problem_843 :
    IsRamseyComplete {n : ℕ | ∃ m : ℕ, m ≥ 1 ∧ n = m ^ 2} 2 :=
  sorry
