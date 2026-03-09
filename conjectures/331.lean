import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Finset Real Classical

noncomputable section

/--
The counting function of A up to N, i.e., |A ∩ {1,…,N}|.
-/
def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/--
A set A ⊆ ℕ grows at least like N^{1/2}: there exists c > 0 such that
|A ∩ {1,…,N}| ≥ c · √N for all sufficiently large N.
-/
def GrowsLikeSqrt (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in atTop,
    (countingFn A N : ℝ) ≥ c * Real.sqrt (N : ℝ)

/--
Erdős Problem #331 [ErGr80,p.50] — DISPROVED:

Let A, B ⊆ ℕ such that for all large N,
  |A ∩ {1,…,N}| ≫ N^{1/2}  and  |B ∩ {1,…,N}| ≫ N^{1/2}.
Is it true that there are infinitely many solutions to
  a₁ - a₂ = b₁ - b₂ ≠ 0
with a₁, a₂ ∈ A and b₁, b₂ ∈ B?

Ruzsa observed a simple counterexample: take A to be the set of numbers whose
binary representation has non-zero digits only in even places, and B similarly
but in odd places. Both grow like ≫ N^{1/2}, yet for any n ≥ 1 there is
exactly one solution to n = a + b with a ∈ A and b ∈ B, so the conjecture
fails.

Since the conjecture is false, we state the negation.
-/
theorem erdos_problem_331 :
    ¬ (∀ (A B : Set ℕ),
      GrowsLikeSqrt A →
      GrowsLikeSqrt B →
      Set.Infinite {d : ℕ | 0 < d ∧
        ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ B, ∃ b₂ ∈ B,
          a₁ - a₂ = d ∧ b₁ - b₂ = d}) :=
  sorry
