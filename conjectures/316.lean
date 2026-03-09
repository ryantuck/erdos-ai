import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
Erdős Problem #316 [ErGr80] (Disproved):

Is it true that if A ⊂ ℕ \ {1} is a finite set with ∑_{n ∈ A} 1/n < 2
then there is a partition A = A₁ ⊔ A₂ such that ∑_{n ∈ Aᵢ} 1/n < 1
for i = 1, 2?

This is false. Sándor observed that the proper divisors of 120 form a
counterexample. The minimal counterexample is {2,3,4,5,6,7,10,11,13,14,15},
found by Tom Stobart.
-/
theorem erdos_problem_316 :
    ¬ (∀ (A : Finset ℕ),
      (∀ a ∈ A, 2 ≤ a) →
      ∑ n ∈ A, (1 : ℚ) / (n : ℚ) < 2 →
      ∃ A₁ A₂ : Finset ℕ,
        A₁ ∪ A₂ = A ∧
        Disjoint A₁ A₂ ∧
        ∑ n ∈ A₁, (1 : ℚ) / (n : ℚ) < 1 ∧
        ∑ n ∈ A₂, (1 : ℚ) / (n : ℚ) < 1) :=
  sorry
