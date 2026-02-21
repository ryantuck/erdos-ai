import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Finset

noncomputable section

/-!
# Erdős Problem #537

Let ε > 0 and N be sufficiently large. If A ⊆ {1, …, N} has |A| ≥ εN, must
there exist a₁, a₂, a₃ ∈ A and distinct primes p₁, p₂, p₃ such that
a₁p₁ = a₂p₂ = a₃p₃?

A positive answer would imply Problem #536.

**Disproved** by a construction of Ruzsa: consider the set of all squarefree
numbers of the shape p₁⋯pᵣ where p_{i+1} > 2pᵢ for 1 ≤ i < r. This set has
positive density. If A is its intersection with (N/2, N) then |A| ≫ N for all
large N, yet no three elements a₁, a₂, a₃ ∈ A and distinct primes p₁, p₂, p₃
satisfy a₁p₁ = a₂p₂ = a₃p₃.
-/

/--
**Erdős Problem #537** (Disproved by Ruzsa):

There exists ε > 0 such that for all sufficiently large N, there is a set
A ⊆ {1, …, N} with |A| ≥ εN such that there are no a₁, a₂, a₃ ∈ A and
distinct primes p₁, p₂, p₃ with a₁p₁ = a₂p₂ = a₃p₃.
-/
theorem erdos_problem_537 :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ ε * (N : ℝ) ≤ (A.card : ℝ) ∧
        ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a₃ ∈ A,
          ∀ p₁ p₂ p₃ : ℕ,
            Nat.Prime p₁ → Nat.Prime p₂ → Nat.Prime p₃ →
            p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
            ¬(a₁ * p₁ = a₂ * p₂ ∧ a₁ * p₁ = a₃ * p₃) :=
  sorry

end
