import Mathlib.Algebra.Group.Even
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Finset

/-!
# Erdős Problem #438

How large can A ⊆ {1, …, N} be if A + A contains no square numbers?

Taking all integers ≡ 1 (mod 3) shows that |A| ≥ N/3 is possible. This can
be improved to (11/32)N by taking all integers ≡ 1,5,9,13,14,17,21,25,26,29,30
(mod 32), as observed by Massias.

Khalfalah, Lodha, and Szemerédi proved that the maximal such A satisfies
|A| ≤ (11/32 + o(1))N, showing that 11/32 is sharp.
-/

/-- No sum of two elements of A is a perfect square. -/
def SumsetAvoidSquares (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬IsSquare (a + b)

/-- Erdős Problem #438 (SOLVED):
For any ε > 0, for all sufficiently large N, if A ⊆ {1, …, N} and no sum
a + b with a, b ∈ A is a perfect square, then |A| ≤ (11/32 + ε) · N.

Proved by Khalfalah, Lodha, and Szemerédi [KLS02]. -/
theorem erdos_problem_438 (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) →
    SumsetAvoidSquares A →
    (A.card : ℝ) ≤ (11 / 32 + ε) * (N : ℝ) :=
  sorry
