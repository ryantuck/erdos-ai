import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

noncomputable section

/-!
# Erdős Problem #806

Let A ⊆ {1,…,n} with |A| ≤ n^{1/2}. Must there exist some B ⊂ ℤ with
|B| = o(n^{1/2}) such that A ⊆ B + B?

A problem of Erdős and Newman [ErNe77], who proved that there exist A with
|A| ≍ n^{1/2} such that if A ⊆ B + B then |B| ≫ (log log n / log n) · n^{1/2}.

Resolved by Alon, Bukh, and Sudakov [ABS09], who proved that for any
A ⊆ {1,…,n} with |A| ≤ n^{1/2} there exists some B such that A ⊆ B + B and
|B| ≪ (log log n / log n) · n^{1/2}.

Reference: [ErNe77]
https://www.erdosproblems.com/806
-/

/--
Erdős Problem #806 [ErNe77]:

For any ε > 0, for all sufficiently large n, for any A ⊆ {1,…,n} with
|A| ≤ √n, there exists a finite set B ⊂ ℤ with |B| ≤ ε · √n such that
every element of A (viewed in ℤ) belongs to B + B.

This captures the o(√n) conjecture. It was resolved by Alon, Bukh, and
Sudakov [ABS09] with the sharper bound |B| ≤ C · (log log n / log n) · √n.
-/
theorem erdos_problem_806 (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) → (A.card : ℝ) ≤ Real.sqrt n →
    ∃ B : Finset ℤ, (B.card : ℝ) ≤ ε * Real.sqrt n ∧
      ∀ a ∈ A, ∃ b₁ ∈ B, ∃ b₂ ∈ B, (a : ℤ) = b₁ + b₂ :=
  sorry

end
