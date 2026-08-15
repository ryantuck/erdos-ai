import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open scoped BigOperators
open Polynomial Finset

noncomputable section

namespace Erdos1114

/--
Erdős Problem #1114 (Proved by Balint [Ba60b]):

Let f(x) ∈ ℝ[x] be a polynomial whose (n+1) roots are all real, distinct, and
form an arithmetic progression: a, a+d, a+2d, ..., a+n·d for some a ∈ ℝ, d > 0.
By Rolle's theorem, f'(x) has n distinct real zeros b₀ < b₁ < ⋯ < b_{n-1}
in the interval (a, a+n·d).

The conjecture (now proved) states that the differences between consecutive
zeros of f'(x) are monotonically increasing from the midpoint towards the
endpoints. By symmetry of the arithmetic progression, the zeros of f' are
symmetric about the center point, so it suffices to state the monotonicity
for the right half: for indices i, j with ⌊(n-1)/2⌋ ≤ i < j and j+1 < n,
we have (b_{i+1} - b_i) ≤ (b_{j+1} - b_j).

Tags: polynomials, analysis
-/
theorem erdos_problem_1114 (n : ℕ) (hn : 2 ≤ n) (a d : ℝ) (hd : 0 < d) :
    let f := ∏ i ∈ range (n + 1), (X - C (a + ↑i * d))
    ∃ b : ℕ → ℝ,
      (∀ i j, i < n → j < n → i < j → b i < b j) ∧
      (∀ j, j < n → (derivative f).IsRoot (b j)) ∧
      (∀ x : ℝ, (derivative f).IsRoot x → ∃ j, j < n ∧ b j = x) ∧
      ∀ i j, (n - 1) / 2 ≤ i → i < j → j + 1 < n →
        b (i + 1) - b i ≤ b (j + 1) - b j :=
  sorry

end Erdos1114
