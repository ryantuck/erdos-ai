import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic

open Finset BigOperators

/-!
# Erdős Problem #437

Let 1 ≤ a₁ < ⋯ < aₖ ≤ x. How many of the partial products
a₁, a₁a₂, …, a₁⋯aₖ can be squares? Is it true that, for any ε > 0,
there can be more than x^{1-ε} squares?

Erdős and Graham write it is 'trivial' that there are o(x) many such squares,
although this is not quite trivial, using Siegel's theorem.

A positive answer follows from work of Bui, Pratt, and Zaharescu [BPZ24],
as noted by Tao.
-/

/-- The partial product of the first (j+1) elements of a finite sequence
    a : Fin k → ℕ, i.e., a(0) * a(1) * ⋯ * a(j). -/
def erdos437_partialProd {k : ℕ} (a : Fin k → ℕ) (j : Fin k) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin k => i ≤ j), a i

/-- The count of indices j ∈ {0, …, k-1} for which the partial product
    a(0) * ⋯ * a(j) is a perfect square. -/
def erdos437_squareCount {k : ℕ} (a : Fin k → ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin k => IsSquare (erdos437_partialProd a j))).card

/-- Erdős Problem #437 (PROVED):

For any ε > 0 and all sufficiently large x, there exists a strictly increasing
sequence 1 ≤ a₁ < ⋯ < aₖ ≤ x such that more than x^{1-ε} of the partial
products a₁, a₁a₂, …, a₁⋯aₖ are perfect squares.

Proved by Bui, Pratt, and Zaharescu [BPZ24], as noted by Tao. -/
theorem erdos_problem_437 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
    ∃ (k : ℕ) (a : Fin k → ℕ),
      StrictMono a ∧
      (∀ i, 1 ≤ a i) ∧
      (∀ i, a i ≤ x) ∧
      (erdos437_squareCount a : ℝ) > (x : ℝ) ^ ((1 : ℝ) - ε) :=
  sorry
