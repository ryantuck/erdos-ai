import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic

open Finset BigOperators

/-!
# Erdős Problem #782

Do the squares contain arbitrarily long quasi-progressions? That is, does there
exist some constant C > 0 such that, for any k, the squares contain a sequence
x₁, ..., x_k where, for some d and all 1 ≤ i < k,
  x_i + d ≤ x_{i+1} ≤ x_i + d + C.

Do the squares contain arbitrarily large combinatorial cubes
  a + {∑_i ε_i b_i : ε_i ∈ {0,1}} ?

A question of Brown, Erdős, and Freedman [BEF90]. It is a classical fact that
the squares do not contain arithmetic progressions of length 4. An affirmative
answer to the first question implies an affirmative answer to the second.
-/

/--
Erdős Problem #782, Part 1 (Quasi-progressions in the squares):

There exists a constant C such that for any k ≥ 2, one can find k perfect
squares x₁ < x₂ < ⋯ < x_k forming a quasi-progression with gap d, meaning
x_i + d ≤ x_{i+1} ≤ x_i + d + C for all consecutive pairs.
-/
theorem erdos_problem_782_quasi_progressions :
    ∃ C : ℕ, ∀ k : ℕ, k ≥ 2 →
    ∃ (x : Fin k → ℕ) (d : ℕ), d > 0 ∧
    (∀ i, IsSquare (x i)) ∧
    (∀ i j : Fin k, i < j → x i < x j) ∧
    (∀ (i : ℕ) (hi : i + 1 < k),
      x ⟨i, by omega⟩ + d ≤ x ⟨i + 1, hi⟩ ∧
      x ⟨i + 1, hi⟩ ≤ x ⟨i, by omega⟩ + d + C) :=
  sorry

/--
Erdős Problem #782, Part 2 (Combinatorial cubes in the squares):

For any m, the set of perfect squares contains a combinatorial cube of
dimension m: there exist a and positive b₁, ..., b_m such that
a + ∑_{i ∈ S} b_i is a perfect square for every subset S ⊆ {1, ..., m}.
-/
theorem erdos_problem_782_cubes :
    ∀ m : ℕ, ∃ (a : ℕ) (b : Fin m → ℕ),
    (∀ i, b i > 0) ∧
    (∀ S : Finset (Fin m), IsSquare (a + ∑ i ∈ S, b i)) :=
  sorry
