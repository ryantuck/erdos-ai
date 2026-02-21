import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Abs

/-!
# Erdős Problem #178

Let A₁, A₂, ... be an infinite collection of infinite sets of integers,
say Aᵢ = {aᵢ₁ < aᵢ₂ < ⋯}. Does there exist some f : ℕ → {-1, 1} such that
  max_{m, 1 ≤ i ≤ d} |∑_{1 ≤ j ≤ m} f(aᵢⱼ)| ≪_d 1
for all d ≥ 1?

This is a question about set discrepancy. Erdős remarked 'it seems certain
that the answer is affirmative'. This was proved by Beck [Be81].
Beck [Be17] later proved that one can replace ≪_d 1 with ≪ d^(4+ε)
for any ε > 0.
-/

/--
Erdős Problem #178 [ErGr79, ErGr80]:
Given any infinite sequence of infinite subsets of ℕ (each represented by
its strictly increasing enumeration a(i, ·) : ℕ → ℕ), there exists a
coloring f : ℕ → ℤ with f(n) ∈ {-1, 1} such that for each d, the partial
sums of f along the first d sequences are uniformly bounded by a constant
depending only on d.

Proved by Beck [Be81].
-/
theorem erdos_problem_178 :
    ∀ a : ℕ → ℕ → ℕ, (∀ i, StrictMono (a i)) →
      ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
        ∀ d : ℕ, ∃ C : ℤ, 0 < C ∧
          ∀ m i, i < d → abs (∑ j ∈ Finset.range m, f (a i j)) ≤ C :=
  sorry
