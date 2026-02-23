import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finite.Defs

open Finset BigOperators

/--
Erdős Problem #46 (proved by Croot [Cr03]):
For every finite colouring of the positive integers ≥ 2, there exists a
monochromatic finite set {n₁, ..., nₖ} with 2 ≤ n₁ < ⋯ < nₖ whose
reciprocals sum to 1, i.e. ∑ 1/nᵢ = 1.
-/
theorem erdos_problem_46 (α : Type*) [Finite α] (c : ℕ → α) :
    ∃ S : Finset ℕ, S.Nonempty ∧
      (∀ n ∈ S, n ≥ 2) ∧
      (∃ color : α, ∀ n ∈ S, c n = color) ∧
      (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1 :=
  sorry
