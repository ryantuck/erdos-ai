import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Card

open Finset Filter Set

/-- The set of natural numbers expressible as a sum of distinct powers of d.
    These are the numbers whose base-d representation uses only digits 0 and 1. -/
def digitSet (d : ℕ) : Set ℕ :=
  {n : ℕ | ∃ S : Finset ℕ, n = ∑ i ∈ S, d ^ i}

/-- The sumset A + B of two sets of natural numbers. -/
def sumSet (A B : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/--
Erdős Problem #125 [BEGL96, Er97] — OPEN

Let A = {∑ εₖ 3ᵏ : εₖ ∈ {0,1}} be the set of integers which have only the
digits 0,1 when written in base 3, and B = {∑ εₖ 4ᵏ : εₖ ∈ {0,1}} be the set
of integers which have only the digits 0,1 when written in base 4.

Does A + B have positive density?

A problem of Burr, Erdős, Graham, and Li. Melfi showed
|C ∩ [1,x]| ≫ x^{0.965} where C = A + B, and Hasler–Melfi improved this to
x^{0.9777}. Hasler–Melfi also show the lower density of C is at most
1015/1458 ≈ 0.69616.
-/
theorem erdos_problem_125 :
    let A := digitSet 3
    let B := digitSet 4
    let C := sumSet A B
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ N in atTop, δ ≤ (Set.ncard (C ∩ Set.Iic N) : ℝ) / (N + 1) :=
  sorry
