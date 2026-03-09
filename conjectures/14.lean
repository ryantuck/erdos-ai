import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat

open scoped Classical
open Finset

noncomputable section

/-- The number of representations of `n` as `a + b` with `a, b ∈ A` and `a ≤ b`. -/
def reprCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A ∧ a ≤ n - a)).card

/-- The set of integers representable in exactly one way as the sum of two
    elements from `A` (with `a ≤ b`). -/
def UniqueRepSum (A : Set ℕ) : Set ℕ :=
  {n : ℕ | reprCount A n = 1}

/-- Count of integers in `{1, …, N}` that are NOT in the unique-representation
    sumset `B`. -/
def nonUniqueRepCount (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => n ∉ UniqueRepSum A)).card

/--
Erdős Problem #14, Part 1 [Er92c, Er97, Er97e]:

Let A ⊆ ℕ and let B be the set of integers representable in exactly one way as
the sum of two elements from A. Is it true that for all ε > 0 and large N,
  |{1, …, N} \ B| ≫_ε N^{1/2 - ε}?
-/
theorem erdos_problem_14a :
    ∀ A : Set ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        C * (N : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (nonUniqueRepCount A N : ℝ) :=
  sorry

/--
Erdős Problem #14, Part 2 [Er92c, Er97, Er97e]:

Let A ⊆ ℕ and let B be the set of integers representable in exactly one way as
the sum of two elements from A. Is it possible that
  |{1, …, N} \ B| = o(N^{1/2})?

That is, does there exist A such that the non-uniquely-representable integers
in {1, …, N} grow slower than N^{1/2}?
-/
theorem erdos_problem_14b :
    ∃ A : Set ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (nonUniqueRepCount A N : ℝ) ≤ ε * (N : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

end
