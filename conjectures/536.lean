import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset

/--
Erdős Problem #536 [Er64, Er70, Er73]:

Let ε > 0 and N be sufficiently large. Is it true that if A ⊆ {1, …, N}
has |A| ≥ εN then there must exist distinct a, b, c ∈ A such that
  lcm(a,b) = lcm(b,c) = lcm(a,c)?

This is false if we ask for four elements with the same pairwise lcm,
as shown by Erdős [Er62].
-/
theorem erdos_problem_536 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset ℕ,
          (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
          ε * (N : ℝ) ≤ (A.card : ℝ) →
          ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
            a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
            Nat.lcm a b = Nat.lcm b c ∧
            Nat.lcm b c = Nat.lcm a c :=
  sorry
