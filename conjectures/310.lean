import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic

open Finset BigOperators

/--
Erdős Problem #310 (PROVED) [ErGr80]:

Let α > 0 and N ≥ 1. Is it true that for any A ⊆ {1, …, N} with |A| ≥ αN
there exists some S ⊆ A such that a/b = ∑_{n ∈ S} 1/n with a ≤ b = O_α(1)?

That is, for every α > 0 there exists a constant C (depending only on α) such
that for every N ≥ 1 and every A ⊆ {1, …, N} with |A| ≥ αN, there exist
positive integers a ≤ b ≤ C and a nonempty subset S ⊆ A with ∑_{n ∈ S} 1/n = a/b.

Liu and Sawhney [LiSa24] observed that the main result of Bloom [Bl21] implies
a positive solution to this conjecture. They proved the more precise bound
b ≤ exp(O(1/α)), which they showed to be sharp.
-/
theorem erdos_problem_310 :
    ∀ α : ℝ, α > 0 →
      ∃ C : ℕ, 0 < C ∧
        ∀ N : ℕ, 1 ≤ N →
          ∀ A : Finset ℕ, (∀ n ∈ A, 1 ≤ n ∧ n ≤ N) →
            α * (N : ℝ) ≤ (A.card : ℝ) →
              ∃ S : Finset ℕ, S ⊆ A ∧ S.Nonempty ∧
                ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ b ≤ C ∧
                  ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = (a : ℚ) / (b : ℚ) :=
  sorry
