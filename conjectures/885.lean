import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.NatAbs
import Mathlib.Order.Fin.Basic

open Finset

/--
The factor difference set of a positive integer n:
  D(n) = { |a - b| : n = a * b }
Since a * b = n with a, b positive, |a - b| is a natural number.
We represent this as a `Set ℕ`.
-/
def factorDifferenceSet (n : ℕ) : Set ℕ :=
  { d : ℕ | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a * b = n ∧ d = Int.natAbs (a - b : ℤ) }

/--
Erdős Problem #885 [ErRo97]:

For integer n ≥ 1 we define the factor difference set of n by
  D(n) = { |a - b| : n = ab }.
Is it true that, for every k ≥ 1, there exist integers N₁ < ⋯ < N_k such that
  |⋂ᵢ D(Nᵢ)| ≥ k?

A question of Erdős and Rosenfeld, who proved this is true for k = 2.
Jiménez-Urroz proved this for k = 3 and Bremner proved this for k = 4.
-/
theorem erdos_problem_885 :
    ∀ k : ℕ, 0 < k →
      ∃ N : Fin k → ℕ,
        (∀ i : Fin k, 0 < N i) ∧
        (StrictMono N) ∧
        ∃ S : Finset ℕ, S.card ≥ k ∧
          ∀ d ∈ S, ∀ i : Fin k, d ∈ factorDifferenceSet (N i) :=
  sorry
