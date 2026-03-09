import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset

/--
Erdős Problem #375 (Grimm's Conjecture) [Er72, Er73, ErGr80]:

Is it true that for any n, k ≥ 1, if n+1, …, n+k are all composite then there
are distinct primes p₁, …, pₖ such that pᵢ ∣ (n+i) for 1 ≤ i ≤ k?

Originally conjectured by Grimm [Gr69]. This is trivial when k ≤ 2. This is a
very difficult problem, since it implies pₙ₊₁ − pₙ < pₙ^(1/2 − c) for some
constant c > 0, in particular resolving Legendre's conjecture.
-/
theorem erdos_problem_375 :
    ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k →
      (∀ i : ℕ, 1 ≤ i → i ≤ k → ¬ Nat.Prime (n + i)) →
      ∃ p : ℕ → ℕ,
        (∀ i : ℕ, 1 ≤ i → i ≤ k → Nat.Prime (p i)) ∧
        (∀ i : ℕ, 1 ≤ i → i ≤ k → (p i) ∣ (n + i)) ∧
        (∀ i j : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → i ≠ j → p i ≠ p j) :=
  sorry
