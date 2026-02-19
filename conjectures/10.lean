import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic

open Finset BigOperators Nat

/--
Erdős Problem #10:
Is there some k such that every large integer is the sum of a prime and at most k powers of 2?
-/
theorem erdos_problem_10_conjecture :
  ∃ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ p : ℕ, p.Prime ∧ ∃ (S : Finset ℕ), S.card ≤ k ∧ n = p + ∑ i ∈ S, 2^i :=
sorry
