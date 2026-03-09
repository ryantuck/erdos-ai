import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset BigOperators

noncomputable section

/-- A natural number is a **product of consecutive primes** if it equals
    p_i · p_{i+1} · ⋯ · p_j for some 0 ≤ i ≤ j, where p_l is the l-th prime
    (0-indexed: p_0 = 2, p_1 = 3, …). -/
def IsProductOfConsecutivePrimes (m : ℕ) : Prop :=
  ∃ i j : ℕ, i ≤ j ∧ m = ∏ l ∈ Finset.Icc i j, Nat.nth Nat.Prime l

/--
Erdős Problem #386 [ErGr80, p.74]:

Let 2 ≤ k ≤ n − 2. Can C(n, k) be the product of consecutive primes
infinitely often? For example C(21, 2) = 2 · 3 · 5 · 7.

The conjecture is that there are infinitely many such pairs (n, k).
-/
theorem erdos_problem_386 :
    ∀ N : ℕ, ∃ n k : ℕ, N ≤ n ∧ 2 ≤ k ∧ k ≤ n - 2 ∧
      IsProductOfConsecutivePrimes (Nat.choose n k) :=
  sorry

end
