import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

noncomputable section

open Nat

/--
The number of elements of A in {1, …, x}.
-/
noncomputable def countIn (A : Set ℕ) (x : ℕ) : ℕ :=
  Nat.card { a : ℕ // a ∈ A ∧ 1 ≤ a ∧ a ≤ x }

/--
Erdős Problem #428 [ErGr80]:

Is there a set A ⊆ ℕ such that, for infinitely many n, all of n - a are prime
for all a ∈ A with 0 < a < n, and
  liminf |A ∩ [1,x]| / π(x) > 0?

Erdős and Graham could show this is true (assuming the prime k-tuple conjecture)
if we replace liminf by limsup.

Tags: number theory, primes
-/
theorem erdos_problem_428 :
    ∃ (A : Set ℕ),
      (∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
        ∀ a ∈ A, 0 < a → a < n → Nat.Prime (n - a)) ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ x : ℕ, 0 < x →
          c ≤ (countIn A x : ℝ) / (Nat.primeCounting x : ℝ) :=
  sorry

end
