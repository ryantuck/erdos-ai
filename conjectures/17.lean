import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Set.Finite.Basic

/--
Erdős's conjecture on primes $p$ such that every even number $n \le p-3$
is a difference of two primes $q_1, q_2 \le p$.
-/
def HasDiffProperty (p : ℕ) : Prop :=
  Nat.Prime p ∧
  ∀ n : ℕ, Even n → n ≤ p - 3 →
    ∃ q1 q2 : ℕ, Nat.Prime q1 ∧ Nat.Prime q2 ∧ q1 ≤ p ∧ q2 ≤ p ∧ q1 - q2 = n

theorem erdos_problem_17 : Set.Infinite {p | HasDiffProperty p} :=
sorry
