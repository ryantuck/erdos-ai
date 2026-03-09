import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Nat Filter

/--
Erdős Problem #463 [ErGr80] [Er92e]:

Is there a function f with f(n) → ∞ as n → ∞ such that, for all large n,
there is a composite number m such that n + f(n) < m < n + p(m)?
Here p(m) denotes the least prime factor of m.
-/
theorem erdos_problem_463 :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ m : ℕ, ¬ m.Prime ∧ 2 ≤ m ∧
          n + f n < m ∧ m < n + m.minFac :=
  sorry
