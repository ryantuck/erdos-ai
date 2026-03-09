import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

open Nat

/--
Erdős Problem #699 [ErSz78]:

Is it true that for every 1 ≤ i < j ≤ n/2 there exists some prime p ≥ i
such that p ∣ gcd(C(n, i), C(n, j))?

A problem of Erdős and Szekeres. A theorem of Sylvester and Schur says that
for any 1 ≤ i ≤ n/2 there exists some prime p > i which divides C(n, i).
-/
theorem erdos_problem_699 :
    ∀ n : ℕ, ∀ i j : ℕ,
      1 ≤ i → i < j → j ≤ n / 2 →
      ∃ p : ℕ, Nat.Prime p ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j) :=
  sorry
