import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

open Finset

/-!
# Erdős Problem #291

Let n ≥ 1 and define L_n to be the least common multiple of {1, ..., n} and a_n by
  ∑_{k=1}^{n} 1/k = a_n / L_n.
Is it true that gcd(a_n, L_n) = 1 and gcd(a_n, L_n) > 1 both occur for infinitely
many n?

The second question is trivially yes (Steinerberger): any n whose leading digit in
base 3 is 2 has 3 ∣ gcd(a_n, L_n).

The first question remains open.
-/

/-- The least common multiple of {1, ..., n}. -/
def lcmUpTo (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

/-- The numerator a_n defined by ∑_{k=1}^{n} 1/k = a_n / L_n, i.e.,
    a_n = ∑_{k=1}^{n} L_n / k. Since L_n is divisible by every k ≤ n,
    each summand is a natural number. -/
def harmonicLcmNumerator (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sum fun k => lcmUpTo n / k

/--
Erdős Problem #291 [ErGr80, p.34]:

Both gcd(a_n, L_n) = 1 and gcd(a_n, L_n) > 1 occur for infinitely many n ≥ 1,
where L_n = lcm(1, ..., n) and a_n = L_n · H_n = ∑_{k=1}^{n} L_n / k.
-/
theorem erdos_problem_291 :
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      Nat.gcd (harmonicLcmNumerator n) (lcmUpTo n) = 1) ∧
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      Nat.gcd (harmonicLcmNumerator n) (lcmUpTo n) > 1) :=
  sorry
