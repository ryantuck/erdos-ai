import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.IsPrimePow

open Finset BigOperators

noncomputable section

/-!
# Erdős Problem #435

Let n ∈ ℕ with n ≠ p^k for any prime p and k ≥ 0. What is the largest integer
not of the form ∑_{1 ≤ i < n} c_i · C(n, i) where the c_i ≥ 0 are integers?

If n = ∏ p_k^{a_k} then the largest integer not of this form is
∑_k (∑_{1 ≤ d ≤ a_k} C(n, p_k^d)) · (p_k - 1) − n.

First proved by Hwang and Song [HwSo24]. Independently found by Peake and Cambie.
-/

/-- The set of natural numbers representable as a non-negative integer linear
combination of the binomial coefficients C(n, i) for 1 ≤ i ≤ n-1. -/
def BinomialRepresentable (n : ℕ) : Set ℕ :=
  {m : ℕ | ∃ c : ℕ → ℕ, m = ∑ i ∈ range (n - 1), c i * n.choose (i + 1)}

/-- The formula for the answer to Erdős Problem #435:
  ∑_p (∑_{d=1}^{v_p(n)} C(n, p^d)) · (p - 1) − n
where the outer sum ranges over primes p dividing n and v_p(n) is the
p-adic valuation of n. -/
noncomputable def erdos435Formula (n : ℕ) : ℕ :=
  (∑ p ∈ n.factorization.support,
    (∑ d ∈ range (n.factorization p), n.choose (p ^ (d + 1))) * (p - 1)) - n

/-- Erdős Problem #435 [ErGr80, p.86] (PROVED):

Let n ∈ ℕ with n ≥ 2 and n not a prime power. The largest natural number
not representable as ∑_{1 ≤ i < n} c_i · C(n, i) with non-negative integers c_i
equals ∑_p (∑_{d=1}^{v_p(n)} C(n, p^d)) · (p - 1) − n,
where the outer sum is over primes p dividing n.

First proved by Hwang and Song [HwSo24]. Independently found by Peake and Cambie. -/
theorem erdos_problem_435 (n : ℕ) (hn : 2 ≤ n) (hnpp : ¬IsPrimePow n) :
    erdos435Formula n ∉ BinomialRepresentable n ∧
    ∀ m : ℕ, m > erdos435Formula n → m ∈ BinomialRepresentable n :=
  sorry

end
