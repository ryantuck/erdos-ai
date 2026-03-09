import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat

noncomputable section

/-!
# Erdős Problem #1139

Let $1 \leq u_1 < u_2 < \cdots$ be the sequence of integers with at most $2$
prime factors (counted with multiplicity). Is it true that
$$\limsup \frac{u_{k+1} - u_k}{\log k} = \infty?$$

Reference: [Va99, 1.4]
https://www.erdosproblems.com/1139
-/

/-- A positive integer has at most 2 prime factors (counted with multiplicity). -/
def hasAtMostTwoPrimeFactors (n : ℕ) : Prop :=
  1 ≤ n ∧ n.primeFactorsList.length ≤ 2

/-- The k-th element (0-indexed) of the increasing sequence of positive integers
    with at most 2 prime factors. -/
noncomputable def almostPrime2 (k : ℕ) : ℕ :=
  nth hasAtMostTwoPrimeFactors k

/-- Gap between consecutive elements of the sequence. -/
noncomputable def almostPrime2Gap (k : ℕ) : ℕ :=
  almostPrime2 (k + 1) - almostPrime2 k

/--
Erdős Problem #1139 [Va99, 1.4]:

Let 1 ≤ u₁ < u₂ < ⋯ be the sequence of positive integers with at most 2 prime
factors (counted with multiplicity). Is it true that
  limsup (u_{k+1} - u_k) / log k = ∞?

Equivalently: for every M > 0, there exist arbitrarily large k such that the gap
u_{k+1} - u_k exceeds M · log k.
-/
theorem erdos_problem_1139 :
    ∀ M : ℝ, M > 0 → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧
      M * Real.log (k : ℝ) < (almostPrime2Gap k : ℝ) :=
  sorry

end
