import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

open Finset BigOperators

noncomputable section

/-- The largest prime factor of a natural number n. Returns 0 if n ≤ 1. -/
def largestPrimeFactor380 (n : ℕ) : ℕ :=
  n.factorization.support.sup id

/-- An interval [u, v] is 'bad' if the greatest prime factor of ∏_{u ≤ m ≤ v} m
    occurs with exponent greater than 1 in the factorization of that product. -/
def IsBadInterval (u v : ℕ) : Prop :=
  let P := ∏ m ∈ Finset.Icc u v, m
  let p := largestPrimeFactor380 P
  u ≤ v ∧ 0 < p ∧ 1 < P.factorization p

/-- A natural number n is contained in at least one bad interval. -/
def InBadInterval (n : ℕ) : Prop :=
  ∃ u v : ℕ, u ≤ n ∧ n ≤ v ∧ IsBadInterval u v

/-- B(x): the number of n ≤ x contained in at least one bad interval. -/
def B380 (x : ℕ) : ℕ :=
  Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ x ∧ InBadInterval n}

/-- The count of n ≤ x such that P(n)² | n, where P(n) is the largest prime factor. -/
def squareDivCount380 (x : ℕ) : ℕ :=
  Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ x ∧
    0 < largestPrimeFactor380 n ∧ (largestPrimeFactor380 n) ^ 2 ∣ n}

/--
Erdős Problem #380 [ErGr80,p.73]:

We call an interval [u,v] 'bad' if the greatest prime factor of ∏_{u ≤ m ≤ v} m
occurs with an exponent greater than 1. Let B(x) count the number of n ≤ x which
are contained in at least one bad interval. Is it true that

  B(x) ~ #{n ≤ x : P(n)² | n},

where P(n) is the largest prime factor of n?

The asymptotic equivalence B(x) ~ f(x) is formalized as: for every ε > 0, for
sufficiently large x, (1 - ε) · f(x) ≤ B(x) ≤ (1 + ε) · f(x).
-/
theorem erdos_problem_380 :
    ∀ ε : ℝ, 0 < ε →
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (1 - ε) * (squareDivCount380 x : ℝ) ≤ (B380 x : ℝ) ∧
      (B380 x : ℝ) ≤ (1 + ε) * (squareDivCount380 x : ℝ) :=
  sorry

end
