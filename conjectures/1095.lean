import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Filter

namespace Erdos1095

/--
A predicate that n > k+1 and all prime factors of C(n, k) are > k.
-/
def AllPrimeFactorsGt (n k : ℕ) : Prop :=
  k + 1 < n ∧ ∀ p : ℕ, p.Prime → p ∣ Nat.choose n k → k < p

/-- Erdős Problem #1095 (OPEN) [EES74]:

Let g(k) > k+1 be the smallest n such that all prime factors of C(n,k) are > k.
Estimate g(k).

Ecklund, Erdős, and Selfridge proved k^{1+c} < g(k) ≤ exp((1+o(1))k) for some c > 0.

They conjectured:
  (1) g(k) < L_k (the lcm of 1,...,k) for all large k
  (2) limsup g(k+1)/g(k) = ∞
  (3) liminf g(k+1)/g(k) = 0

Konyagin proved g(k) ≫ exp(c(log k)²) for some c > 0.

Heuristic evidence suggests log g(k) ≍ k / log k.

There exists c > 0 such that for all sufficiently large k, the smallest n > k+1
    with all prime factors of C(n,k) greater than k satisfies n > k^{1+c}. -/
theorem erdos_1095_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ (k : ℕ) in atTop,
      ∀ n : ℕ, AllPrimeFactorsGt n k → (k : ℝ) ^ (1 + c) < (n : ℝ) :=
  sorry

/-- For infinitely many k, g(k+1) > M * g(k) for any M
    (capturing limsup g(k+1)/g(k) = ∞). -/
theorem erdos_1095_limsup_ratio :
    ∀ M : ℝ, ∃ᶠ (k : ℕ) in atTop,
      ∃ n₁ n₂ : ℕ, AllPrimeFactorsGt n₁ k ∧ AllPrimeFactorsGt n₂ (k + 1) ∧
        (∀ m, AllPrimeFactorsGt m k → n₁ ≤ m) ∧
        (∀ m, AllPrimeFactorsGt m (k + 1) → n₂ ≤ m) ∧
        M * (n₁ : ℝ) < (n₂ : ℝ) :=
  sorry

/-- For infinitely many k, g(k+1) < ε * g(k) for any ε > 0
    (capturing liminf g(k+1)/g(k) = 0). -/
theorem erdos_1095_liminf_ratio :
    ∀ ε : ℝ, 0 < ε → ∃ᶠ (k : ℕ) in atTop,
      ∃ n₁ n₂ : ℕ, AllPrimeFactorsGt n₁ k ∧ AllPrimeFactorsGt n₂ (k + 1) ∧
        (∀ m, AllPrimeFactorsGt m k → n₁ ≤ m) ∧
        (∀ m, AllPrimeFactorsGt m (k + 1) → n₂ ≤ m) ∧
        (n₂ : ℝ) < ε * (n₁ : ℝ) :=
  sorry

end Erdos1095
