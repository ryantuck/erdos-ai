import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Filter

/-!
# Erdős Problem #1095 (OPEN) [EES74]

Let g(k) > k+1 be the smallest n such that all prime factors of C(n,k) are > k.
Estimate g(k).

A question of Ecklund, Erdős, and Selfridge [EES74], who proved
k^{1+c} < g(k) ≤ exp((1+o(1))k) for some constant c > 0, and conjectured:
  (1) g(k) < L_k = [1,...,k] (the least common multiple of all integers ≤ k)
      for all large k
  (2) limsup g(k+1)/g(k) = ∞
  (3) liminf g(k+1)/g(k) = 0

The lower bound was improved by Erdős, Lacampagne, and Selfridge [ELS93] and by
Granville and Ramaré [GrRa96]. The current record is g(k) ≫ exp(c(log k)²) for
some c > 0, due to Konyagin [Ko99b].

Erdős, Lacampagne, and Selfridge [ELS93] write "it is clear to every
right-thinking person" that g(k) ≥ exp(c·k/log k) for some constant c > 0.
Sorenson, Sorenson, and Webster [SSW20] give heuristic evidence that
log g(k) ≍ k/log k.

See also Erdős problem #1094. Related OEIS sequence: A003458.

Status: OPEN at erdosproblems.com/1095 (page edition 12 January 2026, accessed
2026-03-09). An upstream formalization exists at google-deepmind/formal-conjectures,
`FormalConjectures/ErdosProblems/1095.lean`.

References:
- [EES74] Ecklund, Jr., E. F., Erdős, P. and Selfridge, J. L., "A new function
  associated with the prime factors of (n choose k)". Math. Comp. (1974), 647–649.
- [ELS93] Erdős, P., Lacampagne, C. B. and Selfridge, J. L., "Estimates of the
  least prime factor of a binomial coefficient". Math. Comp. (1993), 215–224.
- [GrRa96] Granville, A. and Ramaré, O., "Explicit bounds on exponential sums and
  the scarcity of squarefree binomial coefficients". Mathematika (1996), 73–107.
- [Ko99b] Konyagin, S. V., "Estimates of the least prime factor of a binomial
  coefficient". Mathematika (1999), 41–55.
- [SSW20] Sorenson, B., Sorenson, J. and Webster, J., "An algorithm and estimates
  for the Erdős–Selfridge function". (2020), 371–385.

(Journal volume numbers are not recorded above: they are absent from the sources
recoverable offline and are deliberately not fabricated.)
-/

namespace Erdos1095

/--
A predicate that n > k+1 and all prime factors of C(n, k) are > k.

g(k) is the *least* n satisfying `AllPrimeFactorsGt n k` (well-definedness of g is
part of [EES74]'s upper bound). Lower bounds on g(k) are stated below as bounds on
*every* such n (equivalent, since every witness is ≥ the least one); upper bounds
as the existence of *some* such n.
-/
def AllPrimeFactorsGt (n k : ℕ) : Prop :=
  k + 1 < n ∧ ∀ p : ℕ, p.Prime → p ∣ Nat.choose n k → k < p

/-- [EES74] proved (solved): there exists c > 0 such that for all sufficiently large k,
    the smallest n > k+1 with all prime factors of C(n,k) greater than k satisfies
    n > k^{1+c}; i.e. k^{1+c} < g(k). -/
theorem erdos_1095_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ (k : ℕ) in atTop,
      ∀ n : ℕ, AllPrimeFactorsGt n k → (k : ℝ) ^ (1 + c) < (n : ℝ) :=
  sorry

/-- Conjectured in [EES74] (open): for any M, for infinitely many k,
    g(k+1) > M * g(k) (capturing limsup g(k+1)/g(k) = ∞). -/
theorem erdos_1095_limsup_ratio :
    ∀ M : ℝ, ∃ᶠ (k : ℕ) in atTop,
      ∃ n₁ n₂ : ℕ, AllPrimeFactorsGt n₁ k ∧ AllPrimeFactorsGt n₂ (k + 1) ∧
        (∀ m, AllPrimeFactorsGt m k → n₁ ≤ m) ∧
        (∀ m, AllPrimeFactorsGt m (k + 1) → n₂ ≤ m) ∧
        M * (n₁ : ℝ) < (n₂ : ℝ) :=
  sorry

/-- Conjectured in [EES74] (open): for any ε > 0, for infinitely many k,
    g(k+1) < ε * g(k) (capturing liminf g(k+1)/g(k) = 0). -/
theorem erdos_1095_liminf_ratio :
    ∀ ε : ℝ, 0 < ε → ∃ᶠ (k : ℕ) in atTop,
      ∃ n₁ n₂ : ℕ, AllPrimeFactorsGt n₁ k ∧ AllPrimeFactorsGt n₂ (k + 1) ∧
        (∀ m, AllPrimeFactorsGt m k → n₁ ≤ m) ∧
        (∀ m, AllPrimeFactorsGt m (k + 1) → n₂ ≤ m) ∧
        (n₂ : ℝ) < ε * (n₁ : ℝ) :=
  sorry

/-- [EES74] proved (solved): g(k) ≤ exp((1+o(1))k), i.e. there is f(k) → 0 with,
    for all sufficiently large k, some n > k+1 whose C(n,k) has all prime factors
    > k and n ≤ exp((1 + f(k))·k). (The upstream formal-conjectures file labels
    this bound "conjectured", but the source page states [EES74] *proved* it.) -/
theorem erdos_1095_upper_bound :
    ∃ f : ℕ → ℝ, Tendsto f atTop (nhds 0) ∧ ∀ᶠ (k : ℕ) in atTop,
      ∃ n : ℕ, AllPrimeFactorsGt n k ∧ (n : ℝ) ≤ Real.exp ((1 + f k) * (k : ℝ)) :=
  sorry

/-- Conjectured in [EES74] (open): g(k) < L_k = lcm(1,...,k) for all large k.
    Encoded without an lcm construct: for every positive common multiple L of
    1,...,k there is a witness n < L. Since every positive common multiple is a
    multiple of L_k (hence ≥ L_k), and L_k itself is one, this is equivalent to
    g(k) < L_k. (The guard 0 < L is essential: L = 0 is divisible by everything
    and no witness n < 0 exists.) -/
theorem erdos_1095_lcm_upper_bound :
    ∀ᶠ (k : ℕ) in atTop, ∀ L : ℕ, 0 < L → (∀ m : ℕ, 0 < m → m ≤ k → m ∣ L) →
      ∃ n : ℕ, AllPrimeFactorsGt n k ∧ n < L :=
  sorry

/-- Konyagin [Ko99b] proved (solved, the current record): g(k) ≫ exp(c(log k)²) for
    some c > 0. The implied multiplicative constant of ≫ is absorbed by slightly
    decreasing c, so it is stated as: for all sufficiently large k every witness n
    satisfies exp(c·(log k)²) ≤ n. -/
theorem erdos_1095_konyagin_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ (k : ℕ) in atTop,
      ∀ n : ℕ, AllPrimeFactorsGt n k → Real.exp (c * Real.log k ^ 2) ≤ (n : ℝ) :=
  sorry

/-- Erdős, Lacampagne, and Selfridge [ELS93] write "it is clear to every
    right-thinking person" that (open): g(k) ≥ exp(c·k/log k) for some c > 0. -/
theorem erdos_1095_els_lower_belief :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ (k : ℕ) in atTop,
      ∀ n : ℕ, AllPrimeFactorsGt n k → Real.exp (c * (k : ℝ) / Real.log k) ≤ (n : ℝ) :=
  sorry

/-- Sorenson, Sorenson, and Webster [SSW20] give heuristic evidence that (open):
    log g(k) ≍ k/log k, i.e. there are c₁, c₂ > 0 with, eventually,
    c₁·k/log k ≤ log g(k) ≤ c₂·k/log k. Since log is monotone, the lower half is
    stated for every witness n and the upper half via some witness n. -/
theorem erdos_1095_log_asymptotics :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ (k : ℕ) in atTop,
      (∀ n : ℕ, AllPrimeFactorsGt n k → c₁ * (k : ℝ) / Real.log k ≤ Real.log n) ∧
      (∃ n : ℕ, AllPrimeFactorsGt n k ∧ Real.log n ≤ c₂ * (k : ℝ) / Real.log k) :=
  sorry

end Erdos1095
