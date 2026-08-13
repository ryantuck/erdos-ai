import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Finite.Basic

open Nat

namespace Erdos1094

/--
Erdős Problem #1094 (OPEN) [ELS88][ELS93]:

For all n ≥ 2k, the least prime factor of C(n, k) is ≤ max(n/k, k),
with only finitely many exceptions.

The 14 known exceptions are explicitly listed in [ELS88]:
C(7,3), C(13,4), C(23,5), C(14,4), C(44,8), C(46,10), C(47,10),
C(47,11), C(62,6), C(74,10), C(94,10), C(95,10), C(241,16), C(284,28).

Remarks (erdosproblems.com/1094, page edition 24 October 2025, accessed
2026-03-09, recovered from archived session logs):

* A stronger form of problem [384], appearing in the paper of Erdős,
  Lacampagne, and Selfridge [ELS88]. Erdős observed that the least prime
  factor is always ≤ n/k provided n is sufficiently large depending on k.
  Selfridge [Se77] further conjectured that this always happens if
  n ≥ k² - 1, except for C(62,6) (see the variant below).
* [ELS88] also suggests the stronger conjecture that, with finitely many
  exceptions, the least prime factor is ≤ max(n/k, √k) (see the variant
  below), or perhaps even ≤ max(n/k, O(log k)). In [ELS93] they give
  further computational evidence and point out it is consistent with what
  they know that this holds with ≤ max(n/k, 13), with only 12 exceptions.
* Discussed in problems B31 and B33 of Guy's collection [Gu04]; Guy credits
  Selfridge with the conjecture that if n > 17.125k then C(n,k) has a prime
  factor p ≤ n/k (see the variant below).
* The threshold g(k) below which C(n,k) is guaranteed to be divisible by a
  prime ≤ k is the subject of problem [1095]. Related to problem [1093]:
  counterexamples can only occur for C(n,k) with deficiency ≥ 1.

References (keys as on erdosproblems.com; full bibliographic data not
recoverable offline — stubs only):
[ELS88] Erdős, Lacampagne, Selfridge (1988).
[ELS93] Erdős, Lacampagne, Selfridge (1993).
[Se77] Selfridge (1977).
[Gu04] Guy, Unsolved Problems in Number Theory (2004) — title inferred from
the page's "problem B31 and B33 of Guy's collection"; unverified.

Encoding notes: `n / k` is ℕ floor division, but since `minFac` is a natural
number, `minFac ≤ n / k ↔ minFac ≤ (n : ℝ) / k`, so the encoding is exact.
The hypothesis `1 ≤ k` excludes the degenerate k = 0 (C(n,0) = 1 has no
prime factor and n/k is undefined in the source).
-/
theorem erdos_problem_1094 :
    Set.Finite {p : ℕ × ℕ |
      let n := p.1
      let k := p.2
      1 ≤ k ∧ 2 * k ≤ n ∧
      ¬(Nat.choose n k).minFac ≤ max (n / k) k} :=
  sorry

/--
Variant (OPEN) [ELS88]: the stronger conjecture of Erdős, Lacampagne, and
Selfridge that, with only finitely many exceptions, for n ≥ 2k the least
prime factor of C(n, k) is ≤ max(n/k, √k).

Encoding note: for a natural number m, m ≤ √k ↔ m * m ≤ k, and
m ≤ n/k ↔ m ≤ ⌊n/k⌋, so `m ≤ n / k ∨ m * m ≤ k` is an exact rendering of
m ≤ max(n/k, √k) in ℕ arithmetic.
-/
theorem erdos_problem_1094_variant_sqrt :
    Set.Finite {p : ℕ × ℕ |
      let n := p.1
      let k := p.2
      let m := (Nat.choose n k).minFac
      1 ≤ k ∧ 2 * k ≤ n ∧
      ¬(m ≤ n / k ∨ m * m ≤ k)} :=
  sorry

/--
Variant (OPEN) [Se77]: Selfridge conjectured that for n ≥ 2k the least prime
factor of C(n, k) is ≤ n/k whenever n ≥ k² - 1, with the single exception
C(62,6) (whose least prime factor is 19 > 62/6).

Encoding note: n ≥ k² - 1 is rendered subtraction-free as `k * k ≤ n + 1`.
Verified numerically for all n ≤ 600: no other exception exists in that range.
-/
theorem erdos_problem_1094_variant_selfridge :
    ∀ n k : ℕ, 1 ≤ k → 2 * k ≤ n → k * k ≤ n + 1 → ¬(n = 62 ∧ k = 6) →
      (Nat.choose n k).minFac ≤ n / k :=
  sorry

/--
Variant (OPEN) [Gu04]: Guy (problems B31/B33) credits Selfridge with the
conjecture that if n > 17.125k then C(n, k) has a prime factor p ≤ n/k
(equivalently, its least prime factor is ≤ n/k).

Encoding note: 17.125 = 137/8, so n > 17.125k is rendered exactly as
`137 * k < 8 * n` (which also forces n > 2k for k ≥ 1).
-/
theorem erdos_problem_1094_variant_guy_selfridge :
    ∀ n k : ℕ, 1 ≤ k → 137 * k < 8 * n →
      (Nat.choose n k).minFac ≤ n / k :=
  sorry

end Erdos1094
