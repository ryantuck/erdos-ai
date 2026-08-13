import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

open Nat Finset

namespace Erdos1093

/--
A natural number `m` is `k`-smooth if all of its prime factors are at most `k`.

This is the classical smoothness convention (`p ≤ k`), matching the source's
"divisible only by primes ≤ k". Note that Mathlib's `Nat.smoothNumbers k`
instead requires `p < k`, which differs from the source exactly when `k` is
prime — do not swap one for the other.
-/
def IsSmooth (k m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ≤ k

open Classical in
/--
Whether the deficiency of `C(n, k)` is defined: it is defined when `n ≥ 2k`
and `C(n, k)` is not divisible by any prime `p ≤ k`.
-/
def deficiencyDefined (n k : ℕ) : Prop :=
  2 * k ≤ n ∧ ∀ p : ℕ, p.Prime → p ≤ k → ¬(p ∣ Nat.choose n k)

open Classical in
/--
The deficiency of `C(n, k)` (when defined) is the number of `0 ≤ i < k` such that
`n - i` is `k`-smooth.

(On the intended domain `2k ≤ n` we have `i < k ≤ n`, so the truncated ℕ
subtraction `n - i` never engages; the values `n - i` range over
`n, n-1, …, n-k+1`, all positive.)
-/
noncomputable def deficiency (n k : ℕ) : ℕ :=
  ((range k).filter (fun i => IsSmooth k (n - i))).card

/--
Erdős Problem #1093, Part 1 (OPEN) [ELS88,p.522]:

A problem of Erdős, Lacampagne, and Selfridge, also asked in the 1986 problem
session of West Coast Number Theory. For n ≥ 2k, define the deficiency
of C(n,k) as the number of 0 ≤ i < k such that n - i is k-smooth, provided that
C(n,k) is not divisible by any prime p ≤ k.

Are there infinitely many binomial coefficients with deficiency 1?

Known examples with deficiency 1 (there are 58 examples with n ≤ 10^5) include
C(7,3), C(13,4), C(14,4), C(23,5), C(62,6), C(94,10), C(95,10).

In [ELS93] it is proved that if the deficiency exists and is ≥ 1 then
n ≪ 2^k √k (see `erdos_problem_1093_els93_bound` below).

See also Erdős problems #384 and #1094.

References:
[ELS88] Erdős, P., Lacampagne, C. B., Selfridge, J. L. (1988), p. 522.
(Stub: cited as [ELS88,p.522] on the source page; full bibliographic details
were not recoverable offline.)
[ELS93] Erdős, P., Lacampagne, C. B., Selfridge, J. L., Estimates of the
least prime factor of a binomial coefficient. Math. Comp. (1993), 215–224.
(Volume number not recoverable offline.)

Source: erdosproblems.com/1093 (page last edited 27 December 2025,
accessed 2026-03-09).
-/
theorem erdos_problem_1093_part1 :
    Set.Infinite {p : ℕ × ℕ | deficiencyDefined p.1 p.2 ∧ deficiency p.1 p.2 = 1} :=
  sorry

/--
Erdős Problem #1093, Part 2 (OPEN) [ELS88,p.522]:

Are there only finitely many binomial coefficients with deficiency > 1?

The examples below are the only known ones with deficiency > 1.
Deficiency 2: C(44,8), C(74,10), C(174,12), C(239,14), C(5179,27),
C(8413,28), C(8414,28), C(96622,42).
Deficiency 3: C(46,10), C(47,10), C(241,16), C(2105,25), C(1119,27),
C(6459,33).
Deficiency 4: C(47,11). Deficiency 9: C(284,28).

Barreto (in the comments on the source page) has given a positive answer to
this question, conditional on two (strong) conjectures.
-/
theorem erdos_problem_1093_part2 :
    Set.Finite {p : ℕ × ℕ | deficiencyDefined p.1 p.2 ∧ deficiency p.1 p.2 > 1} :=
  sorry

/--
Erdős Problem #1093, partial result (SOLVED) [ELS93]:

Erdős, Lacampagne, and Selfridge proved that if the deficiency exists and is
≥ 1 then n ≪ 2^k √k.

Encoding note: over ℕ we write the bound as `C * 2 ^ k * (Nat.sqrt k + 1)`.
Any pair with deficiency ≥ 1 has k ≥ 1, and for k ≥ 1 the factor
`Nat.sqrt k + 1` lies in [√k, 2√k], so the existential-constant form is
equivalent to the real bound C · 2^k · √k.

NOT COMPILE-VERIFIED: statement added during Fable review without a Lean
toolchain; check with `lake build` before downstream use.
-/
theorem erdos_problem_1093_els93_bound :
    ∃ C : ℕ, 0 < C ∧ ∀ n k : ℕ, deficiencyDefined n k → 1 ≤ deficiency n k →
      n ≤ C * 2 ^ k * (Nat.sqrt k + 1) :=
  sorry

/--
Erdős Problem #1093, smallest listed example (SOLVED) [ELS88]:

C(7,3) = 35 has deficiency 1: no prime p ≤ 3 divides 35, and among the
numbers 7 - i for 0 ≤ i < 3 (namely 7, 6, 5) exactly one (6 = 2·3) is
3-smooth. This is the first entry of the deficiency-1 list on the source
page, and pins down the `p ≤ k` smoothness convention (under the strict
`p < k` convention of `Nat.smoothNumbers`, 6 would not count as 3-smooth
and C(7,3) would get deficiency 0, contradicting the source's data).

NOT COMPILE-VERIFIED: statement added during Fable review without a Lean
toolchain; check with `lake build` before downstream use.
-/
theorem erdos_problem_1093_example_7_3 :
    deficiencyDefined 7 3 ∧ deficiency 7 3 = 1 :=
  sorry

end Erdos1093
