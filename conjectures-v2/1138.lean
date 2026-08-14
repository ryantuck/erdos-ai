import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open Finset Real

/-!
# Erdős Problem #1138

Let x/2 < y < x and C > 1. If d = max_{p_n < x} (p_{n+1} - p_n), where p_n
denotes the nth prime, then is it true that
  π(y + Cd) - π(y) ~ Cd / log y?

Status: OPEN per erdosproblems.com/1138 (page last edited 23 January 2026,
accessed 2026-02-23) — "This is open, and cannot be resolved with a finite
computation."

The problem is a yes/no question; following this corpus's convention for open
questions, the theorem below states the conjectured ("yes") direction as a
direct assertion with the parameters C and ε as theorem binders. In styled
question form it would be
`answer(sorry) ↔ ∀ (C : ℝ), 1 < C → ∀ (ε : ℝ), 0 < ε → ∃ N, …`
with those quantifiers moved inside the iff.

Page remarks: "In other words, prove the expected asymptotic formula for the
number of primes in the interval [y, y + Cd]. This is a curious combination
of two well-studied problems: find the minimum h = h(y) for which one obtains
the expected asymptotic π(y + h) - π(y) ~ h / log y, and understand the
asymptotic behaviour of d = max_{p_n < x} (p_{n+1} - p_n). The conjectured
size of d is ≈ (log x)², which is far below the h we can obtain such an
asymptotic for, even assuming the Riemann hypothesis (which delivers an
asymptotic for h = y^{1/2+o(1)})."

Tags: number theory, primes
Related OEIS sequences: none listed (the database marks them "Possible").
Formalised statement per the page: "No" as of the 2026-02-23 access.

Reference: [Va99, 1.3]
https://www.erdosproblems.com/1138

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §1.3. (Honest stub from the upstream contributing guide's canonical entry;
  the site's /latex/1138 bibliography was never captured, so fuller
  bibliographic detail is DEFERRED. Note: the "Vardi, I." attribution for
  this key carried by some sibling artifacts is a hallucination and is
  deliberately not reproduced here.)
-/

namespace Erdos1138

/-- The maximal gap between consecutive primes below x:
    for each index k with the k-th prime (0-indexed) less than x,
    compute the gap to the next prime and take the maximum — the source's
    d = max_{p_n < x} (p_{n+1} - p_n). For the largest admissible k the next
    prime p_{k+1} may be ≥ x, exactly as in the source (whose condition
    constrains p_n only). The ℕ subtraction never truncates because
    `Nat.nth Nat.Prime` is strictly monotone. Returns 0 (`sup` of the empty
    range) when there are no primes less than x, i.e. for x ≤ 2. -/
noncomputable def maxPrimeGap (x : ℕ) : ℕ :=
  (range (Nat.primeCounting' x)).sup
    (fun k => Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k)

/--
Erdős Problem #1138 [Va99, 1.3] (OPEN):

Let x/2 < y < x and C > 1. If d = max_{p_n < x} (p_{n+1} - p_n) is the maximal
prime gap below x, where p_n denotes the n-th prime, then is it true that
  π(y + Cd) - π(y) ~ Cd / log y?

In other words, the expected asymptotic formula for the number of primes in the
interval [y, y + Cd] holds. This is a curious combination of two well-studied
problems: finding the minimum h = h(y) for which π(y + h) - π(y) ~ h / log y,
and understanding the maximal prime gap d. The conjectured size of d is
≈ (log x)², which is far below the h for which such an asymptotic is
obtainable even assuming the Riemann hypothesis (which delivers it for
h = y^{1/2+o(1)}).

Encoding notes:
* Stated in the conjectured ("yes") direction, as this corpus does for open
  yes/no questions; the ε–N form unfolds "~ as x → ∞, uniformly in
  x/2 < y < x" for each fixed C > 1.
* Since y : ℕ and primes are integers, a prime p satisfies p ≤ y + Cd iff
  p ≤ y + ⌊Cd⌋, so the `Nat.floor` in the numerator argument is lossless;
  the denominator keeps the exact real Cd / log y of the source.
* The constraints x < 2y and y < x force y ≥ 2 and x ≥ 3 for every admissible
  pair, hence log y ≥ log 2 > 0 and maxPrimeGap x ≥ 1: no division by zero is
  ever consulted. For x ≤ 2 the inner quantifier over y is vacuous.
* Quantifying y over ℕ rather than ℝ is equivalent to the real-variable
  reading of the source: for real y ∈ (n, n+1) the count π(y + Cd) − π(y)
  differs from its value at a neighbouring admissible integer by at most a
  bounded amount and log y / log n → 1 uniformly; since d / log x → ∞
  (Westzynthius 1931), the expected count Cd / log y → ∞ and the perturbation
  is asymptotically negligible in the ratio.

Tags: number theory, primes
-/
theorem erdos_problem_1138 (C : ℝ) (hC : 1 < C) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ∀ y : ℕ, x < 2 * y → y < x →
        |((Nat.primeCounting (y + ⌊C * (maxPrimeGap x : ℝ)⌋₊) : ℝ) -
          (Nat.primeCounting y : ℝ)) /
          (C * (maxPrimeGap x : ℝ) / log (y : ℝ)) - 1| < ε :=
  sorry

end Erdos1138

end
