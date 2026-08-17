import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Erdős Problem 69

*Reference:* [erdosproblems.com/69](https://www.erdosproblems.com/69)
(accessed 2026-03-05; page edition "last edited 02 December 2025"; page content
recovered from the archived captures in the original pipeline session's log,
`claude-session-logs/4f14c6c8-17cd-44ac-9150-020e06223008.jsonl` — line 9, a Read of
the then-extant `html/69.html` (full 27 KB page), and line 13, a Read of
`tidy/69.html` (the problem-box div); the two captures agree on statement, status,
citations, and remarks. The live site is unreachable from the review container.)

Statement (verbatim from the site): "Is $$\sum_{n\geq 2}\frac{\omega(n)}{2^n}$$
irrational? (Here $\omega(n)$ counts the number of distinct prime divisors of
$n$.)" Cited on the page as [Er68d][ErGr80][Er88c,p.102][Er90][Er97f]. Tags:
number theory | irrationality. No prize. The related OEIS sequence is A262153.

Status: **PROVED** (tooltip: "This has been solved in the affirmative."). The
teorth/erdosproblems metadata mirror (`data/problems.yaml`, commit a09c7a2,
2026-08-14) agrees: proved, last update 2025-12-02, OEIS A262153, tags number
theory/irrationality. The upstream google-deepmind/formal-conjectures repository
(HEAD dd1c2beb, fetched 2026-08-16) has `ErdosProblems/69.lean` stating
`erdos_69 : Irrational <| ∑' n, ω (n + 2) / 2 ^ (n + 2)` (category `textbook`)
plus a `research solved` variant recording Tao's identity with Problem #257 —
matching the page's "Formalised statement? Yes" link. Upstream's index shift
`n + 2` and this file's `if n < 2` guard describe the same series term-for-term.

Remarks from the page: "Erdős [Er48] proved that $\sum_n \frac{d(n)}{2^n}$ is
irrational, where $d(n)$ is the divisor function. Pratt [Pr24] has proved this is
irrational, conditional on a uniform version of the prime $k$-tuples conjecture.
Tao has observed that this is a special case of [257], since
$$\sum_{n\geq 2}\frac{\omega(n)}{2^n}=\sum_p \frac{1}{2^p-1}.$$ This sum was
proved to be irrational unconditionally by Tao and Teräväinen [TaTe25]."
Additional thanks (per the page): Vjekoslav Kovac and Terence Tao.

Tao's identity is formalized as a variant below. The Erdős [Er48] divisor-function
result is deliberately left as prose: `Nat.divisors` is not reachable from this
file's imports, and adding an import is a compiler-dependent change out of scope
for this pipeline (Problem #257's page/file carry that variant). The Pratt [Pr24]
conditional result is also left as prose: formalizing it would require encoding a
"uniform version of the prime $k$-tuples conjecture", which the page does not
state precisely.

References (per-entry provenance; the page's `/latex/69` and `/bibs/` payloads
were NOT captured in the logs, so entries below come from the upstream
formal-conjectures repository and corpus consensus, or are key-only stubs, marked
DEFERRED — nothing is fabricated):

- [Er68d] Erdős, P. (1968). (Key-only stub: no expansion of this key is
  recoverable offline — no sibling file in this corpus or upstream expands it, and
  no `/latex` capture carries it; DEFERRED. Same conclusion as the Problem #68
  review, which shares the key.)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement Mathématique
  (1980). (Upstream formal-conjectures and corpus consensus; DEFERRED for
  volume-level data.)
- [Er88c] Erdős, P., _On the irrationality of certain series: problems and
  results_. New advances in transcendence theory (Durham, 1986) (1988), 102-109.
  (Upstream `ErdosProblems/1051.lean` and corpus consensus; the page's pin
  [Er88c, p.102] falls on this entry's page range, corroborating it; DEFERRED.)
- [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul
  Erdős (1990), 467-478. (Upstream `ErdosProblems/115.lean` and corpus consensus;
  DEFERRED.)
- [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and
  probability (Cambridge, 1993) (1997), 1-10. (Upstream `ErdosProblems/24.lean`,
  `119.lean`; note the Problem #68/#19 reviews found conflicting corpus
  expansions of this key, so treat as unconfirmed; DEFERRED.)
- [Er48] Erdős, P., _On arithmetical properties of Lambert series_. J. Indian
  Math. Soc. (N.S.) (1948), 63-66. (Upstream `ErdosProblems/257.lean`,
  `1049.lean`; DEFERRED for volume-level data.)
- [Pr24] Pratt, K. (2024). (Key-only stub: no expansion recoverable offline —
  the only Pratt entries in the corpus are the distinct keys [Pr22]/[BPZ24];
  DEFERRED.)
- [TaTe25] Tao, T. and Teräväinen, J., _Quantitative correlations and some
  problems on prime factors of consecutive integers_. arXiv:2512.01739 (2025).
  (Upstream `ErdosProblems/248.lean`.)
-/

open scoped Topology

/--
Erdős Problem #69 [Er68d, ErGr80, Er88c (p.102), Er90, Er97f] — PROVED:

Is the sum ∑_{n≥2} ω(n)/2ⁿ irrational, where ω(n) counts the number of
distinct prime divisors of n?

Erdős [Er48] proved the analogous ∑_n d(n)/2ⁿ (d = divisor function) is
irrational. Pratt [Pr24] proved the present sum irrational conditional on a
uniform version of the prime k-tuples conjecture. Tao observed that this is the
special case A = {primes} of Problem #257, since ∑_{n≥2} ω(n)/2ⁿ = ∑_p 1/(2^p - 1)
(variant `erdos_problem_69.variants.tao_prime_sum`). This sum was proved to be
irrational unconditionally by Tao and Teräväinen [TaTe25], so the problem is
SOLVED in the affirmative (page last edited 02 December 2025). The sum evaluates
to 1/3 + 1/7 + 1/31 + 1/127 + ⋯ ≈ 0.5169; the page's related OEIS sequence is
A262153 (contents unverifiable offline).

Encoding notes: the problem is a yes/no question resolved affirmatively;
following this corpus's convention (no `answer()` macro with Mathlib-only
imports), this theorem is the direct assertion of the *true* direction —
irrationality — so the polarity matches the resolution. `n.primeFactors.card` is
exactly ω(n), and the `if n < 2` guard zeroes the n = 0, 1 terms so the tsum is
literally ∑_{n≥2} ω(n)/2ⁿ; the guard is in fact redundant (ω(0) = ω(1) = 0 since
`Nat.primeFactors 0 = Nat.primeFactors 1 = ∅`) but harmless and explicit. The
series is summable (0 ≤ ω(n) ≤ log₂ n ≤ n and ∑ n/2ⁿ < ∞), so `∑'` denotes the
honest sum — the irrationality claim is about the genuine real number, not a
junk value. All arithmetic happens in ℝ after coercion; no ℕ subtraction or
division occurs.
-/
theorem erdos_problem_69 :
    Irrational (∑' (n : ℕ), if n < 2 then (0 : ℝ)
      else (n.primeFactors.card : ℝ) / (2 : ℝ) ^ n) :=
  sorry

/--
Page-confirmed variant (Tao's observation): ∑_{n≥2} ω(n)/2ⁿ = ∑_p 1/(2^p - 1),
exhibiting Problem #69 as the special case A = {primes} of Problem #257
(is ∑_{n∈A} 1/(2ⁿ - 1) irrational for every infinite A ⊆ ℕ?). The identity is a
nonnegative-terms interchange of summation (Tonelli):
∑_{n≥2} ω(n)/2ⁿ = ∑_p ∑_{m : p∣m} 1/2^m = ∑_p ∑_{k≥1} (1/2^p)^k
= ∑_p 1/(2^p - 1). The prime-indexed sum is encoded over all of ℕ with an
`if p.Prime` guard (non-primes contribute 0); the subtraction 2^p - 1 is real
subtraction, and the guard admits only p ≥ 2, so no denominator vanishes. The
upstream formal-conjectures file records the same identity as a `research solved`
variant (`erdos_69.variants.specialisation_of_erdos_257`).

NOTE: this variant was added by the Fable review and is NOT compile-verified; it
uses only constructs already present in the file (tsum, if-guards, real division
and casts, ℕ-exponent powers on ℝ) plus `Nat.Prime`, which is transitively
reachable from the existing `Mathlib.Data.Nat.PrimeFin` import (verified against
the Mathlib import graph: `PrimeFin` → `Nat.Factors` → `Nat.Prime.Basic` →
`Nat.Prime.Defs`, which also carries the `Decidable (Nat.Prime p)` instance the
`if` requires).
-/
theorem erdos_problem_69.variants.tao_prime_sum :
    (∑' (n : ℕ), if n < 2 then (0 : ℝ)
      else (n.primeFactors.card : ℝ) / (2 : ℝ) ^ n)
      = ∑' (p : ℕ), if p.Prime then (1 : ℝ) / ((2 : ℝ) ^ p - 1) else 0 :=
  sorry
