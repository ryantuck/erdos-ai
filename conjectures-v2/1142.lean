import Mathlib.Data.Nat.Prime.Basic

/-!
# Erdős Problem #1142

Are there infinitely many $n$ (or any $n > 105$) such that $n - 2^k$ is prime
for all $1 < 2^k < n$?

Verbatim source statement (erdosproblems.com/1142): "Are there infinitely many
$n$ (or any $n>105$) such that $n-2^k$ is prime for all $1<2^k<n$?"

Status: OPEN per erdosproblems.com/1142 (page last edited 23 January 2026,
accessed 2026-02-23) — "This is open, and cannot be resolved with a finite
computation."

Remarks from the source page:
* The only known such $n$ are $4, 7, 15, 21, 45, 75, 105$. This is A039669 in
  the OEIS.
* Mientka and Weitzenkamp [MiWe69] have proved there are no other such
  $n \leq 2^{44}$.
* Vaughan [Va73] has proved that the number of $n \leq N$ such that $n - 2^k$
  is prime for all $1 < 2^k < n$ is
  $< \exp\left(-c \frac{\log\log\log N}{\log\log N} \log N\right) N$ for some
  constant $c > 0$. (Not formalized here: expressing this counting bound needs
  `Finset` cardinalities, real exponentials and logarithms — constructs not
  present in this file — deferred enrichment.)
* This is discussed in problem A19 of Guy's collection [Gu04].
* Erdős made the stronger conjecture (see problem #236) that the number of
  $1 < 2^k < n$ for which $n - 2^k$ is prime is $o(\log n)$. Since there are
  $\sim \log_2 n$ admissible $k$, that conjecture would force a negative
  answer to the infinitude question here for all sufficiently large $n$.

See also: problem #236 (and the neighboring #1141).
Tags: number theory, primes
Related OEIS sequences: A039669.
Formalised statement (per the page, as of access): No. (An upstream
formalization at FormalConjectures/ErdosProblems/1142.lean in
google-deepmind/formal-conjectures postdating the page snapshot is captured in
this repo's session logs.)

Reference: [Va99, 1.7]
https://www.erdosproblems.com/1142

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §1.7. (Honest stub matching the upstream formal-conjectures 1142.lean entry
  for this key, recovered from the session logs, and consistent with sibling
  files 1068, 1131, 1137–1141. Note: the gloss of `[Va99]` as "Vaughan, R.C.,
  Some problems of Erdős in combinatorial number theory" found in early styled
  drafts of this problem in the logs is a hallucination for this key.)
[MiWe69] Mientka, W. E. and Weitzenkamp, R. C., _On f-plentiful numbers_,
  Journal of Combinatorial Theory 7 (1969), no. 4, 374–377. (Title, journal,
  year, and pages per the recovered `/latex/1142` extraction; the volume/issue
  numbers appear only in the upstream formal-conjectures 1142.lean capture and
  are not `/latex`-verified.)
[Va73] Vaughan, R. C., _Some applications of Montgomery's sieve_, Journal of
  Number Theory 5 (1973), 64–79. (Same provenance split: volume number from
  the upstream capture only.)
[Gu04] Guy, R. K., _Unsolved Problems in Number Theory_, 3rd ed., Springer,
  2004, xviii+437 pp.; Problem A19. (Year and page extent per the `/latex/1142`
  extraction; edition/publisher per the upstream capture; "Problem A19" per
  the source page itself.)
-/

open Nat

/--
A natural number n has the property that n - 2^k is prime
for every k ≥ 1 with 2^k < n.

Note (encoding): for n ≤ 2 no k satisfies 1 ≤ k ∧ 2^k < n, so 0, 1, 2 satisfy
this predicate vacuously. These three junk values are immaterial to the
infinitude statement below, but any finite-enumeration variant must guard them
away (see `erdos_problem_1142.variants.mientka_weitzenkamp`, and the OEIS
A039669 convention "Numbers n > 2 such that ...").
-/
def AllPowerOfTwoComplementsPrime (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → 2 ^ k < n → (n - 2 ^ k).Prime

/--
Erdős Problem #1142 [Va99, 1.7] (Open):

Are there infinitely many n (or any n > 105) such that n - 2^k is prime for
all 1 < 2^k < n?

The only known such n are 4, 7, 15, 21, 45, 75, 105 (OEIS A039669).
Mientka and Weitzenkamp [MiWe69] proved there are no other such n ≤ 2^44.
Vaughan [Va73] proved the count of such n ≤ N is at most
exp(-c · (log log log N / log log N) · log N) · N for some c > 0.

Encoding notes:
* The ℕ subtraction `n - 2 ^ k` never truncates, being guarded by `2 ^ k < n`.
* The source condition $1 < 2^k$ is exactly `1 ≤ k` (both say $k \geq 1$).
* `∀ N, ∃ n > N` is the standard encoding of "infinitely many" over ℕ; the
  vacuous members n ∈ {0, 1, 2} of the predicate cannot witness it beyond
  N = 2 and are immaterial.
* Membership under this encoding was verified computationally during review:
  the members in [0, 2·10⁶] are exactly {0, 1, 2} ∪ {4, 7, 15, 21, 45, 75,
  105} — consistent with the page's known list and [MiWe69]'s exhaustive
  search to 2^44.

The problem is an open yes/no question; per this corpus's convention the
asked ("yes") direction is stated as a direct assertion. In styled question
form it would be `answer(sorry) ↔ Set.Infinite {n : ℕ | …}`. (Vaughan's
sparsity bound and Erdős's stronger conjecture in problem #236 suggest the
true answer may be "no".)

Tags: number theory, primes
-/
theorem erdos_problem_1142 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ AllPowerOfTwoComplementsPrime n :=
  sorry

/--
Variant (page sub-question, open): the source question's parenthetical asks
for less — is there *any* n > 105 with the property? (105 is the largest
known such n.) The asked ("yes") direction is stated per the corpus
convention; the main theorem trivially implies this one (take N = 105).
-/
theorem erdos_problem_1142.variants.any_gt_105 :
    ∃ n : ℕ, 105 < n ∧ AllPowerOfTwoComplementsPrime n :=
  sorry

/--
Variant (page-confirmed, [MiWe69]): Mientka and Weitzenkamp proved that the
only n ≤ 2^44 with the property are 4, 7, 15, 21, 45, 75, 105 — stated here
as the completeness direction of their exhaustive search. The hypothesis
`2 < n` is required: 0, 1, 2 satisfy the predicate vacuously (no admissible
k exists), and without the guard the statement would be false at n = 0.
-/
theorem erdos_problem_1142.variants.mientka_weitzenkamp :
    ∀ n : ℕ, 2 < n → n ≤ 2 ^ 44 → AllPowerOfTwoComplementsPrime n →
      n = 4 ∨ n = 7 ∨ n = 15 ∨ n = 21 ∨ n = 45 ∨ n = 75 ∨ n = 105 :=
  sorry

/--
Variant (page-confirmed): each of the seven known values has the property.
(A finite decidable check, verified numerically during review — e.g. for 105:
103, 101, 97, 89, 73, 41 are all prime; for 4: 4 - 2 = 2 is prime.)
-/
theorem erdos_problem_1142.variants.known_values :
    AllPowerOfTwoComplementsPrime 4 ∧ AllPowerOfTwoComplementsPrime 7 ∧
      AllPowerOfTwoComplementsPrime 15 ∧ AllPowerOfTwoComplementsPrime 21 ∧
      AllPowerOfTwoComplementsPrime 45 ∧ AllPowerOfTwoComplementsPrime 75 ∧
      AllPowerOfTwoComplementsPrime 105 :=
  sorry
