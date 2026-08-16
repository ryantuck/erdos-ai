import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/--
A natural number `n` is the sum of a prime and at most `k` powers of 2
(with distinct exponents) if there exist a prime `p` and a finite set of
exponents `S` with `|S| ≤ k` such that `n = p + ∑_{e ∈ S} 2^e`.

Encoding notes:

- **Distinct exponents are without loss of generality.** If
  `n = p + 2^{e_1} + ⋯ + 2^{e_m}` with `m ≤ k` and repetitions allowed,
  then since the binary digit sum satisfies `s₂(a + b) ≤ s₂(a) + s₂(b)`
  (carries only merge digits), the total `t = 2^{e_1} + ⋯ + 2^{e_m}` has
  `s₂(t) ≤ m`, so `t` is a sum of `s₂(t) ≤ k` *distinct* powers of 2.
  Conversely a `Finset` sum is a special multiset sum. Hence this predicate
  defines the same set of `n` as the repetition-allowed reading (the upstream
  formal-conjectures encoding uses a `Multiset` of cardinality `≤ k`; the two
  are extensionally equal).
- **`S = ∅` is allowed**: a prime `p` itself counts as "a sum of a prime and
  at most `k` powers of 2" (zero powers used), for every `k`. In particular
  `IsSumPrimeAndPowersOf2 n 0 ↔ n.Prime`. This matches the source's
  "at most" and the upstream encoding (`Multiset` of cardinality `≤ k`,
  including `0`).
- `2^0 = 1` is a permitted power of 2, as in the source (cf. Erdős
  Problem #9, which uses `p + 2^k + 2^l` with `k, l ≥ 0`).
-/
def IsSumPrimeAndPowersOf2 (n k : ℕ) : Prop :=
  ∃ (p : ℕ) (S : Finset ℕ), Nat.Prime p ∧ S.card ≤ k ∧
    n = p + S.sum (2 ^ ·)

/--
Erdős Problem #10 [Er77c, ErGr80 p.28, Er85c, Er92c, Er95, Er97, Er97c, Er97e]:

> Is there some $k$ such that every large integer is the sum of a prime and
> at most $k$ powers of 2?

**Status: OPEN** ("This is open, and cannot be resolved with a finite
computation." — erdosproblems.com/10, page edition 24 January 2026, accessed
2026-03-05; status re-confirmed open against the teorth/erdosproblems metadata
mirror, `data/problems.yaml` entry 10, last update 2025-08-31).

Erdős described this as 'probably unattackable'. In [ErGr80] Erdős and Graham
suggest that **no such $k$ exists**. Following this corpus's convention for
open yes/no questions (direct assertion of the believed/conjectured direction,
with the belief documented), this theorem asserts the Erdős–Graham direction:
for every $k$ there are arbitrarily large integers that are *not* the sum of a
prime and at most $k$ powers of 2. This is the exact logical negation of the
question's "yes" side
`∃ k N, ∀ n ≥ N, IsSumPrimeAndPowersOf2 n k`.

Note the literature is not unanimous: Granville and Soundararajan [GrSo98]
conjecture the opposite — that $3$ powers of 2 suffice for all odd integers
$> 1$, and hence $4$ powers suffice for all even integers (see
`erdos_problem_10.variants.granville_soundararajan`), which would answer the
question "yes" with $k = 4$. Erdős's and Graham's suggestion is the problem
owners' recorded guess and is the direction asserted here; a proof of either
this statement or its negation would resolve the problem.

Known partial results and remarks from the problem page:

- Gallagher [Ga75] proved: for any $\epsilon > 0$ there exists $k(\epsilon)$
  such that the set of integers which are the sum of a prime and at most
  $k(\epsilon)$ powers of 2 has lower density at least $1 - \epsilon$.
  (Not formalized here: it needs a lower-density definition on sets of
  naturals, machinery not present in this file.)
- Granville and Soundararajan [GrSo98] conjectured that at most $3$ powers of
  2 suffice for all odd integers, and hence at most $4$ powers of 2 suffice
  for all even integers.
- Bogdan Grechuk observed that $1117175146$ is not the sum of a prime and at
  most $3$ powers of 2 (see `erdos_problem_10.variants.grechuk_example`;
  independently re-verified by direct computation during this review), and
  pointed out that parity considerations, coupled with the fact that there are
  many integers not the sum of a prime and $2$ powers of 2 (see Erdős
  Problem #9), suggest that there exist infinitely many even integers which
  are not the sum of a prime and at most $3$ powers of 2 (see
  `erdos_problem_10.variants.grechuk_even`).

See also Erdős Problems #9, #11, and #16. Tags: number theory, additive
basis, primes. Related OEIS sequence: A387053. Additional thanks (page):
Bogdan Grechuk and Desmond Weisenberg.

References (bibliographic data recovered from sibling files in this corpus
and from the upstream formal-conjectures `ErdosProblems/10.lean` capture in
the session logs; the `erdosproblems.com/latex/10` bibliography was not
recoverable offline, so entries are honest stubs where noted and volume/issue
data is deliberately omitted rather than guessed):

- [Er77c] Erdős, P., Problems and results on combinatorial number theory.
  III. Number Theory Day (Proc. Conf., Rockefeller Univ., New York, 1976)
  (1977), 43-72.
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in
  combinatorial number theory. Monographies de L'Enseignement Mathématique
  (1980). Cited by the page at p.28.
- [Er85c] Erdős, P., On some of my problems in number theory I would most
  like to see solved. Number theory (Ootacamund, 1984) (1985), 74-84.
- [Er92c] Erdős, P. (1992). (Stub: sibling files disagree on this key's
  title — "Some of my favourite problems in various branches of
  combinatorics", Matematiche (Catania) (1992), vs "Some of my forgotten
  problems in number theory", Hardy-Ramanujan J. (1992).)
- [Er95] Erdős, P., Some of my favourite problems in various branches of
  combinatorics (1995). (Corpus-majority title; a minority of sibling files
  carry "Some of my favourite problems in number theory, combinatorics, and
  geometry", Resenhas 1 (1995), 165-186, under this key.)
- [Er97] Erdős, P., Some of my new and almost new problems and results in
  combinatorial number theory (1997).
- [Er97c] Erdős, P., Some of my favorite problems and results. The
  mathematics of Paul Erdős, I (1997). (Sibling files split on this key's
  title; this is the reading confirmed by the `/latex/5` recovery in
  `fable-review/5.md`.)
- [Er97e] Erdős, P. (1997). (Stub: sibling files disagree on this key's
  title.)
- [Ga75] Gallagher, P. X., Primes and powers of 2 (1975). (Title from the
  upstream formal-conjectures capture; year per key convention.)
- [GrSo98] Granville, A. and Soundararajan, K., A binary additive problem of
  Erdős and the order of 2 mod p² (1998). (Title from the upstream
  formal-conjectures capture; year per key convention.)
-/
theorem erdos_problem_10 :
    ∀ k : ℕ, ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ ¬IsSumPrimeAndPowersOf2 n k :=
  sorry

/--
Erdős Problem #10, Grechuk's example (SOLVED — a finite computation):

Bogdan Grechuk observed that $1117175146$ is not the sum of a prime and at
most $3$ powers of 2. Re-verified by direct computation during this review:
no representation `1117175146 = p + Σ_{e ∈ S} 2^e` with `p` prime and
`|S| ≤ 3` exists (checked over all `≤ 3`-element sets of exponents below 31,
in both the distinct-exponent and repetition-allowed readings).
-/
theorem erdos_problem_10.variants.grechuk_example :
    ¬IsSumPrimeAndPowersOf2 1117175146 3 :=
  sorry

/--
Erdős Problem #10, Granville–Soundararajan conjecture (OPEN) [GrSo98]:

at most $3$ powers of 2 suffice for all odd integers $> 1$, and hence at most
$4$ powers of 2 suffice for all even integers $\ne 0$. (The "hence": for even
$n \ge 4$, $n - 1$ is odd and $> 1$, so $n = p + (\text{≤ 3 powers}) + 2^0$,
a sum of at most 4 powers after binary carrying; $n = 2$ is itself prime.
A "yes" here answers the main question affirmatively with $k = 4$ — the
direction opposite to the Erdős–Graham suggestion asserted in
`erdos_problem_10`. The restriction to odd integers in the 3-power clause is
important: see `erdos_problem_10.variants.grechuk_example` and
`erdos_problem_10.variants.grechuk_even`.)
-/
theorem erdos_problem_10.variants.granville_soundararajan :
    (∀ n : ℕ, Odd n → 1 < n → IsSumPrimeAndPowersOf2 n 3) ∧
      (∀ n : ℕ, Even n → n ≠ 0 → IsSumPrimeAndPowersOf2 n 4) :=
  sorry

/--
Erdős Problem #10, Grechuk's suggestion (OPEN):

there exist infinitely many even integers which are not the sum of a prime
and at most $3$ powers of 2 — suggested by Bogdan Grechuk on the problem
page, based on parity considerations coupled with the fact that there are
many integers not the sum of a prime and $2$ powers of 2 (see Erdős
Problem #9). "Infinitely many" is encoded as "arbitrarily large", matching
the main theorem's form.
-/
theorem erdos_problem_10.variants.grechuk_even :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ Even n ∧ ¬IsSumPrimeAndPowersOf2 n 3 :=
  sorry
