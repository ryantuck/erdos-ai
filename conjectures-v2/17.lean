import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Cofinite

open Filter

/--
A prime `p` is a **cluster prime** if every even number `n` with `2 ≤ n` and
`n ≤ p - 3` can be written as a difference `q₁ - q₂` of two primes `q₁, q₂ ≤ p`.

Encoding notes (ℕ semantics, analyzed in `fable-review/17.md`):

- `p - 3` is ℕ-truncated subtraction. For every prime `p ≥ 3` it equals the
  integer value of `p - 3`; for `p = 2` it truncates to `0`, so the inner
  condition is vacuous and `2` (like `3` and `5`, whose ranges of relevant
  `n` are empty or trivial) is a cluster prime by vacuity. The literature
  (Blecksmith-Erdős-Selfridge [BES99]; OEIS A038133, which lists the odd
  primes `3, 5, 7, 11, …, 89, 101, …`) defines cluster primes among odd
  primes only; the vacuous membership of `2` is harmless for the infinitude
  statement below, since one extra element never changes `Set.Infinite`.
- `n = q₁ - q₂` is also ℕ-truncated, but under the hypothesis `2 ≤ n` it is
  exactly equivalent to the intended integer equation `(n : ℤ) = q₁ - q₂`:
  if `q₂ > q₁` the truncated difference is `0 ≠ n`, and otherwise ℕ- and
  ℤ-subtraction agree. (The upstream google-deepmind/formal-conjectures
  file states both comparisons in ℤ instead; the two definitions agree on
  all primes.)
-/
def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧
    ∀ n : ℕ, 2 ≤ n → n ≤ p - 3 → Even n →
      ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧ q₁ ≤ p ∧ q₂ ≤ p ∧ n = q₁ - q₂

/--
Erdős Problem #17 [Er95, p.172]:

> Are there infinitely many primes $p$ such that every even number
> $n \leq p - 3$ can be written as a difference of primes $n = q_1 - q_2$
> where $q_1, q_2 \leq p$?

**Status: OPEN** ("This is open, and cannot be resolved with a finite
computation." — erdosproblems.com/17, page edition 28 December 2025,
recovered from the original pipeline's session logs; status re-confirmed
open against the teorth/erdosproblems metadata mirror, `data/problems.yaml`
entry 17, last update 2025-08-31). This is a yes/no question; following
this corpus's convention for open yes/no questions (direct assertion of the
conjectured direction), the theorem asserts that the set of cluster primes
is infinite. The upstream google-deepmind/formal-conjectures file
(`ErdosProblems/17.lean`) encodes the same content in question form:
`erdos_17 : answer(sorry) ↔ {p : ℕ | IsClusterPrime p}.Infinite`.

Remarks from the problem page:

- The first prime without this property is $97$. The sequence of such
  primes is A038133 in the OEIS. These are called cluster primes. (See
  `erdos_problem_17.variants.*` below.)
- Blecksmith, Erdős, and Selfridge [BES99] proved that the number of such
  primes up to $x$ is $\ll_A x/(\log x)^A$ for every $A > 0$, and Elsholtz
  [El03] improved this to $\ll x\exp(-c(\log\log x)^2)$ for every
  $c < 1/8$. (Not formalized in this file: encoding these counting bounds
  requires `Real.log`/`Real.exp`, asymptotic notation, and a counting
  function, none of which are among this file's constructs; upstream
  formalizes them as `erdos_17.variants.upper_BES` and
  `erdos_17.variants.upper_Elsholtz`.)
- This is discussed in problem C1 of Guy's collection [Gu04].

Tags: number theory, primes. Related OEIS sequence: A038133. No prize.
Additional thanks (page): Ralf Stephan and Terence Tao.

References (assembled from the provenance noted per entry; the
`erdosproblems.com/latex/17` bibliography was not recoverable offline, so
entries are honest stubs with missing data omitted rather than guessed):

- [Er95] Erdős, P., Some of my favourite problems in number theory,
  combinatorics, and geometry. Resenhas 1 (1995), 165-186. (Title, journal,
  pages from sibling corpus files, e.g. `deepmind/deepmind/46.lean`; the
  volume number is the corpus reading, unverified offline. A corpus
  minority carries "Some of my favourite problems in various branches of
  combinatorics", Congressus Numerantium 107 (1995), 167-189, under this
  key — that reading is incompatible with the page citations
  `[Er95, p.165]` and `[Er95, p.166]` recorded for problems 1, 2 and 7,
  which fall below its first page 167, so the Resenhas reading is
  preferred.)
- [BES99] Blecksmith, R., Erdős, P., and Selfridge, J. L., Cluster primes.
  Amer. Math. Monthly (1999), 43-48. (From the upstream formal-conjectures
  `ErdosProblems/17.lean` docstrings — session-log capture and fresh clone
  agree; the volume number is absent there and is omitted here rather than
  guessed.)
- [El03] Elsholtz, C., On cluster primes. Acta Arith. (2003), 281-284.
  (Same provenance as [BES99]; volume number likewise absent.)
- [Gu04] Guy, R. K., Unsolved problems in number theory. 3rd ed., Springer
  (2004), xviii+437. Problem C1. (Bibliographic data from sibling files in
  this corpus carrying the same key, e.g. `conjectures-v2/1052.lean`; the
  problem-C1 pointer is from the recovered page.)
-/
theorem erdos_problem_17 : {p : ℕ | IsClusterPrime p}.Infinite :=
  sorry

/--
Erdős Problem #17, page-confirmed remark — **97 is not a cluster prime**
("The first prime without this property is $97$.").

Concrete witness (documented, not compile-verified): `n = 88` is even with
`2 ≤ 88 ≤ 94 = 97 - 3`, and `88 = q₁ - q₂` with primes `q₁, q₂ ≤ 97` would
force `q₂ ≤ 9`, i.e. `q₂ ∈ {2, 3, 5, 7}`, giving `q₁ ∈ {90, 91, 93, 95}`,
none of which is prime. (The upstream formal-conjectures test theorem for
this problem uses the same witness.)
-/
theorem erdos_problem_17.variants.not_clusterPrime_97 :
    Nat.Prime 97 ∧ ¬ IsClusterPrime 97 :=
  sorry

/--
Erdős Problem #17, page-confirmed remark — 97 is the **first** prime
without the cluster property: every prime `p < 97` is a cluster prime.
(Under the vacuous-`p = 2` convention documented on `IsClusterPrime`
above; the odd primes `3, 5, 7, …, 89` are the initial terms of OEIS
A038133.) Together with `erdos_problem_17.variants.not_clusterPrime_97`
this renders the page's "the first prime without this property is $97$"
exactly.
-/
theorem erdos_problem_17.variants.clusterPrime_below_97 :
    ∀ p : ℕ, p.Prime → p < 97 → IsClusterPrime p :=
  sorry
