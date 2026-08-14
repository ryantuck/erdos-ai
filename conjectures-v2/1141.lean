import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős Problem #1141

Are there infinitely many $n$ such that $n - k^2$ is prime for all $k$ with
$(n,k) = 1$ and $k^2 < n$?

Verbatim source statement (erdosproblems.com/1141): "Are there infinitely many
$n$ such that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2<n$?"

Status: OPEN per erdosproblems.com/1141 (page last edited 26 January 2026,
accessed 2026-03-09) — "This is open, and cannot be resolved with a finite
computation."

Remarks from the source page:
* In [Va99] it is asked whether $968$ is the largest integer with this
  property, but this is an error, since for example $968 - 9 = 959 = 7 \cdot
  137$ (and $\gcd(968, 3) = 1$, $9 < 968$).
* The list of $n$ satisfying the given property is A214583 in the OEIS. The
  largest known such $n$ is $1722$.
* ChatGPT and Tang have shown that the number of such $n$ in $[1, N]$ is at
  most $N^{1/2+o(1)}$. (Not formalized here: expressing this counting bound
  needs `Finset` cardinalities and real exponents, constructs not present in
  this file — deferred enrichment.)

See also: problems #1140 and #1142.
Tags: number theory, primes
Related OEIS sequences: A214583.
Formalised statement (per the page): yes, upstream at
FormalConjectures/ErdosProblems/1141.lean in google-deepmind/formal-conjectures.

Reference: [Va99, 1.6]
https://www.erdosproblems.com/1141

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §1.6. (Honest stub matching the upstream formal-conjectures 1141.lean entry
  for this key, recovered from the session logs, and consistent with sibling
  files 1068, 1131, 1132, 1137, 1138, 1139, 1140; fuller bibliographic detail
  is DEFERRED. Note: unrelated glosses of `[Va99]` as Vaughan/Vardi/etc. found
  in some styled sibling artifacts are hallucinations for this key.)
-/

/--
Erdős Problem #1141 [Va99, 1.6] (Open):

Are there infinitely many n such that n - k² is prime for all k with
gcd(n, k) = 1 and k² < n?

The list of n satisfying this property is A214583 in the OEIS. The largest
known such n is 1722. In [Va99] it is asked whether 968 is the largest integer
with this property, but this is an error, since 968 - 9 = 959 = 7 · 137.
ChatGPT and Tang have shown that the number of such n in [1, N] is at most
N^{1/2+o(1)}.

Encoding notes:
* The ℕ subtraction `n - k ^ 2` never truncates, being guarded by `k ^ 2 < n`.
* `k = 0`: `Nat.Coprime n 0 ↔ n = 1`, so the `k = 0` instance only bites at
  `n = 1`, where it demands `Nat.Prime 1` (false) — hence `1` is excluded from
  the set, and for every `n ≥ 2` the quantifier effectively ranges over
  `k ≥ 1`, matching the source. (Under the alternative `k ≥ 1` reading, `1`
  would be a vacuous member; the two readings differ only at `n = 1`, which is
  immaterial to infinitude.)
* `n = 0` is a vacuous member of the set (no `k` satisfies `k ^ 2 < 0`), a
  single junk element likewise immaterial to `Set.Infinite`.
* Membership under this encoding was verified computationally during review:
  the members in `[1, 5000]` are 3, 4, 6, 8, 12, 14, 18, 20, 24, 30, 32, 38,
  42, 48, 54, 60, 62, 68, 72, 80, 84, 90, 98, 108, 110, 132, 138, 140, 150,
  180, 182, 198, 252, 318, 360, 398, 468, 570, 572, 930, 1722 — consistent
  with the page's "largest known such n is 1722".

The problem is an open yes/no question; per this corpus's convention the
asked ("yes") direction is stated as a direct assertion. In styled question
form it would be `answer(sorry) ↔ Set.Infinite {n : ℕ | …}`.

Tags: number theory, primes
-/
theorem erdos_problem_1141 :
    Set.Infinite {n : ℕ | ∀ k : ℕ, k ^ 2 < n → Nat.Coprime n k → Nat.Prime (n - k ^ 2)} :=
  sorry

/--
Variant (page-confirmed, [Va99] erratum): in [Va99] it is asked whether 968 is
the largest integer with this property, "but this is an error, since for
example 968 - 9 = 7 · 137" — that is, 968 does not have the property at all:
k = 3 satisfies k² = 9 < 968 and gcd(968, 3) = 1, yet 968 - 9 = 959 = 7 · 137
is not prime. (A finite decidable check; verified numerically during review.)
-/
theorem erdos_problem_1141.variants.va99_968_error :
    968 ∉ {n : ℕ | ∀ k : ℕ, k ^ 2 < n → Nat.Coprime n k → Nat.Prime (n - k ^ 2)} :=
  sorry

/--
Variant (page-confirmed): "The largest known such n is 1722" — in particular
1722 has the property: for every k with k² < 1722 and gcd(1722, k) = 1, the
number 1722 - k² is prime. (A finite decidable check; verified numerically
during review: the coprime k < 42 are 1, 5, 11, 13, 17, 19, 23, 25, 29, 31,
37, and each 1722 - k² is prime.)
-/
theorem erdos_problem_1141.variants.largest_known :
    1722 ∈ {n : ℕ | ∀ k : ℕ, k ^ 2 < n → Nat.Coprime n k → Nat.Prime (n - k ^ 2)} :=
  sorry
