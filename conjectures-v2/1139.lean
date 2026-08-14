import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat

noncomputable section

/-!
# Erdős Problem #1139

Let $1 \leq u_1 < u_2 < \cdots$ be the sequence of integers with at most $2$
prime factors (counted with multiplicity). Is it true that
$$\limsup \frac{u_{k+1} - u_k}{\log k} = \infty?$$

Verbatim source statement (erdosproblems.com/1139): "Let $1\leq u_1<u_2<\cdots$
be the sequence of integers with at most $2$ prime factors. Is it true
that\[\limsup \frac{u_{k+1}-u_k}{\log k}=\infty?\]"

Status: OPEN per erdosproblems.com/1139 (page last edited 23 January 2026,
accessed 2026-03-09) — "This is open, and cannot be resolved with a finite
computation."

Interpretation note: the page does not say whether prime factors are counted
with multiplicity. This file reads "at most 2 prime factors" as $\Omega(n) \le 2$
(with multiplicity, i.e. $n = 1$, $n = p$, or $n = pq$ with $p, q$ prime, not
necessarily distinct) — the standard almost-prime reading, and the same reading
as the upstream formal-conjectures formalization linked from the page
(`Nat.nth (fun n ↦ 0 < n ∧ Ω n ≤ 2)`), which divides by $\log(k+1)$ exactly as
the theorem below does.

The problem is a yes/no question; following this corpus's convention for open
questions, the theorem below states the conjectured ("yes") direction as a
direct assertion. In styled question form it would be
`answer(sorry) ↔ ∀ M : ℝ, M > 0 → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ …`
with the quantifiers inside the iff (this is how the upstream
formal-conjectures file states it, via `atTop.limsup … = (⊤ : EReal)`).

Tags: number theory, primes
Related OEIS sequences: none listed (the database marks them "Possible").
Formalised statement per the page: "Yes" —
google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/1139.lean.

Reference: [Va99, 1.4]
https://www.erdosproblems.com/1139

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §1.4. (Honest stub from the upstream contributing guide's canonical entry;
  the site's /latex/1139 and /bibs/Va99 content was never captured in the
  session logs, so fuller bibliographic detail is DEFERRED. Note: the
  "Vardi, I." attribution for this key carried by some sibling artifacts is a
  hallucination and is deliberately not reproduced here.)
-/

/-- A positive integer has at most 2 prime factors (counted with multiplicity):
    $1 \le n$ and $\Omega(n) \le 2$, since `Nat.primeFactorsList` lists prime
    factors with multiplicity (e.g. `primeFactorsList 12 = [2, 2, 3]`, so 12 is
    excluded while 9 = 3² is included). The predicate holds for n = 1
    ($\Omega(1) = 0$) and for every prime, so the set it carves out is
    infinite. -/
def hasAtMostTwoPrimeFactors (n : ℕ) : Prop :=
  1 ≤ n ∧ n.primeFactorsList.length ≤ 2

/-- The k-th element (0-indexed) of the increasing sequence of positive integers
    with at most 2 prime factors: 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, ….
    Since the underlying set is infinite (it contains all primes), `Nat.nth`
    enumerates it in strictly increasing order, and the source's 1-indexed
    $u_j$ is `almostPrime2 (j - 1)`; in particular `almostPrime2 0 = 1 = u₁`. -/
noncomputable def almostPrime2 (k : ℕ) : ℕ :=
  nth hasAtMostTwoPrimeFactors k

/-- Gap between consecutive elements of the sequence: in the source's 1-indexed
    terms this is $u_{k+2} - u_{k+1}$. The ℕ subtraction never truncates,
    because `Nat.nth` of an infinite predicate is strictly monotone. -/
noncomputable def almostPrime2Gap (k : ℕ) : ℕ :=
  almostPrime2 (k + 1) - almostPrime2 k

/--
Erdős Problem #1139 [Va99, 1.4] (OPEN):

Let 1 ≤ u₁ < u₂ < ⋯ be the sequence of positive integers with at most 2 prime
factors (counted with multiplicity). Is it true that
  limsup (u_{k+1} - u_k) / log k = ∞?

Stated here in the conjectured ("yes") direction, unfolded: for every M > 0
there exist arbitrarily large k with u_{k+1} - u_k > M · log k.

Encoding notes:
* Indexing: the source's ratio at 1-indexed k is (u_{k+1} - u_k)/log k; with
  the 0-indexed `almostPrime2` this is `almostPrime2Gap (k - 1) / log k`, i.e.
  `almostPrime2Gap k / log (k + 1)` — hence the `log ((k : ℝ) + 1)` below,
  making the translation term-by-term exact (and matching the upstream
  formal-conjectures encoding).
* The inequality is stated multiplied through by the (eventually positive)
  log (k + 1), avoiding division; at k = 0 it reads M · log 1 = 0 < gap,
  which is true but harmless: the leading ∀ N still forces arbitrarily
  large witnesses.
* `M > 0` suffices for limsup = ∞ since the bound for large M implies the
  bound for all smaller M.
-/
theorem erdos_problem_1139 :
    ∀ M : ℝ, M > 0 → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧
      M * Real.log ((k : ℝ) + 1) < (almostPrime2Gap k : ℝ) :=
  sorry

end
