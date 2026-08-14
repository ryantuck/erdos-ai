import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #1143

Let $p_1 < \cdots < p_u$ be primes and let $k \geq 1$. Let $F_k(p_1,\ldots,p_u)$
be such that every interval of $k$ positive integers contains at least
$F_k(p_1,\ldots,p_u)$ multiples of at least one of the $p_i$. Estimate
$F_k(p_1,\ldots,p_u)$, particularly in the range $k = \alpha p_u$ for constant
$\alpha > 2$.

Verbatim source statement (erdosproblems.com/1143): "Let $p_1<\cdots<p_u$ be
primes and let $k\geq 1$. Let $F_k(p_1,\ldots,p_u)$ be such that every interval
of $k$ positive integers contains at least $F_k(p_1,\ldots,p_u)$ multiples of
at least one of the $p_i$. / Estimate $F_k(p_1,\ldots,p_u)$, particularly in
the range $k=\alpha p_u$ for constant $\alpha>2$."

Status: OPEN per erdosproblems.com/1143 (page last edited 23 January 2026,
accessed 2026-02-23) — "This is open, and cannot be resolved with a finite
computation."

Remarks from the source page:
* "In [Va99] it is reported that Erdős and Selfridge found 'the exact bound'
  when $2<\alpha<3$, and that 'if $\alpha>3$ then very little is known'. No
  reference is given, and I cannot find a relevant paper of Erdős and
  Selfridge." (Page owner's wording. Since the exact bound itself is nowhere
  stated, no Erdős–Selfridge variant can be formalized honestly.)
* See also problem #970 (Jacobsthal's function).

Formalization scope: "Estimate $F_k$" is an open-ended estimation request with
no single formalizable statement. This file records the central object $F_k$
(as `F_k` below) and a concrete elementary sieve lower bound: every interval
of $k$ consecutive positive integers contains at least
$k(1 - \prod_{p\in S}(1 - 1/p)) - 2^{|S|}$ multiples of some element of $S$.
This proxy is *true and provable* by truncated inclusion–exclusion (each of
the $2^{|S|}-1$ nonempty subsets $T \subseteq S$ contributes a difference of
floors within $1$ of $k/\prod_{p\in T}p$; distinctness of the primes gives
$\mathrm{lcm} = \prod$); it is a known consequence of sieve theory, not the
open problem itself. The open problem — sharper estimates, in particular the
exact value of $F_k$ for $\alpha > 3$ — is recorded here in prose only.

Tags: number theory, primes
Formalised statement (per the page, as of access): No. (An upstream
formalization at FormalConjectures/ErdosProblems/1143.lean in
google-deepmind/formal-conjectures postdating the page snapshot is captured in
this repo's session logs.)

Reference: [Va99, 1.8]
https://www.erdosproblems.com/1143

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §1.8. (Honest stub per the `/latex/1143` extraction recovered from the
  session logs, matching the upstream formal-conjectures 1143.lean entry and
  sibling files 1068, 1137–1142. Note: the gloss of `[Va99]` as "Vaughan,
  R.C., _On a problem of Erdős, Straus, and Schinzel_, Combinatorica 19
  (1999), 111–115" — found in an early styled draft of this problem in the
  logs and endorsed by the prior ai-review — is a hallucination for this key;
  Vaughan's genuine paper of that title concerns unit fractions and is
  unrelated to this problem.)
-/

open Finset BigOperators

namespace Erdos1143

/-- Count of integers in {n+1, ..., n+k} divisible by at least one element of
`S`. (For k = 0 the interval is empty and the count is 0.) -/
def countDivisible (S : Finset ℕ) (k n : ℕ) : ℕ :=
  ((Icc (n + 1) (n + k)).filter (fun m => ∃ p ∈ S, p ∣ m)).card

/-- `F_k S k` is the minimum, over all starting points `n`, of the count of
integers in {n+1, …, n+k} divisible by at least one element of `S` — the
central object $F_k(p_1,\ldots,p_u)$ of Erdős Problem #1143, i.e. the largest
value such that *every* interval of `k` positive integers contains at least
that many multiples of some element of `S`. The infimum is attained: the range
of `countDivisible S k` is a nonempty set of naturals (indeed `countDivisible`
is periodic in `n` with period `∏ p ∈ S, p`). -/
noncomputable def F_k (S : Finset ℕ) (k : ℕ) : ℕ :=
  iInf (countDivisible S k)

/--
Erdős Problem #1143 [Va99, 1.8] (Open):

Let p₁ < ⋯ < p_u be primes and k ≥ 1. Define F_k(p₁,…,p_u) to be the
minimum, over all starting points n ≥ 0, of the count of integers in
{n+1, …, n+k} that are divisible by at least one pᵢ — equivalently, the
largest value such that every interval of k positive integers contains at
least F_k(p₁,…,p_u) such multiples.

Estimate F_k(p₁,…,p_u), particularly in the range k = α·p_u for constant α > 2.

In [Va99] it is reported that Erdős and Selfridge found 'the exact bound'
when 2 < α < 3, and that 'if α > 3 then very little is known'. No reference
is given there, and the source page's owner could not locate a relevant paper
of Erdős and Selfridge.

We formalize a sieve lower bound (a true, provable proxy — see the module
docstring): for any finite nonempty set of primes S, every interval of k
consecutive positive integers contains at least
k·(1 - ∏_{p∈S}(1 - 1/p)) - 2^|S| multiples of some element of S.

Encoding notes:
* The error term 2^|S| dominates the truncated inclusion–exclusion error:
  over the 2^|S| - 1 nonempty subsets T ⊆ S, the count of multiples of
  ∏_{p∈T} p in the interval is a difference of floors within 1 of
  k/∏_{p∈T} p, so the total error is < 2^|S| - 1 (even 2^|S| - 1 would be a
  valid, slightly sharper constant).
* Primality (or at least pairwise coprimality) of S is essential, since
  inclusion–exclusion needs lcm(T) = ∏ T: for S = {2, 4}, k = 40, n = 0 the
  interval [1, 40] contains 20 multiples of 2 or 4 while the formula demands
  40·(1 - (1/2)(3/4)) - 4 = 21. So `hS` cannot be weakened to positivity.
* `hne` and `hk` are convenience hypotheses matching the source's setup
  (u ≥ 1, k ≥ 1); for S = ∅ or k = 0 the right-hand side is negative and the
  inequality holds trivially.
* All arithmetic on the right-hand side is in ℝ (the bound can be negative),
  with 1/p a real division by p ≥ 2 — no ℕ truncation traps arise.
* The bound was corroborated by brute force during review for
  S ∈ {{2},{3},{2,3},{2,3,5},{3,5,7},{2,3,5,7},{5,7,11}}, all k ≤ 60 (k ≤ 40
  for the larger sets), over a full period of n in each case.

The open problem is to determine sharper estimates, particularly the exact
value of F_k for α > 3.

Tags: number theory, primes
-/
theorem erdos_problem_1143 (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (hne : S.Nonempty) (k : ℕ) (hk : 0 < k) :
    ∀ n : ℕ,
      (countDivisible S k n : ℝ) ≥
        (k : ℝ) * (1 - S.prod (fun p => (1 - 1 / (p : ℝ)))) - (2 : ℝ) ^ S.card :=
  sorry

/--
Variant: the sieve lower bound restated for the problem's central object
F_k(p₁,…,p_u) itself — F_k(S) ≥ k·(1 - ∏_{p∈S}(1 - 1/p)) - 2^|S|. This
follows from `erdos_problem_1143` because the ℕ-valued infimum defining `F_k`
is attained at some starting point n₀.
-/
theorem erdos_problem_1143.variants.F_k_lower (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hne : S.Nonempty) (k : ℕ) (hk : 0 < k) :
    (F_k S k : ℝ) ≥
      (k : ℝ) * (1 - S.prod (fun p => (1 - 1 / (p : ℝ)))) - (2 : ℝ) ^ S.card :=
  sorry

end Erdos1143
