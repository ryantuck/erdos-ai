import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

/-!
# Erdős Problem #1097

Let $A$ be a set of $n$ integers. How many distinct $d$ can occur as the common
difference of a three-term arithmetic progression in $A$? Are there always
$O(n^{3/2})$ many such $d$?

A problem Erdős posed in the 1989 problem session of Great Western Number
Theory [GWNT89]. Status on erdosproblems.com/1097: OPEN (page edition
03 December 2025, accessed 2026-03-09).

Erdős states that Erdős and Ruzsa gave an explicit construction which achieved
$n^{1+c}$ for some $c > 0$, and Erdős and Spencer gave a probabilistic proof
which achieved $n^{3/2}$, and speculated this may be the best possible.

However, the page's remarks record that (as noticed by Chan in the comment
section) this problem is *exactly equivalent* to a sums-differences question of
Bourgain [Bo99], introduced as an arithmetic path towards the Kakeya
conjecture: find the smallest $c \in [1,2]$ such that, for any finite sets of
integers $A$ and $B$ and $G \subseteq A \times B$,
$$\lvert A \overset{G}{-} B\rvert \ll
  \max(\lvert A\rvert, \lvert B\rvert, \lvert A \overset{G}{+} B\rvert)^c$$
(where $A \overset{G}{+} B$ denotes the set of $a+b$ with $(a,b) \in G$). The
equivalence is that the greatest exponent $c$ achievable for the main problem
is equal to the smallest constant achievable for the sums-differences question,
and the current best bounds are
$$1.77898\cdots \leq c \leq 11/6 \approx 1.833.$$
The upper bound is due to Katz and Tao [KaTa99]; the lower bound is due to
Lemm [Le15] (with a very small improvement found by AlphaEvolve [GGTW25]).

Since $1.77898 > 3/2$, the answer to the question "are there always
$O(n^{3/2})$ many such $d$?" is **NO**: there are sets of $n$ integers with at
least $n^{1.77898-o(1)}$ distinct common differences of three-term arithmetic
progressions, refuting Erdős's speculation. (Transfer of the sums-differences
lower bound: given $G \subseteq A \times B$, the set
$S = 2\cdot A \cup (A \overset{G}{+} B) \cup 2\cdot B$ has
$\lvert S\rvert \leq 3\max(\lvert A\rvert,\lvert B\rvert,
\lvert A \overset{G}{+} B\rvert)$, and for each $(a,b) \in G$ the triple
$2b, a+b, 2a \in S$ is a three-term progression with common difference $a-b$,
so $S$ has at least $\lvert A \overset{G}{-} B\rvert$ distinct common
differences.) The remaining OPEN content of the problem — the site's headline
question "how many distinct $d$ can occur?" — is to determine the exact
exponent $c \in [1.77898\cdots, 11/6]$, which this file does not formalize as
a single statement (it is a value request with unknown answer).

The main theorem below is therefore stated in the true (negated) direction;
the affirmative $O(n^{3/2})$ bound it denies is preserved verbatim as the
body of the negation. NOTE: the restated theorem and the added variants are
not compile-verified (the review container cannot run `lake build`); the
original affirmative statement did compile in the formalization session.

Tags: number theory, additive combinatorics.

References (honest stubs; the site loads full bibliographic data via
separate `/bibs/` requests that were not captured in the session logs —
do not trust beyond what is stated):
- [GWNT89] Problems of the 1989 problem session of the Great Western Number
  Theory conference (problem list hosted at westcoastnumbertheory.org,
  wcnt-problems-1989.pdf).
- [Bo99] Bourgain, J. (1999). Sums-differences question introduced as an
  arithmetic approach to the Kakeya conjecture.
- [KaTa99] Katz, N. and Tao, T. (1999). Upper bound $c \leq 11/6$ for the
  sums-differences problem.
- [Le15] Lemm, M. (2015). Lower bound $c \geq 1.77898\cdots$ for the
  sums-differences problem.
- [GGTW25] (2025). Small improvement to the lower bound, found by AlphaEvolve.

Additional thanks to (per the problem page): Koishi Chan and Terence Tao.

Note: the authoritative upstream formalization of this problem lives in
google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/1097.lean`,
linked from the problem page as "Formalised statement? Yes") and is not
present in this repository; this file is the local raw first-pass. The
upstream file states the question noncommittally as
`erdos_1097 : answer(sorry) ↔ ∃ C > (0 : ℝ), ∀ (A : Finset ℤ),
(CommonDifferencesThreeTermAP A).ncard ≤ C * (A.card : ℝ) ^ (3 / 2 : ℝ)`.
-/

namespace Erdos1097

/--
The set of common differences of three-term arithmetic progressions in `A`.
That is, `d` is in this set if there exists `a ∈ A` with `a + d ∈ A` and `a + 2 * d ∈ A`.

Note on degenerate cases: `0 ∈ apDiffs A` whenever `A` is nonempty (the
constant progression `a, a, a`), and `d ∈ apDiffs A ↔ -d ∈ apDiffs A`
(reverse the progression). So this count exceeds the count of common
differences of nondegenerate ascending progressions by at most a factor of
`2` plus `1`, which is harmless for every power-type bound stated below.
The `image` step over `A ×ˢ A` is only there to realize the set as a
`Finset`: any `d` with `a ∈ A` and `a + d ∈ A` is the difference
`(a + d) - a` of two elements of `A`, so the subsequent `filter` carves out
exactly `{d | ∃ a ∈ A, a + d ∈ A ∧ a + 2 * d ∈ A}`.
-/
noncomputable def apDiffs (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.2 - p.1) |>.filter (fun d =>
    ∃ a ∈ A, a + d ∈ A ∧ a + 2 * d ∈ A)

/-- Erdős Problem #1097 [GWNT89]:

Let A be a set of n integers. How many distinct d can occur as the common
difference of a three-term arithmetic progression in A? Are there always
O(n^{3/2}) many such d?

The answer to the second (yes/no) question is NO — stated here in the true,
negated direction. Erdős and Spencer gave a probabilistic proof that there
exist sets achieving n^{3/2} such differences and Erdős speculated this may
be best possible, but by the exact equivalence (observed by Chan, recorded on
the problem page) with Bourgain's sums-differences question [Bo99], Lemm's
lower bound [Le15] produces sets of n integers with at least n^{1.77898-o(1)}
distinct common differences, and 1.77898 > 3/2. See the module docstring for
the transfer argument. The problem page nevertheless retains OPEN status,
which refers to determining the exact optimal exponent
(currently known to lie in [1.77898..., 11/6]).

NOTE: this negated restatement is not compile-verified.
-/
theorem erdos_problem_1097 :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
      ((apDiffs A).card : ℝ) ≤ C * (A.card : ℝ) ^ ((3 : ℝ) / 2) :=
  sorry

/--
Erdős Problem #1097, Erdős–Spencer lower bound [GWNT89]:

Erdős and Spencer gave a probabilistic proof that there exist arbitrarily
large sets A of n integers with at least a constant times n^{3/2} distinct
common differences of three-term arithmetic progressions. (Solved.)

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1097.variants.erdos_spencer :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ A : Finset ℤ,
      N ≤ A.card ∧ c * (A.card : ℝ) ^ ((3 : ℝ) / 2) ≤ ((apDiffs A).card : ℝ) :=
  sorry

/--
Erdős Problem #1097, Erdős–Ruzsa explicit construction [GWNT89]:

Erdős and Ruzsa gave an explicit construction of arbitrarily large sets of n
integers achieving n^{1+c} distinct common differences, for some c > 0.
(Solved; any multiplicative constant in the construction is absorbed by
slightly decreasing the exponent c, which is quantified existentially.)

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1097.variants.erdos_ruzsa :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ A : Finset ℤ,
      N ≤ A.card ∧ (A.card : ℝ) ^ ((1 : ℝ) + c) ≤ ((apDiffs A).card : ℝ) :=
  sorry

/--
Erdős Problem #1097, Lemm lower bound via the Bourgain sums-differences
equivalence [Le15][Bo99]:

For every exponent e < 1.77898 there are arbitrarily large sets A of n
integers with at least n^e distinct common differences of three-term
arithmetic progressions. This follows from Lemm's lower bound
1.77898... for the smallest sums-differences constant together with the
exact equivalence recorded on the problem page (the truncation 1.77898 of
the constant 1.77898... is used, which only weakens the statement; the
AlphaEvolve improvement [GGTW25] is likewise subsumed). (Solved.)

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1097.variants.lower_bound_lemm :
    ∀ e : ℝ, e < 1.77898 → ∀ N : ℕ, ∃ A : Finset ℤ,
      N ≤ A.card ∧ (A.card : ℝ) ^ e ≤ ((apDiffs A).card : ℝ) :=
  sorry

/--
Erdős Problem #1097, Katz–Tao upper bound via the Bourgain sums-differences
equivalence [KaTa99][Bo99]:

For every exponent e > 11/6 there is a constant C > 0 such that every finite
set A of integers has at most C |A|^e distinct common differences of
three-term arithmetic progressions. This follows from the Katz–Tao upper
bound c ≤ 11/6 for the sums-differences problem together with the exact
equivalence recorded on the problem page ("greatest achievable exponent
≤ 11/6" unwinds to exactly this eventual-bound form, and small sets are
absorbed into C via the trivial n² bound). (Solved.)

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1097.variants.upper_bound_katz_tao :
    ∀ e : ℝ, (11 : ℝ) / 6 < e → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
      ((apDiffs A).card : ℝ) ≤ C * (A.card : ℝ) ^ e :=
  sorry

/--
Erdős Problem #1097, trivial upper bound (upstream-confirmed variant):

There are always at most n² such values of d: every common difference is a
difference of two elements of A, and A has at most |A|² ordered pairs. The
authoritative upstream formalization carries this as
`erdos_1097.variants.weaker`. (Elementary.)

NOTE: added per the recovered upstream skeleton; not compile-verified.
-/
theorem erdos_problem_1097.variants.weaker :
    ∀ A : Finset ℤ, (apDiffs A).card ≤ A.card ^ 2 :=
  sorry

end Erdos1097
