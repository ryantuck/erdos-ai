import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Interval

/-!
# Erdős Problem 36

*Reference:* [erdosproblems.com/36](https://www.erdosproblems.com/36)
(accessed 2026-03-05, page edition 23 January 2026; page content recovered from
two agreeing archived session-log captures — the live site is unreachable from
the review container).

Statement (verbatim from the site): "Find the optimal constant $c>0$ such that
the following holds. For all sufficiently large $N$, if $A\sqcup B=\{1,\ldots,2N\}$
is a partition into two equal parts, so that $\lvert A\rvert=\lvert B\rvert=N$,
then there is some $x$ such that the number of solutions to $a-b=x$ with
$a\in A$ and $b\in B$ is at least $cN$." [Er55][Er56][Er61][Er92c]

Status: **OPEN** ("This is open, and cannot be resolved with a finite
computation"). The teorth/erdosproblems metadata mirror (`data/problems.yaml`,
checked at commit a09c7a21, 2026-08-14) agrees: status "open" (last update
2025-08-31); comment "minimum overlap problem"; tags: number theory, additive
combinatorics; OEIS A393584 (marked "possible"); no prize.

Remarks from the page: this is the *minimum overlap problem*. The example
(with $N$ even) $A=\{N/2+1,\ldots,3N/2\}$ shows that $c\leq 1/2$ (indeed,
Erdős initially conjectured that $c=1/2$). The lower bound $c\geq 1/4$ is
trivial, and Scherk improved this to $1-1/\sqrt{2}=0.29\cdots$. The current
records are $0.379005 < c < 0.380876$, the lower bound due to White [Wh22] and
the upper bound due to the TTT-Discover LLM [YKLBMWKCZGS26], improving slightly
on earlier bounds due to AlphaEvolve [GGTW25] and Haugland [Ha16]. The problem
is discussed as problem C17 of Guy's collection [Gu04]. Additional thanks to:
Terence Tao.

"Find the optimal constant" is a value request about an open quantity; without
the styled `answer()` machinery (not part of this raw pipeline) it is
represented below by a statement that pins the constant $c$ *uniquely* as the
threshold (supremum) of the constants for which the eventual lower bound
holds: every smaller constant works for all sufficiently large $N$, and every
larger constant fails for infinitely many $N$. The value of $c$ (known to lie
in $(0.379005, 0.380876)$) is the open content and is recorded here. Scherk's
$1-1/\sqrt{2}$ bound is not formalized ( `Real.sqrt` is not imported); the
trivial $1/4$ bound and both current record bounds are, as variants.

References (recovered from the archived page, the upstream formal-conjectures
file for this problem — commit dd1c2beb — and canonical sibling entries in
this repo; entries marked "stub" lack full bibliographic data, which is not
fabricated here; no `/latex/36` fetch exists in the session logs):

- [Er55] Erdős, P., _Some remarks on number theory_ (in Hebrew). Riveon
  Lematematika 9 (1955), 45-48. (Volume number from the upstream
  formal-conjectures docstring.)
- [Er56] Erdős, P., _Problems and results in additive number theory_.
  Colloque sur la Théorie des Nombres, Bruxelles, 1955 (1956), 127-137.
- [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató
  Int. Közl. 6 (1961), 221-254.
- [Er92c] Erdős, P. (1992). (Stub: sibling files disagree on this key's
  title — "Some of my favourite problems in various branches of
  combinatorics", Matematiche (Catania) (1992), vs "Some of my forgotten
  problems in number theory", Hardy-Ramanujan J. (1992).)
- [Wh22] White, E. P., _Erdős' minimum overlap problem_. arXiv:2201.05704
  (2022). (From the upstream formal-conjectures docstring.)
- [YKLBMWKCZGS26] (2026). Upper-bound record 0.380876, found by the
  TTT-Discover LLM. (Stub; only the key and attribution appear on the page.)
- [GGTW25] (2025). Earlier upper-bound improvement, found by AlphaEvolve.
  (Stub; key also appears in sibling file `conjectures/1097.lean`.)
- [Ha16] Haugland, J. K. (2016). Earlier upper-bound record. (Stub; likely
  the computation reported at neutreeko.net/mop — upper bound
  0.3809268534330870 per the upstream formal-conjectures docstring — but the
  page shows only the key and surname.)
- [Gu04] Guy, R. K., _Unsolved problems in number theory_ (2004), xviii+437.
  Problem C17.
-/

open Finset

/--
Given sets A and B of integers and an integer x, the number of
pairs (a, b) with a ∈ A, b ∈ B, and a - b = x.
-/
noncomputable def repCount (A B : Finset ℤ) (x : ℤ) : ℕ :=
  (A.filter fun a => (a - x) ∈ B).card

/--
Erdős Problem #36 [Er55, Er56, Er61, Er92c] — The Minimum Overlap Problem
(OPEN):

Find the optimal constant c > 0 such that for all sufficiently large N, if
A ⊔ B = {1,…,2N} is a partition into two equal parts (|A| = |B| = N), then
there exists some x such that the number of solutions to a - b = x with
a ∈ A and b ∈ B is at least cN.

The example (with N even) A = {N/2+1,…,3N/2} shows c ≤ 1/2 (Erdős initially
conjectured c = 1/2); the lower bound c ≥ 1/4 is trivial, improved by Scherk
to 1 - 1/√2. The current record bounds are 0.379005 < c < 0.380876 (lower:
White [Wh22]; upper: TTT-Discover [YKLBMWKCZGS26], after AlphaEvolve [GGTW25]
and Haugland [Ha16]). Finding the value of c is the open problem.

Encoding note ([defect] fix, not compile-verified): the input file asserted
only `∃ c > 0` such that the eventual lower bound holds — a statement provable
by pigeonhole with c = 1/4 (each equal partition of {1,…,2N} yields N² pairs
(a, b) spread over at most 4N - 1 differences, so some difference occurs
≥ N²/(4N-1) > N/4 times), so it captured none of the problem's content, which
lies entirely in the word "optimal". The statement below pins c uniquely as
the threshold constant: (i) every c' < c admits the eventual lower bound
c'·N over all equal partitions, and (ii) every c' > c fails it at infinitely
many N (some equal partition has all difference-counts < c'·N). These two
clauses determine at most one real c (any two candidates would contradict
each other at a constant strictly between them), and such a c exists —
it is liminf over N of (min over equal partitions of the max difference-count)
divided by N, which conjuncts (i)/(ii) characterize exactly, and it is
positive by the pigeonhole bound. The open question is its value.
-/
theorem erdos_problem_36 :
    ∃ c : ℝ, 0 < c ∧
      (∀ c' : ℝ, c' < c →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ (A B : Finset ℤ),
            A ∪ B = Finset.Icc (1 : ℤ) (2 * ↑N) →
            Disjoint A B →
            A.card = N →
            B.card = N →
            ∃ x : ℤ, (repCount A B x : ℝ) ≥ c' * (N : ℝ)) ∧
      (∀ c' : ℝ, c < c' →
        ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
          ∃ (A B : Finset ℤ),
            A ∪ B = Finset.Icc (1 : ℤ) (2 * ↑N) ∧
            Disjoint A B ∧
            A.card = N ∧
            B.card = N ∧
            ∀ x : ℤ, (repCount A B x : ℝ) < c' * (N : ℝ)) :=
  sorry

/--
The trivial lower bound (page-confirmed variant, not compile-verified): for
every N ≥ 1 and every equal partition A ⊔ B = {1,…,2N}, some difference x has
at least N/4 representations a - b = x. (Pigeonhole: N² pairs spread over at
most 4N - 1 possible differences give a difference with ≥ N²/(4N-1) > N/4
representations.) On the page: "The lower bound of c ≥ 1/4 is trivial."
-/
theorem erdos_problem_36.variants.lower_trivial :
    ∀ N : ℕ, 1 ≤ N →
      ∀ (A B : Finset ℤ),
        A ∪ B = Finset.Icc (1 : ℤ) (2 * ↑N) →
        Disjoint A B →
        A.card = N →
        B.card = N →
        ∃ x : ℤ, (repCount A B x : ℝ) ≥ (1 / 4 : ℝ) * (N : ℝ) :=
  sorry

/--
Erdős's upper-bound example (page-confirmed variant, not compile-verified):
for infinitely many N — every even N works, via A = {N/2+1,…,3N/2} and
B = {1,…,N/2} ∪ {3N/2+1,…,2N} — there is an equal partition of {1,…,2N} in
which every difference x has at most N/2 representations. (A window of N
consecutive integers cannot meet both halves of B, which sit N + 1 apart, so
each shifted copy of A meets B in at most N/2 elements; the shift x = N/2
attains N/2.) This shows the optimal constant satisfies c ≤ 1/2. Erdős
initially conjectured that c = 1/2; the record upper bounds (c < 0.380876)
have since refuted that. [Er55]
-/
theorem erdos_problem_36.variants.upper_half :
    ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ∃ (A B : Finset ℤ),
        A ∪ B = Finset.Icc (1 : ℤ) (2 * ↑N) ∧
        Disjoint A B ∧
        A.card = N ∧
        B.card = N ∧
        ∀ x : ℤ, (repCount A B x : ℝ) ≤ (N : ℝ) / 2 :=
  sorry

/--
White's record lower bound [Wh22] (page-confirmed variant, not
compile-verified): for all sufficiently large N, every equal partition
A ⊔ B = {1,…,2N} has some difference x with at least 0.379005·N
representations. (The page states 0.379005 < c; since c exceeds this value,
the eventual uniform lower bound at 0.379005 itself holds.)
-/
theorem erdos_problem_36.variants.lower_white :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (A B : Finset ℤ),
        A ∪ B = Finset.Icc (1 : ℤ) (2 * ↑N) →
        Disjoint A B →
        A.card = N →
        B.card = N →
        ∃ x : ℤ, (repCount A B x : ℝ) ≥ (0.379005 : ℝ) * (N : ℝ) :=
  sorry

/--
The record upper bound [YKLBMWKCZGS26] (page-confirmed variant, not
compile-verified): for infinitely many N there is an equal partition of
{1,…,2N} in which every difference x has fewer than 0.380876·N
representations. (The page states c < 0.380876; since c is the threshold
constant, the bound must fail at 0.380876 for infinitely many N. The
"infinitely many" form is the safe consequence of c < 0.380876 alone,
without invoking existence of the limit.)
-/
theorem erdos_problem_36.variants.upper_record :
    ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ∃ (A B : Finset ℤ),
        A ∪ B = Finset.Icc (1 : ℤ) (2 * ↑N) ∧
        Disjoint A B ∧
        A.card = N ∧
        B.card = N ∧
        ∀ x : ℤ, (repCount A B x : ℝ) < (0.380876 : ℝ) * (N : ℝ) :=
  sorry
