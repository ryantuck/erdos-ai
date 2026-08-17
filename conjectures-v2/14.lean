import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat

open scoped Classical
open Finset

noncomputable section

/-- The number of representations of `n` as `a + b` with `a, b ∈ A` and `a ≤ b`.

Encoding notes:

- `a` ranges over `Finset.range (n + 1) = {0, …, n}`, so `a ≤ n` and the
  ℕ-subtraction `n - a` is exact (never truncated). Under `a ≤ n` the filter
  condition `a ≤ n - a` is exactly `2 * a ≤ n`, and `a ↦ (a, n - a)` is a
  bijection between the filtered set and the representations `n = a + b` with
  `a ≤ b` and `a, b ∈ A`, so the card is exactly the number of unordered
  representations.
- "Sum of two elements from `A`" allows `a = b` (i.e. `n = a + a` counts),
  matching the upstream formal-conjectures encoding (ordered pairs with
  `a.1 ≤ a.2`).
- `A : Set ℕ` may contain `0` (Lean's ℕ includes `0`); the upstream
  formal-conjectures file `ErdosProblems/14.lean` makes the same choice. -/
def reprCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A ∧ a ≤ n - a)).card

/-- The set of integers representable in exactly one way as the sum of two
    elements from `A` (with `a ≤ b`). This is the set called $B$ on the
    problem page. -/
def UniqueRepSum (A : Set ℕ) : Set ℕ :=
  {n : ℕ | reprCount A n = 1}

/-- Count of integers in `{1, …, N}` that are NOT in the unique-representation
    sumset `B`, i.e. $\lvert \{1,\ldots,N\}\setminus B\rvert$. (Despite the
    name, this counts both integers with *no* representation and integers with
    *more than one* representation — exactly the complement of $B$, as in the
    problem statement.) -/
def nonUniqueRepCount (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => n ∉ UniqueRepSum A)).card

/--
Erdős Problem #14, Part 1 [Er92c, Er97, Er97e]:

> Let $A\subseteq \mathbb{N}$. Let $B\subseteq \mathbb{N}$ be the set of
> integers which are representable in exactly one way as the sum of two
> elements from $A$. Is it true that for all $\epsilon>0$ and large $N$
> $\lvert \{1,\ldots,N\}\backslash B\rvert \gg_\epsilon N^{1/2-\epsilon}$?

**Status: OPEN** ("This is open, and cannot be resolved with a finite
computation." — erdosproblems.com/14, page edition 14 September 2025,
accessed 2026-03-05; status re-confirmed open against the
teorth/erdosproblems metadata mirror, `data/problems.yaml` entry 14, last
update 2025-08-31). This is a yes/no question; following this corpus's
convention for open yes/no questions (direct assertion of the affirmative,
unrefuted direction — the page records no belief either way), the theorem
asserts the lower bound. The implied constant in $\gg_\epsilon$ is
existentially quantified after `A` and `ε` (so it may depend on both), and
"large $N$" is `∃ N₀, ∀ N ≥ N₀`; this matches the upstream
formal-conjectures encoding (`answer(sorry) ↔ ∀ A, ∀ ε > 0,
nonUniqueSumCount A ≫ almostSquareRoot ε`). Note that under the leading
`∀ ε > 0` the per-`A` and `A`-uniform constant readings are equivalent:
a per-`A` constant for exponent `1/2 - ε` gives the constant `1` for any
exponent `1/2 - ε'` with `ε' > ε` once `N` is large.

Remarks from the problem page:

- Apparently originally considered by Erdős and Nathanson, although later
  Erdős attributes this to Erdős, Sárközy, and Szemerédi (but gives no
  reference), and claims a construction of an $A$ such that for all
  $\epsilon>0$ and all large $N$,
  $\lvert \{1,\ldots,N\}\backslash B\rvert \ll_\epsilon N^{1/2+\epsilon}$,
  and yet for all $\epsilon>0$ there exist infinitely many $N$ where
  $\lvert \{1,\ldots,N\}\backslash B\rvert \gg_\epsilon N^{1/3-\epsilon}$
  (see `erdos_problem_14.variants.erdos_construction`).
- Erdős and Freud investigated the finite analogue in [ErFr91], proving
  that there exists $A\subseteq \{1,\ldots,N\}$ such that the number of
  integers not representable in exactly one way as the sum of two elements
  from $A$ is $< 2^{3/2}N^{1/2}$, and suggest the constant $2^{3/2}$ is
  perhaps best possible (see
  `erdos_problem_14.variants.erdos_freud_finite`).

Tags: number theory, sidon sets, additive combinatorics. Related OEIS
sequence: A143824. The page links an upstream formalization
(google-deepmind/formal-conjectures, `ErdosProblems/14.lean`). Additional
thanks (page): Boris Alexeev and Zach Hunter.

References (the `erdosproblems.com/latex/14` bibliography was not
recoverable offline; entries below are assembled from sibling files in this
corpus, are honest stubs where noted, and omit journal/volume/page data
rather than guess it):

- [Er92c] Erdős, P. (1992). (Stub: sibling files disagree on this key's
  title — "Some of my favourite problems in various branches of
  combinatorics", Matematiche (Catania) (1992), vs "Some of my forgotten
  problems in number theory", Hardy-Ramanujan J. (1992).)
- [Er97] Erdős, P., Some of my new and almost new problems and results in
  combinatorial number theory (1997). (Corpus-unanimous title for this key,
  but sibling reviews note it coincides with the corpus title of [Er98] —
  a possible corpus-level conflation, unresolved offline.)
- [Er97e] Erdős, P. (1997). (Stub: sibling files disagree on this key's
  title.)
- [ErFr91] Erdős, P. and Freud, R., On sums of a Sidon-sequence.
  J. Number Theory (1991), 196-205. (Corpus-majority entry — so in
  `deepmind/deepmind/819.lean` and `840.lean`; one sibling
  (`deepmind/deepmind/864.lean`) instead titles this key "On
  Sidon-sequences and related problems" — disagreement unresolved offline;
  volume number absent, not fabricated.)
-/
theorem erdos_problem_14a :
    ∀ A : Set ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        C * (N : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (nonUniqueRepCount A N : ℝ) :=
  sorry

/--
Erdős Problem #14, Part 2 [Er92c, Er97, Er97e]:

> Is it possible that
> $\lvert \{1,\ldots,N\}\backslash B\rvert =o(N^{1/2})?$

That is, does there exist $A$ such that the integers in $\{1,\ldots,N\}$ not
representable in exactly one way number $o(N^{1/2})$? **Status: OPEN**; a
yes/no question, asserted here in the affirmative direction per the corpus
convention (see `erdos_problem_14a`'s docstring for status and convention
provenance). Little-$o$ is encoded by its standard ε-definition (the counts
are non-negative, so no absolute values are needed); $N^{1/2}$ is
`Real.rpow`, and `(0 : ℝ) ^ (1/2 : ℝ) = 0` affects nothing since the bound
is only asserted eventually. This matches the upstream formal-conjectures
encoding (`answer(sorry) ↔ ∃ A, IsLittleO atTop (nonUniqueSumCount A)
squareRoot`).

Note the two affirmative assertions `erdos_problem_14a` and
`erdos_problem_14b` are mutually consistent: a set with
$\lvert \{1,\ldots,N\}\backslash B\rvert \asymp N^{1/2}/\log N$ would
satisfy both, so asserting both directions is not self-contradictory.
-/
theorem erdos_problem_14b :
    ∃ A : Set ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (nonUniqueRepCount A N : ℝ) ≤ ε * (N : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

/--
Erdős Problem #14, Erdős's claimed construction (CLAIMED — Erdős attributes
it to Erdős, Sárközy, and Szemerédi but gives no reference; treated as a
claimed result, not a page-verified theorem) [Er92c, Er97, Er97e]:

there is an $A$ such that for all $\epsilon>0$ and all large $N$,
$\lvert \{1,\ldots,N\}\backslash B\rvert \ll_\epsilon N^{1/2+\epsilon}$,
and yet for all $\epsilon>0$ there exist infinitely many $N$ where
$\lvert \{1,\ldots,N\}\backslash B\rvert \gg_\epsilon N^{1/3-\epsilon}$.

(Both bounds are read, per the page's "a construction of an $A$ such
that … and yet …", as properties of the same set $A$. "Infinitely many $N$"
is encoded as "arbitrarily large $N$" — `∀ M, ∃ N ≥ M` — which is exact for
a predicate on ℕ.)
-/
theorem erdos_problem_14.variants.erdos_construction :
    ∃ A : Set ℕ,
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (nonUniqueRepCount A N : ℝ) ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + ε)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
        c * (N : ℝ) ^ ((1 : ℝ) / 3 - ε) ≤ (nonUniqueRepCount A N : ℝ)) :=
  sorry

/--
Erdős Problem #14, the Erdős–Freud finite analogue (SOLVED) [ErFr91]:

there exists $A\subseteq \{1,\ldots,N\}$ such that the number of integers
not representable in exactly one way as the sum of two elements from $A$ is
$< 2^{3/2}N^{1/2}$. (They suggest the constant $2^{3/2}$ is perhaps best
possible — an open sharpening, recorded here in prose only.)

Encoding notes:

- The page does not specify the range of "integers" counted; this encoding
  counts integers in $\{1,\ldots,N\}$ (via `nonUniqueRepCount A N`),
  paralleling the problem's central quantity
  $\lvert \{1,\ldots,N\}\backslash B\rvert$ and the companion Erdős–Freud
  problems on $(A+A)\cap\{1,\ldots,N\}$ for $A\subseteq\{1,\ldots,N\}$
  (Erdős Problems #819, #840, which cite the same paper). The alternative
  reading (integers up to $2N$) is noted in the review but not encoded.
- The hypothesis `1 ≤ N` excludes the degenerate `N = 0`, where the
  right-hand side is `2^{3/2} * 0 ^ (1/2) = 0` (Lean's `rpow` convention)
  and the strict inequality `0 < 0` is false — the page's statement is
  implicitly about genuine intervals. For `1 ≤ N ≤ 18` the strict bound was
  verified by exhaustive computation over all `A ⊆ {1, …, N}` during
  review (the count is at most `N`, and `N < 2^{3/2}√N` already for
  `N < 8`).
-/
theorem erdos_problem_14.variants.erdos_freud_finite :
    ∀ N : ℕ, 1 ≤ N →
      ∃ A : Set ℕ, (∀ a ∈ A, a ∈ Finset.Icc 1 N) ∧
        (nonUniqueRepCount A N : ℝ) <
          (2 : ℝ) ^ ((3 : ℝ) / 2) * (N : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

end
