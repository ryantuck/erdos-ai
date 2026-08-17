import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Classical
open Finset

/-!
# Erdős Problem #39

Is there an infinite Sidon set $A\subset \mathbb{N}$ such that
$$\lvert A\cap \{1\ldots,N\}\rvert \gg_\epsilon N^{1/2-\epsilon}$$
for all $\epsilon>0$?

**Status: OPEN** — banner tooltip: "This is open, and cannot be resolved
with a finite computation." **$500** prize. (erdosproblems.com/39, page
last edited 23 January 2026, accessed 2026-03-05; the teorth/erdosproblems
metadata mirror agrees: state "open", last update 2025-08-31, prize $500,
no OEIS refs, tags "number theory", "sidon sets", "additive
combinatorics".)

Remarks from the source page:

- The trivial greedy construction achieves $\gg N^{1/3}$. The first
  improvement on this was achieved by Ajtai, Komlós, and Szemerédi
  [AKS81b], who found an infinite Sidon set with growth rate
  $\gg (N\log N)^{1/3}$. The current best bound of $\gg N^{\sqrt 2-1+o(1)}$
  is due to Ruzsa [Ru98]. (The Ruzsa bound is formalized below as
  `erdos_problem_39.variants.ruzsa_lower`.)
- Erdős [Er73] had offered \$25 for any construction which achieves $N^c$
  for some $c>1/3$. Later he [Er77c] offered \$100 for a construction
  which achieves $\omega(N)N^{1/3}$ for some $\omega(N)\to\infty$.
- Erdős proved that for every infinite Sidon set $A$ we have
  $\liminf \lvert A\cap\{1,\ldots,N\}\rvert/N^{1/2}=0$. (Formalized below
  as `erdos_problem_39.variants.liminf_zero`.)
- Erdős and Rényi have constructed, for any $\epsilon>0$, a set $A$ such
  that $\lvert A\cap\{1\ldots,N\}\rvert\gg_\epsilon N^{1/2-\epsilon}$ for
  all large $N$ and $1_A\ast 1_A(n)\ll_\epsilon 1$ for all $n$ — near-Sidon
  growth, but with merely bounded (not distinct) representations.
  (Formalized below as `erdos_problem_39.variants.erdos_renyi`.)
- This is discussed in problem C9 of Guy's collection [Gu04].

Formalised statement? **Yes** — upstream google-deepmind/formal-conjectures
`FormalConjectures/ErdosProblems/39.lean` (present at HEAD dd1c2beb) states
`answer(sorry) ↔ ∃ A, A.Infinite ∧ IsSidon A ∧ ∀ᵉ (ε > (0:ℝ)),
(· ^ (1/2 - ε) : ℕ → ℝ) =O[atTop] fun N => ((Set.Icc 1 N ∩ A).ncard : ℝ)`
— the same question in `answer()`-iff form with an `IsBigO`/`atTop`
(eventual) encoding of $\gg_\epsilon$; see the docstring of
`erdos_problem_39` below for why the present all-$N$ encoding is
equivalent as an existence statement.

## References

Problem sources on the page: [Er56] [Er61] [Er73] [Er77c] [ErGr80, p.48]
[Er81] [Er82e] [Er85c] [Er91] [Er95] [Er97c] [Va99, 1.18]; remarks cite
[AKS81b] [Ru98] [Gu04] (and [Er73], [Er77c] again for the prizes). No
`/latex/39` fetch exists in the session logs, so no bibliography could be
recovered from the site itself; the entries below are honest stubs with
their provenance flagged, and the rest are keys only: DEFERRED.

- [Er56] Erdős, P., _Problems and results in additive number theory_.
  Colloque sur la Théorie des Nombres, Bruxelles, 1955 (1956), 127-137.
  (Stub: sibling-corpus and upstream consensus entry; unverified offline.)
- [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat.
  Kutató Int. Közl. 6 (1961), 221-254. (Stub: sibling-corpus consensus;
  unverified offline.)
- [Er73] Erdős, P., _Problems and results on combinatorial number
  theory_. A survey of combinatorial theory (Proc. Internat. Sympos.,
  Colorado State Univ., Fort Collins, Colo., 1971) (1973), 117-138.
  (Stub: sibling-corpus and upstream consensus; unverified offline.)
- [Er77c] Erdős, P., _Problems and results on combinatorial number
  theory. III_. Number Theory Day (Proc. Conf., Rockefeller Univ., New
  York, 1976) (1977), 43-72. (Stub: sibling-corpus consensus; unverified
  offline.)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement
  Mathématique 28 (1980). This problem: p. 48. (Stub: sibling-corpus and
  upstream consensus; unverified offline.)
- [Er81] Erdős, P., _On the combinatorial problems which I would most
  like to see solved_. Combinatorica 1 (1981), 25-42. (Stub:
  sibling-corpus consensus; unverified offline.)
- [Er85c] Erdős, P., _On some of my problems in number theory I would
  most like to see solved_. Number theory (Ootacamund, 1984) (1985),
  74-84. (Stub: from sibling corpus files, which are split on this key's
  title; unverified offline.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas 1 (1995), 165-186. (Stub:
  corpus-majority entry; unverified offline.)
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced
  for the conference "Paul Erdős and his Mathematics" (Budapest, 1999).
  This problem: §1.18. (Stub: from sibling corpus files; unverified
  offline.)
- [Gu04] Guy, R. K., _Unsolved problems in number theory_. 3rd ed.,
  Springer (2004), xviii+437. Problem C9. (Stub: from sibling corpus
  files; unverified offline.)
- [AKS81b] Ajtai, M., Komlós, J., and Szemerédi, E. (1981). Author names
  and year from the page prose/key; the standard citation _A dense
  infinite Sidon sequence_, European J. Combin. 2 (1981), 1-11, is
  reviewer-supplied and unverified offline.
- [Ru98] Ruzsa, I. Z. (1998). Author name and year from the page
  prose/key; the standard citation _An infinite Sidon sequence_,
  J. Number Theory 68 (1998), 63-71, is reviewer-supplied and unverified
  offline. (Distinct from the site key [Ru98b], _A small maximal Sidon
  set_, cited by sibling file `conjectures/156.lean`.)
- [Er82e] [Er91] [Er97c] — keys only; no reliable corpus expansion (the
  corpus's entries for these keys conflict): DEFERRED.

Tags: number theory, sidon sets, additive combinatorics
https://www.erdosproblems.com/39
-/

/--
A set of natural numbers is a **Sidon set** (or B₂ set) if all pairwise sums
are distinct: for a, b, c, d ∈ A with a ≤ b and c ≤ d,
a + b = c + d implies a = c and b = d.

(Equivalent to the unordered formulation — `a + b = c + d → {a,b} = {c,d}`
as multisets — by ordering each pair; the upstream formal-conjectures
shared library states it unordered as `IsSidon`. Mathlib itself has no
Sidon-set definition to reuse.)
-/
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → a ≤ b → c ≤ d → a = c ∧ b = d

/--
The counting function for A up to N: |A ∩ {1, …, N}|.

(`Finset.Icc 1 N` is exactly {1, …, N}; membership in `A : Set ℕ` is
decided classically via `open scoped Classical`, which is why downstream
uses are `noncomputable`-safe.)
-/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/--
Erdős Problem #39 [Er56, Er61, Er73, Er77c, ErGr80, Er81, Er82e, Er85c, Er91,
Er95, Er97c, Va99] — OPEN, $500 prize (erdosproblems.com/39, page last
edited 23 January 2026, accessed 2026-03-05; status cross-checked open
against the teorth/erdosproblems metadata mirror):

Is there an infinite Sidon set A ⊂ ℕ such that
  |A ∩ {1, …, N}| ≫_ε N^{1/2 - ε}
for all ε > 0?

The theorem below asserts the affirmative (conjectured) direction of this
open yes/no question, matching the upstream formal-conjectures encoding
`answer(sorry) ↔ ∃ A, …`.

A Sidon set has all pairwise sums distinct. The trivial greedy construction
gives |A ∩ {1,…,N}| ≫ N^{1/3}; the first improvement, by Ajtai, Komlós, and
Szemerédi [AKS81b], achieves ≫ (N log N)^{1/3}. The best known bound, due to
Ruzsa (1998) [Ru98], achieves ≫ N^{√2 - 1 + o(1)} (see
`erdos_problem_39.variants.ruzsa_lower`). Erdős proved that every infinite
Sidon set satisfies lim inf |A ∩ {1,…,N}| / N^{1/2} = 0, so N^{1/2} is a
hard barrier (see `erdos_problem_39.variants.liminf_zero`); Erdős and Rényi
showed the growth target is attainable if Sidon is relaxed to bounded
representation multiplicity (see `erdos_problem_39.variants.erdos_renyi`).

Encoding note (all N vs. eventually): the site's ≫_ε is the eventual bound
(∃ C > 0 with the inequality for all sufficiently large N; cf. the upstream
`=O[atTop]` form), while this statement demands it for every N ≥ 1, which
for fixed A additionally forces 1 ∈ A (at N = 1 it reads
countingFn A 1 ≥ C > 0). The two existence statements are nevertheless
equivalent: translating a witness A down by min A − 1 preserves the Sidon
property (sums shift by a constant) and infinitude, puts 1 in the set, and
only increases the counting function; then for each ε the finitely many
N below the eventual threshold are covered by shrinking C (countingFn ≥ 1
there). So the theorem as stated is a faithful rendering of the question.
-/
theorem erdos_problem_39 :
    ∃ A : Set ℕ, A.Infinite ∧ IsSidonSet A ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∀ N : ℕ, 0 < N →
            (countingFn A N : ℝ) ≥ C * (N : ℝ) ^ ((1 : ℝ) / 2 - ε) :=
  sorry

/--
Erdős Problem #39, Ruzsa's lower bound [Ru98] (SOLVED):

There is an infinite Sidon set A ⊂ ℕ with
  |A ∩ {1, …, N}| ≥ N^{√2 - 1 - ε}
for every ε > 0 and all sufficiently large N — the page's
"current best bound of ≫ N^{√2 - 1 + o(1)}, due to Ruzsa". The o(1) in the
exponent absorbs any multiplicative constant, so no constant C is needed.
The exponent √2 is written `(2 : ℝ) ^ ((1 : ℝ) / 2)` (real rpow, already
used in this file) to avoid relying on `Real.sqrt` being in the import
closure. √2 - 1 ≈ 0.41421 > 1/3, comfortably beating the greedy bound.
-/
theorem erdos_problem_39.variants.ruzsa_lower :
    ∃ A : Set ℕ, A.Infinite ∧ IsSidonSet A ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
          (countingFn A N : ℝ) ≥ (N : ℝ) ^ ((2 : ℝ) ^ ((1 : ℝ) / 2) - 1 - ε) :=
  sorry

/--
Erdős Problem #39, the N^{1/2} barrier (SOLVED, Erdős):

Every infinite Sidon set A satisfies
  lim inf_{N → ∞} |A ∩ {1, …, N}| / N^{1/2} = 0.
Stated in unfolded ε-form to avoid `Filter.liminf` on ℝ (whose
`sSup`-based junk values on unbounded sets would otherwise need a separate
boundedness argument): since the sequence is nonnegative, its liminf is 0
iff for every c > 0 there are infinitely many N with
|A ∩ {1, …, N}| < c·N^{1/2}. In particular no infinite Sidon set has
counting function ≫ N^{1/2}, so the exponent 1/2 - ε in the main problem
cannot be improved to 1/2.
-/
theorem erdos_problem_39.variants.liminf_zero :
    ∀ A : Set ℕ, A.Infinite → IsSidonSet A →
      ∀ c : ℝ, 0 < c →
        ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧
          (countingFn A N : ℝ) < c * (N : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

/--
Erdős Problem #39, Erdős–Rényi bounded-multiplicity approximation (SOLVED):

For any ε > 0 there is a set A ⊂ ℕ with
  |A ∩ {1, …, N}| ≫_ε N^{1/2 - ε} for all large N, and
  1_A ∗ 1_A(n) ≪_ε 1 for all n
— i.e. the desired growth is achievable if the Sidon condition (every sum
has at most one representation, up to order) is relaxed to representation
counts bounded by a constant K = K(ε). The representation count is encoded
as the number of unordered pairs {a, n - a} ⊆ A summing to n, via a filter
over a ∈ {0, …, n} with a ≤ n - a; the natural subtraction n - a is exact
since a ≤ n, and boundedness of the unordered count is equivalent to
boundedness of the convolution 1_A ∗ 1_A (they differ by a factor of at
most 2). Note A here is not required (and cannot be required) to be Sidon.
-/
theorem erdos_problem_39.variants.erdos_renyi :
    ∀ ε : ℝ, 0 < ε →
      ∃ A : Set ℕ,
        (∃ C : ℝ, 0 < C ∧
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
            (countingFn A N : ℝ) ≥ C * (N : ℝ) ^ ((1 : ℝ) / 2 - ε)) ∧
        (∃ K : ℕ, ∀ n : ℕ,
          ((Finset.Icc 0 n).filter
            (fun a => a ∈ A ∧ (n - a) ∈ A ∧ a ≤ n - a)).card ≤ K) :=
  sorry
