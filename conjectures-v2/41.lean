import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup

open scoped Classical
open Filter

/-!
# Erdős Problem #41

Let $A\subset\mathbb{N}$ be an infinite set such that the triple sums
$a+b+c$ are all distinct for $a,b,c\in A$ (aside from the trivial
coincidences). Is it true that
$$\liminf \frac{\lvert A\cap \{1,\ldots,N\}\rvert}{N^{1/3}}=0?$$

**Status: OPEN** — banner tooltip: "This is open, and cannot be resolved
with a finite computation." **$500** prize. (erdosproblems.com/41, page
last edited 23 January 2026, accessed 2026-03-05; the teorth/erdosproblems
metadata mirror — commit a09c7a2, 2026-08-14 — agrees: state "open", last
update 2025-08-31, prize $500, OEIS N/A, tags "number theory", "sidon
sets", "additive combinatorics".)

Remarks from the source page:

- Erdős proved that if the pairwise sums $a+b$ are all distinct aside from
  the trivial coincidences then
  $\liminf \lvert A\cap \{1,\ldots,N\}\rvert/N^{1/2}=0$. (Formalized below
  as `erdos_problem_41.variants.pairwise_erdos`.)
- This is discussed in problem C11 of Guy's collection [Gu04], in which
  Guy says Erdős offered \$500 for the general problem of whether, for all
  $h\geq 2$, $\liminf \lvert A\cap \{1,\ldots,N\}\rvert/N^{1/h}=0$
  whenever the sums of $h$ terms in $A$ are distinct. (Formalized below as
  `erdos_problem_41.variants.bh_general`.)
- This was proved for $h=4$ by Nash [Na89] (recorded in prose here — it is
  subsumed by the even-$h$ result) and for all even $h$ by Chen [Ch96b]
  (formalized below as `erdos_problem_41.variants.chen_even`; note $h=2$,
  Erdős's own case, is also even).

Additional thanks (page): Zachary Chase. 0 forum comments.

Formalised statement? **Yes** — upstream google-deepmind/formal-conjectures
`FormalConjectures/ErdosProblems/41.lean` (present at HEAD dd1c2beb) states
the same conjecture as a bare open assertion,
`Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0`
under its `NtupleCondition A 3` and `A.Infinite`, plus a solved pairwise
variant. Caveat on upstream: its `NtupleCondition` quantifies over
`Finset`s, i.e. tuples of *distinct* elements, so it does not constrain
sums with repeated terms such as $a+a+b$; the multiset-faithful notion
(used by this file's `IsB3Set` via sorted triples) constrains those too
and is the standard $B_3$ definition.

## References

Problem sources on the page: [Er77c] [ErGr80] [Er81] [Er85c] [Er91] [Er95]
[Er97c] [Va99, 1.23]; remarks cite [Gu04] [Na89] [Ch96b]. No `/latex/41`
fetch exists in the session logs, so no bibliography could be recovered
from the site itself; the entries below are honest stubs with their
provenance flagged, and the rest are keys only: DEFERRED.

- [Er77c] Erdős, P., _Problems and results on combinatorial number
  theory. III_. Number Theory Day (Proc. Conf., Rockefeller Univ., New
  York, 1976) (1977), 43-72. (Stub: sibling-corpus consensus; unverified
  offline.)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement
  Mathématique 28 (1980). (Stub: sibling-corpus and upstream consensus;
  unverified offline.)
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
  This problem: §1.23. (Stub: from sibling corpus files; unverified
  offline.)
- [Gu04] Guy, R. K., _Unsolved problems in number theory_. 3rd ed.,
  Springer (2004), xviii+437. Problem C11. (Stub: from sibling corpus
  files; unverified offline.)
- [Na89] Nash, J. C. M. (1989). Author name and year from the page
  prose/key; the standard citation _On B₄-sequences_, Canad. Math. Bull.
  32 (1989), 446-449, is reviewer-supplied and unverified offline.
- [Ch96b] Chen, S. (1996). Author name and year from the page prose/key;
  the candidate citation _A note on B_{2k}-sequences_, J. Number Theory
  56 (1996), 1-3, is reviewer-supplied and unverified offline.
- [Er91] [Er97c] — keys only; no reliable corpus expansion (the corpus's
  entries for these keys conflict): DEFERRED.

Tags: number theory, sidon sets, additive combinatorics
https://www.erdosproblems.com/41
-/

/--
A set A ⊆ ℕ is a **B₃ set** if all triple sums are distinct aside from
trivial coincidences: for a ≤ b ≤ c and d ≤ e ≤ f, all in A,
a + b + c = d + e + f implies a = d, b = e, c = f.

(Sorted-triple formulation; equivalent to "the multisets {a,b,c} and
{d,e,f} coincide whenever their sums agree", i.e. to `IsBhSet A 3` below:
sort each multiset to compare component-wise. Repeated elements are
allowed in a triple — e.g. a + a + b collisions are constrained — which is
the standard B₃ notion; the upstream formal-conjectures `NtupleCondition`
uses `Finset`s and therefore constrains only distinct-element triples.)
-/
def IsB3Set (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, ∀ e ∈ A, ∀ f ∈ A,
    a + b + c = d + e + f → a ≤ b → b ≤ c → d ≤ e → e ≤ f →
      a = d ∧ b = e ∧ c = f

/--
A set A ⊆ ℕ is a **B₂ (Sidon) set** if all pairwise sums are distinct
aside from trivial coincidences: for a ≤ b and c ≤ d, all in A,
a + b = c + d implies a = c and b = d.

(Same sorted-tuple style as `IsB3Set`; equivalent to `IsBhSet A 2`.
Used by the page-confirmed variant `erdos_problem_41.variants.pairwise_erdos`.)
-/
def IsB2Set (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → a ≤ b → c ≤ d → a = c ∧ b = d

/--
A set A ⊆ ℕ is a **Bₕ set** if all h-fold sums are distinct aside from
trivial coincidences (permutations of the summands): any two size-h
multisets of elements of A with equal sums coincide. Repeated summands are
allowed, matching the standard Bₕ definition. For h = 0 and h = 1 the
condition is trivially true; the interesting range is h ≥ 2.

(For h = 3 this is equivalent to `IsB3Set`, and for h = 2 to `IsB2Set`,
by sorting each multiset and comparing component-wise.)
-/
def IsBhSet (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ s t : Multiset ℕ,
    (∀ x ∈ s, x ∈ A) → (∀ x ∈ t, x ∈ A) →
      Multiset.card s = h → Multiset.card t = h →
        s.sum = t.sum → s = t

/--
The counting function for A up to N: |A ∩ {1, …, N}|.

(`Finset.Icc 1 N` is exactly {1, …, N} — in particular a possible element
0 ∈ A is never counted, matching the site's ℕ = {1, 2, …}; membership in
`A : Set ℕ` is decided classically via `open scoped Classical`, which is
why the definition is `noncomputable`.)
-/
noncomputable def countingFn41 (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/--
Erdős Problem #41 [Er77c, ErGr80, Er81, Er85c, Er91, Er95, Er97c, Va99] —
OPEN, $500 prize (erdosproblems.com/41, page last edited 23 January 2026,
accessed 2026-03-05; status cross-checked open against the
teorth/erdosproblems metadata mirror):

Let A ⊂ ℕ be an infinite B₃ set (all triple sums a + b + c are distinct
aside from trivial coincidences). Is it true that
  lim inf |A ∩ {1, …, N}| / N^{1/3} = 0 ?

The theorem below asserts the affirmative (conjectured) direction of this
open yes/no question, matching the upstream formal-conjectures encoding
(a bare open assertion of the same liminf identity).

Erdős proved the analogous result for B₂ sets (Sidon sets): every infinite
Sidon set satisfies lim inf |A ∩ {1,…,N}| / N^{1/2} = 0 (see
`erdos_problem_41.variants.pairwise_erdos`). The general conjecture for
Bₕ sets (h-fold sums distinct), for which Guy [Gu04, problem C11] reports
Erdős offered the $500, states that lim inf |A ∩ {1,…,N}| / N^{1/h} = 0
for every h ≥ 2 (see `erdos_problem_41.variants.bh_general`). This was
proved for h = 4 by Nash [Na89] and for all even h by Chen [Ch96b] (see
`erdos_problem_41.variants.chen_even`).

Encoding note (ℝ-valued `liminf` safety): `Filter.liminf` on ℝ is
`sSup {a | ∀ᶠ N in atTop, a ≤ f N}`, and `Real.sSup` returns the junk
value 0 on unbounded sets. Here the set of eventual lower bounds is
nonempty (f ≥ 0, so 0 belongs) and bounded above *given the hypotheses*:
for a B₃ set, k = |A ∩ [1,N]| elements yield C(k+2,3) ≥ k³/6 pairwise
distinct triple sums, all lying in [0, 3N], so k³ ≤ 6(3N+1) and
f N = k/N^{1/3} ≤ 24^{1/3} < 3 for N ≥ 1. Hence the `sSup` is genuine and
the statement is the intended liminf identity — no junk-value
trivialization. (At N = 0 the term is 0/0 = 0 in Lean, harmless at
`atTop`.)
-/
theorem erdos_problem_41 (A : Set ℕ) (hA : A.Infinite) (hB3 : IsB3Set A) :
    liminf (fun N => (countingFn41 A N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3)) atTop = 0 :=
  sorry

/--
Erdős Problem #41, the pairwise (B₂ / Sidon) case (SOLVED, Erdős):

If A ⊂ ℕ is infinite and its pairwise sums a + b are all distinct aside
from the trivial coincidences, then
  lim inf |A ∩ {1, …, N}| / N^{1/2} = 0.
Page-confirmed: "Erdős proved that if the pairwise sums a+b are all
distinct aside from the trivial coincidences then
liminf |A ∩ {1,…,N}|/N^{1/2} = 0." The upstream formal-conjectures file
carries the same variant (`erdos_41.variants.pairwise`, research solved).

(ℝ-`liminf` safety, as for the main theorem: for a Sidon set,
k = |A ∩ [1,N]| gives C(k+1,2) ≥ k²/2 distinct pairwise sums in [0, 2N],
so k²/2 ≤ 2N + 1 and the sequence is bounded by √6; the eventual-lower-
bound set is nonempty and bounded above, so no junk values arise.)
-/
theorem erdos_problem_41.variants.pairwise_erdos
    (A : Set ℕ) (hA : A.Infinite) (hB2 : IsB2Set A) :
    liminf (fun N => (countingFn41 A N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 2)) atTop = 0 :=
  sorry

/--
Erdős Problem #41, the general Bₕ problem (OPEN — this is the $500
general problem reported in Guy [Gu04, problem C11]):

For every h ≥ 2, if A ⊂ ℕ is infinite and the sums of h terms of A are
distinct aside from trivial coincidences (`IsBhSet A h`), then
  lim inf |A ∩ {1, …, N}| / N^{1/h} = 0.
The case h = 2 is Erdős's theorem, h = 3 is the main statement of this
problem, h = 4 is Nash [Na89], and all even h are Chen [Ch96b]; odd
h ≥ 3 remain open.

(The hypothesis 2 ≤ h matters for well-formedness, not only content: at
h = 0 the Bₕ condition is vacuous and N^{1/h} would degenerate — Lean's
1/(0:ℝ) = 0 gives N^0 = 1 and the sequence |A ∩ [1,N]| → ∞, whose
eventual-lower-bound set is all of ℝ and whose Real-liminf is the junk
value 0, making the h = 0 instance "true" vacuously. With 2 ≤ h the usual
counting bound C(k+h-1,h) ≥ kʰ/h! of distinct h-fold sums in [0, hN]
gives k ≤ (h·h!·(N+1))^{1/h}, so the sequence is bounded and the liminf
is genuine.)
-/
theorem erdos_problem_41.variants.bh_general
    (h : ℕ) (hh : 2 ≤ h)
    (A : Set ℕ) (hA : A.Infinite) (hBh : IsBhSet A h) :
    liminf (fun N => (countingFn41 A N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / (h : ℝ))) atTop = 0 :=
  sorry

/--
Erdős Problem #41, the even-h case (SOLVED, Chen [Ch96b]; the case h = 4
was proved earlier by Nash [Na89]):

For every even h ≥ 2, every infinite Bₕ set A ⊂ ℕ satisfies
  lim inf |A ∩ {1, …, N}| / N^{1/h} = 0.
Page-confirmed: "This was proved for h = 4 by Nash [Na89] and for all
even h by Chen [Ch96b]." (h = 2 — even — is Erdős's own pairwise
theorem, so this statement subsumes both `pairwise_erdos` and Nash's
h = 4 result. ℝ-`liminf` safety as in `bh_general`.)
-/
theorem erdos_problem_41.variants.chen_even
    (h : ℕ) (hh : 2 ≤ h) (hEven : Even h)
    (A : Set ℕ) (hA : A.Infinite) (hBh : IsBhSet A h) :
    liminf (fun N => (countingFn41 A N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / (h : ℝ))) atTop = 0 :=
  sorry
