import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Finset

/-- A finite set of natural numbers is a Sidon set (also called a B₂ set) if all
    pairwise sums a + b (allowing a = b) are distinct: whenever a + b = c + d
    with a, b, c, d ∈ A, we have {a, b} = {c, d} as multisets. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/--
Erdős Problem #44 [Er84b, p.16] [Er91] [Er95] [Er97c] — OPEN
(erdosproblems.com/44, page last edited 09 January 2026, accessed 2026-03-05):

Let N ≥ 1 and A ⊆ {1, ..., N} be a Sidon set. Is it true that, for any ε > 0,
there exist M and B ⊆ {N+1, ..., M} (which may depend on N, A, ε) such that
A ∪ B ⊆ {1, ..., M} is a Sidon set of size at least (1 - ε) · M^{1/2}?

In other words, can any Sidon set be extended to a nearly optimal-size Sidon set
in some larger interval?

Status and provenance:
- Page banner at capture: OPEN, tooltip "This is open, and cannot be resolved
  with a finite computation" (plus the site's standard open-status disclaimer).
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  commit a09c7a21, 2026-08-14) agrees: state "open", last update 2025-08-31;
  no prize; OEIS: N/A.
- The upstream formal-conjectures file (FormalConjectures/ErdosProblems/44.lean,
  present at HEAD dd1c2beb, 2026-08-16) marks `erdos_44` as `research open` and
  states `answer(sorry) ↔ ∀ᵉ (N ≥ 1) (A ⊆ Icc 1 N), IsSidon A → ∀ᵉ (ε > 0),
  ∃ᵉ (M > N) (B ⊆ Icc (N+1) M), IsSidon (A ∪ B) ∧ (1 - ε) * √M ≤ (A ∪ B).card`
  — the same proposition as below, modulo the redundant `Disjoint` conjunct
  (see the encoding notes). The direct assertion below is the affirmative
  (conjectured) direction of this open yes/no question.

Remark from the source page: "See also [329] and [707] (indeed a positive
solution to [707] implies a positive solution to this problem, which in turn
implies a positive solution to [329]). This is discussed in problem C9 of
Guy's collection [Gu04]."

Encoding notes:
- `N < M`: the page leaves the size of M implicit (B ⊆ {N+1, ..., M} forces
  B = ∅ whenever M ≤ N). Requiring M > N matches the upstream `∃ᵉ (M > N)`
  encoding and does not change the universally quantified statement: a
  witness for the relaxed reading at N' = N + 1 with the same A (still Sidon,
  still inside {1, ..., N+1}) yields M ≥ N + 1 > N and
  B ⊆ {N+2, ..., M} ⊆ {N+1, ..., M}, i.e. a witness for the strict form; the
  converse is immediate.
- `Disjoint A B` is redundant: it already follows from ∀ a ∈ A, a ≤ N and
  ∀ b ∈ B, N + 1 ≤ b. It is kept (harmless, and it makes
  (A ∪ B).card = A.card + B.card immediate for readers); it does not change
  satisfiability since every B meeting the membership bound is disjoint
  from A.
- A ∪ B ⊆ {1, ..., M} is implied by the two membership bounds together with
  N < M, so it is not restated.
- All arithmetic in the size bound happens in ℝ after coercion
  ((A ∪ B).card : ℝ, Real.sqrt (M : ℝ)); no ℕ subtraction or division occurs
  anywhere ((1 - ε) is real).

References (no /latex/44 capture exists in the session logs, so no
bibliography could be recovered from the site itself; entries below are
honest stubs with provenance flagged, the rest are keys only: DEFERRED):
- [Er84b] Erdős, P., _On some problems in graph theory, combinatorial
  analysis and combinatorial number theory_. Graph theory and combinatorics
  (Cambridge, 1983), Academic Press, London (1984), 1-17. This problem:
  p. 16. (Stub: sibling-corpus entry carried by `deepmind/deepmind/545.lean`
  and `546.lean`; unverified offline.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas 1 (1995), 165-186. (Stub:
  corpus-majority entry; unverified offline.)
- [Gu04] Guy, R. K., _Unsolved problems in number theory_. 3rd ed., Springer
  (2004), xviii+437. Problem C9. (Stub: from sibling corpus files;
  unverified offline.)
- [Er91] [Er97c] — keys only; no reliable corpus expansion (the corpus's
  entries for these keys conflict): DEFERRED.

Tags: number theory | sidon sets | additive combinatorics. No prize;
OEIS: N/A. Formalised statement? Yes (upstream, see above). Additional
thanks to: Gusarich and Desmond Weisenberg.
Source: https://www.erdosproblems.com/44
-/
theorem erdos_problem_44 :
    ∀ (ε : ℝ), 0 < ε →
      ∀ (N : ℕ) (A : Finset ℕ),
        1 ≤ N →
        IsSidonSet A →
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
        ∃ (M : ℕ) (B : Finset ℕ),
          N < M ∧
          (∀ b ∈ B, N + 1 ≤ b ∧ b ≤ M) ∧
          Disjoint A B ∧
          IsSidonSet (A ∪ B) ∧
          (((A ∪ B).card : ℝ) ≥ (1 - ε) * Real.sqrt (M : ℝ)) :=
  sorry

/--
Empty-start variant, after upstream `erdos_44.variants.empty_start` ("The case
where we start with an empty set (constructing large Sidon sets)", tagged
`research open` there with `answer(sorry)`): for any ε > 0, every sufficiently
large M admits a Sidon set A ⊆ {1, ..., M} of size at least (1 - ε) · M^{1/2}.

Upstream writes the eventuality as `∀ᶠ (M : ℕ) in Filter.atTop`; here it is
encoded equivalently as ∃ M₀, ∀ M ≥ M₀, using only constructs already present
in this file (no filter import needed).

Reviewer note (flagged, not from the page): unlike the main problem, this
special case is classically known to be true — Singer difference sets give
Sidon subsets of {1, ..., q² + q + 1} of size q + 1 for every prime power q,
and combining this with the density of primes yields maximal Sidon sets of
size (1 + o(1)) · M^{1/2} in {1, ..., M} for all large M (Erdős–Turán 1941,
Singer 1938). Upstream nevertheless conservatively tags the variant
`research open`; this assessment is reviewer-supplied and unverified offline.

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_44.variants.empty_start :
    ∀ (ε : ℝ), 0 < ε →
      ∃ M₀ : ℕ, ∀ (M : ℕ), M₀ ≤ M →
        ∃ (A : Finset ℕ),
          (∀ a ∈ A, 1 ≤ a ∧ a ≤ M) ∧
          IsSidonSet A ∧
          ((A.card : ℝ) ≥ (1 - ε) * Real.sqrt (M : ℝ)) :=
  sorry
