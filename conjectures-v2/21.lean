import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #21

Verbatim source statement (erdosproblems.com/21):

> Let $f(n)$ be minimal such that there is an intersecting family $\mathcal{F}$
> of sets of size $n$ (so $A\cap B\neq\emptyset$ for all $A,B\in \mathcal{F}$)
> with $\lvert \mathcal{F}\rvert=f(n)$ such that any set $S$ with
> $\lvert S\rvert \leq n-1$ is disjoint from at least one $A\in \mathcal{F}$.
> Is it true that $f(n) \ll n$?

The site phrases the problem as a yes/no question; this file asserts the proved
"yes" direction as a direct statement, the convention of this raw corpus.

Status (page accessed 2026-02-24, page edition 03 December 2025; cross-checked
against the teorth/erdosproblems metadata mirror, `data/problems.yaml`, which
agrees): **PROVED** — "This has been solved in the affirmative." — with a $500
prize.

Conjectured by Erdős and Lovász [ErLo75], who proved
$\frac{8}{3}n - 3 \leq f(n) \ll n^{3/2}\log n$ for all $n$. The upper bound was
improved by Kahn [Ka92b] to $f(n) \ll n\log n$. (The upper bound constructions
in both cases are formed by taking a random set of lines from a projective
plane of order $n-1$, assuming $n-1$ is a prime power.) The problem was solved
by Kahn [Ka94], who proved the upper bound $f(n) \ll n$. The Erdős–Lovász lower
bound of $\frac{8}{3}n - O(1)$ has not been improved, and it has been
speculated (see e.g. [Ka94]) that the correct answer is $3n + O(1)$.

It is trivial that $f(1)=1$ and $f(2)=3$. The values $f(3)=6$ and $f(4)=9$ were
established by Tripathi [Tr14]. Barát and Wanless [BaWa21] proved that
$f(5)=13$, and that $13 \leq f(6) \leq 18$.

Problem sources cited on the page: [Er81], [Er90], [Er92b], [Er97f].

References (recovered offline from the archived page, the pipeline's
`erdosproblems.com/latex/21` fetch preserved in the session logs, and sibling
corpus files; honest stubs where noted — nothing guessed):

- [Er81] Erdős, P., _On the combinatorial problems which I would most like to
  see solved_. Combinatorica 1 (1981), 25-42. (Sibling-corpus consensus,
  including a sibling /latex recovery of the same key; not in the /latex/21
  extraction.)
- [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to
  Paul Erdős (1990), 467-478. (Sibling-corpus consensus; not in the /latex/21
  extraction.)
- [Er92b] Erdős, P., _Some of my favourite problems in various branches of
  combinatorics_. Matematiche (Catania) 47 (1992), 231-240. (Sibling-corpus
  consensus; not in the /latex/21 extraction.)
- [Er97f] Erdős, P. (1997). (Key-only stub; sibling files disagree on this
  key's expansion, so no details are recorded.)
- [ErLo75] Erdős, P. and Lovász, L., _Problems and results on 3-chromatic
  hypergraphs and some related questions_. Infinite and finite sets (Colloq.,
  Keszthely, 1973; dedicated to P. Erdős on his 60th birthday), Vol. II
  (1975), 609-627. (Pages from the /latex/21 fetch; proceedings data from the
  styled sibling file — the /latex extraction did not name the venue.)
- [Ka92b] Kahn, J., _On a problem of Erdős and Lovász: random lines in a
  projective plane_. Combinatorica 12 (1992), 417-423. (Title, journal, year,
  pages from the /latex/21 fetch; volume from the original pipeline's
  citation-fix pass.)
- [Ka94] Kahn, J., _On a problem of Erdős and Lovász. II. n(r)=O(r)_.
  J. Amer. Math. Soc. 7 (1994), no. 1, 125-143. (/latex/21 fetch; volume and
  issue from the styled sibling file.)
- [Tr14] Tripathi, A., _A result on intersecting families with maximum
  transversal size_. Preprint (2014), arXiv:1409.4610. (/latex/21 fetch.)
- [BaWa21] Barát, J. and Wanless, I. M., _Intersecting and 2-intersecting
  hypergraphs with maximal covering number_. J. Combin. Des. 29 (2021),
  no. 3, 260-286. (Title, journal, year, pages from the /latex/21 fetch;
  volume and issue from the styled sibling file.)

Related OEIS sequence: A391599 (contents unverifiable offline).

Additional thanks (page): Noga Alon, Zachary Chase, and Alexis Olson.

Tags: combinatorics, intersecting family
https://www.erdosproblems.com/21
-/

/--
A family F of n-element subsets of ℕ is intersecting if every two members
of F have non-empty intersection.

Note the pair condition ranges over all A, B ∈ F including A = B, so members
must be nonempty; this is automatic for n ≥ 1 (each member has card n) and
for n = 0 it forces F = ∅.
-/
def IsIntersectingNFamily (F : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  (∀ A ∈ F, A.card = n) ∧ (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)

/--
A family F of n-sets covers all small sets if every set S with |S| ≤ n - 1
is disjoint from at least one member of F.

The quantification over all finite S ⊆ ℕ is equivalent to the source's
quantification over arbitrary small sets: for any abstract S, only
S ∩ ⋃ F matters (any A ∈ F disjoint from S ∩ ⋃ F is disjoint from S), and
that intersection is a finite subset of the ground set. Taking S = ∅
(card 0 ≤ n - 1) forces F to be nonempty, for every n — including n = 0,
where ℕ-subtraction gives n - 1 = 0.
-/
def CoversAllSmallSets (F : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

/--
f(n) is the minimal size of an intersecting family of n-sets that covers
all sets of size at most n - 1.

For n ≥ 1 the feasible set of cardinalities is nonempty (witness: the family
of all n-element subsets of a fixed (2n-1)-element set is intersecting, and
any S with |S| ≤ n - 1 leaves at least n of the 2n-1 points uncovered, hence
misses some member entirely), so `sInf` is a genuine minimum and this matches
the source's f(n). For n = 0 no family qualifies (`IsIntersectingNFamily`
forces F = ∅, while `CoversAllSmallSets` requires F ≠ ∅), so the feasible set
is empty and `sInf ∅ = 0` yields the junk value f(0) = 0 — harmless, since
the theorems below only constrain n ≥ 1 or eventual behaviour.
-/
noncomputable def erdosLovaszF (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ F : Finset (Finset ℕ),
    F.card = k ∧ IsIntersectingNFamily F n ∧ CoversAllSmallSets F n}

/--
Erdős Problem #21 (PROVED — solved by Kahn [Ka94]; $500 prize):
Let f(n) be the minimal size of an intersecting family F of n-element sets such
that any set S with |S| ≤ n - 1 is disjoint from at least one A ∈ F.
Then f(n) ≪ n, i.e., there exist constants C > 0 and N₀ such that
f(n) ≤ C · n for all n ≥ N₀.

The source asks this as a yes/no question ("Is it true that f(n) ≪ n?"); this
statement asserts the proved "yes" direction, the convention of this raw
corpus. The eventual form is equivalent to the global form "f(n) ≤ C·n for
all n ≥ 1": f is everywhere finite, so the finitely many n < N₀ are absorbed
by enlarging C.

Erdős and Lovász [ErLo75] proved (8/3)n - 3 ≤ f(n) ≪ n^{3/2} log n.
Kahn [Ka92b] improved the upper bound to f(n) ≪ n log n.
Kahn [Ka94] proved the upper bound f(n) ≪ n, settling the conjecture.
-/
theorem erdos_problem_21 :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (erdosLovaszF n : ℝ) ≤ C * n :=
  sorry

/--
**Erdős–Lovász lower bound** (variant of Erdős Problem #21) [ErLo75]:
(8/3)n - 3 ≤ f(n), proved for all n in the paper that posed the conjecture.
This lower bound has not been improved (up to the O(1) term).

The `1 ≤ n` hypothesis tracks the source's implicit domain; the inequality
would in fact also hold at the junk value n = 0 (where -3 ≤ 0), so the guard
is safe in both directions. Consistent with the known small values: at n = 6
it gives 13 ≤ f(6), matching [BaWa21]'s lower bound exactly.

Statement added by the review pipeline from the recovered page content; NOT
compile-verified.
-/
theorem erdos_problem_21.variants.lower_bound :
    ∀ n : ℕ, 1 ≤ n → (8 / 3 : ℝ) * n - 3 ≤ (erdosLovaszF n : ℝ) :=
  sorry

/--
**Known small values** (variant of Erdős Problem #21):
f(1) = 1 and f(2) = 3 are trivial; f(3) = 6 and f(4) = 9 were established by
Tripathi [Tr14]; f(5) = 13 by Barát and Wanless [BaWa21]. See OEIS A391599.

Statement added by the review pipeline from the recovered page content; NOT
compile-verified.
-/
theorem erdos_problem_21.variants.small_values :
    erdosLovaszF 1 = 1 ∧ erdosLovaszF 2 = 3 ∧ erdosLovaszF 3 = 6 ∧
      erdosLovaszF 4 = 9 ∧ erdosLovaszF 5 = 13 :=
  sorry

/--
**Bounds on f(6)** (variant of Erdős Problem #21) [BaWa21]:
Barát and Wanless proved 13 ≤ f(6) ≤ 18.

Statement added by the review pipeline from the recovered page content; NOT
compile-verified.
-/
theorem erdos_problem_21.variants.f_six_bounds :
    13 ≤ erdosLovaszF 6 ∧ erdosLovaszF 6 ≤ 18 :=
  sorry

/--
**Speculated exact asymptotics** (OPEN; variant of Erdős Problem #21):
It has been speculated (see e.g. [Ka94]) that the correct answer is
f(n) = 3n + O(1), i.e., there is a constant C with |f(n) - 3n| ≤ C for all
n ≥ 1. This is strictly stronger than both Kahn's f(n) ≪ n and the
Erdős–Lovász lower bound (8/3)n - O(1). Stated in the raw corpus's direct
assertion form for the speculated direction; the speculation is open.

The global `∀ n ≥ 1` form is equivalent to the eventual O(1) form, since f is
everywhere finite and finitely many exceptions are absorbed into C.

Statement added by the review pipeline from the recovered page content; NOT
compile-verified.
-/
theorem erdos_problem_21.variants.speculated_exact_asymptotics :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |(erdosLovaszF n : ℝ) - 3 * n| ≤ C :=
  sorry
