import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Erdős Problem #1111

If G is a finite graph and A, B are disjoint sets of vertices then we call
A, B anticomplete if there are no edges between A and B.

If t, c ≥ 1 then there exists d ≥ 1 such that if χ(G) ≥ d and ω(G) < t then
there are anticomplete sets A, B with χ(A) ≥ χ(B) ≥ c.

Status: OPEN (erdosproblems.com banner, tooltip "This is open, and cannot be
resolved with a finite computation").

A problem of El Zahar and Erdős [ElEr85], who show that it suffices to
consider the case t ≤ c. Let d(t,c) be the minimal such d. Remarks from the
problem page:

* El Zahar and Erdős note that a result of Wagon [Wa80b] implies
  d(t,2) ≤ C(t,2) + 1, and in fact d(t+1,2) ≤ d(t,2) + t. The page also
  records the exact values d(2,2) = 2, d(3,2) = 4 and d(4,2) = 5 (the page
  writes "t(2,2)=2 and t(3,2)=4 and t(4,2)=5", an evident typo for d(·,·)).
  The recursion and the exact values are recorded here in prose only:
  stating them formally needs a definition of the *minimal* such d, which
  this file does not introduce.
* El Zahar and Erdős proved d(3,3) ≤ 8 and
  d(t,3) ≤ 2·C(t-1,3) + 7·C(t-1,2) + t for t > 3.
* Nguyen, Scott, and Seymour [NSS24] prove that if t, c ≥ 1 then there
  exists d ≥ 1 such that if χ(G) ≥ d and ω(G) < t then there are
  anticomplete sets A, B with χ(B) ≥ c and such that the minimum degree of
  the induced graph on A is at least c. (This is a relaxation of the
  conjecture on the A side, not a strengthening: minimum degree ≥ c does not
  imply χ ≥ c — a c-regular bipartite graph has χ = 2 — while χ ≥ c + 1
  always yields a subgraph of minimum degree ≥ c.)

The page states the conclusion with the ordering χ(A) ≥ χ(B) ≥ c. Since the
anticomplete relation is symmetric in A and B, this is equivalent to
requiring χ(A) ≥ c and χ(B) ≥ c (relabel so the larger is A), which is how
the theorem below states it.

References (titles, journals, years, pages and MR numbers recovered from the
site's bibliography; the volume numbers 5, 29, 165 were not in the site data
and are carried over from the upstream formal-conjectures completion of this
file — consistent with reviewer knowledge, but not site-verified):

[ElEr85] El-Zahar, M. and Erdős, P., _On the existence of two nonneighboring
subgraphs in a graph_. Combinatorica **5** (1985), 295–300. (MR 845138)

[Er85b] Erdős, P., _Problems and results on chromatic numbers in finite and
infinite graphs_. Graph theory with applications to algorithms and computer
science (Kalamazoo, Mich., 1984), (1985), 201–213. (MR 812666)

[Wa80b] Wagon, S., _A bound on the chromatic number of graphs without
certain induced subgraphs_. J. Combin. Theory Ser. B **29** (1980), 345–346.
(MR 602428)

[NSS24] Nguyen, T., Scott, A. and Seymour, P., _On a problem of El-Zahar and
Erdős_. J. Combin. Theory Ser. B **165** (2024), 211–222. (MR 4676642)

https://www.erdosproblems.com/1111
Page last edited 07 December 2025; accessed 2026-02-23.
Tags: graph theory. Related OEIS sequences: "Possible" (none enumerated).
-/

noncomputable section
open SimpleGraph Classical

namespace Erdos1111

/-- Two disjoint sets of vertices A, B are anticomplete in G if there are no edges
    between any vertex in A and any vertex in B. -/
def Anticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b

/--
Erdős Problem #1111 (Open) — El Zahar and Erdős [ElEr85] (see also [Er85b]):

If t, c ≥ 1 then there exists d ≥ 1 such that if G is a finite graph with
χ(G) ≥ d and ω(G) < t, then there exist anticomplete sets A, B ⊆ V(G) with
χ(G[A]) ≥ c and χ(G[B]) ≥ c.

Two disjoint vertex sets A, B are anticomplete if there are no edges between them.
χ denotes the chromatic number and ω the clique number. The condition ω(G) < t
is expressed as G.CliqueFree t (no clique of size t exists). The source states
the conclusion as χ(A) ≥ χ(B) ≥ c; by symmetry of the anticomplete relation
this is equivalent to the symmetric form used here.

El Zahar and Erdős show it suffices to consider t ≤ c. Let d(t,c) be the minimal
such d. Known bounds include d(t,2) ≤ C(t,2)+1 (via Wagon [Wa80b]) and
d(3,3) ≤ 8; Nguyen, Scott, and Seymour [NSS24] proved the variant where the
chromatic-number condition on one of the two sets is replaced by a minimum-degree
condition (see the variants below).
-/
theorem erdos_problem_1111 (t c : ℕ) (ht : 1 ≤ t) (hc : 1 ≤ c) :
    ∃ d : ℕ, 1 ≤ d ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (d : ℕ∞) ≤ G.chromaticNumber →
        G.CliqueFree t →
        ∃ (A B : Set (Fin n)),
          Anticomplete G A B ∧
          (c : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
          (c : ℕ∞) ≤ (G.induce B).chromaticNumber :=
  sorry

/--
Wagon's bound (page-confirmed, SOLVED): d(t,2) ≤ C(t,2) + 1. That is, every
finite graph with χ(G) ≥ C(t,2) + 1 and ω(G) < t contains two anticomplete
sets each of chromatic number at least 2. Noted by El Zahar and Erdős [ElEr85]
as a consequence of a result of Wagon [Wa80b].

Small-parameter sanity: for t = 1 the hypothesis pair (χ ≥ 1, no vertices) is
unsatisfiable, and for t = 2 the pair (χ ≥ 2, no edges) is unsatisfiable, so
both cases hold vacuously — matching the source, whose claim is likewise
vacuous there. The first substantive case t = 3 gives the page's d(3,2) ≤ 4.
-/
theorem erdos_problem_1111.variants.wagon_d_t_two (t : ℕ) (ht : 1 ≤ t) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ((t.choose 2 + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber →
      G.CliqueFree t →
      ∃ (A B : Set (Fin n)),
        Anticomplete G A B ∧
        (2 : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
        (2 : ℕ∞) ≤ (G.induce B).chromaticNumber :=
  sorry

/--
El Zahar–Erdős (page-confirmed, SOLVED): d(3,3) ≤ 8. Every finite
triangle-free graph with χ(G) ≥ 8 contains two anticomplete sets each of
chromatic number at least 3 [ElEr85].
-/
theorem erdos_problem_1111.variants.d_three_three (n : ℕ) (G : SimpleGraph (Fin n))
    (hχ : (8 : ℕ∞) ≤ G.chromaticNumber) (hω : G.CliqueFree 3) :
    ∃ (A B : Set (Fin n)),
      Anticomplete G A B ∧
      (3 : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
      (3 : ℕ∞) ≤ (G.induce B).chromaticNumber :=
  sorry

/--
El Zahar–Erdős (page-confirmed, SOLVED): for t > 3,
d(t,3) ≤ 2·C(t-1,3) + 7·C(t-1,2) + t. Every finite graph with
χ(G) ≥ 2·C(t-1,3) + 7·C(t-1,2) + t and ω(G) < t contains two anticomplete
sets each of chromatic number at least 3 [ElEr85].

The ℕ subtraction t - 1 is safe under the hypothesis 3 < t.
-/
theorem erdos_problem_1111.variants.d_t_three (t : ℕ) (ht : 3 < t) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ((2 * (t - 1).choose 3 + 7 * (t - 1).choose 2 + t : ℕ) : ℕ∞) ≤ G.chromaticNumber →
      G.CliqueFree t →
      ∃ (A B : Set (Fin n)),
        Anticomplete G A B ∧
        (3 : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
        (3 : ℕ∞) ≤ (G.induce B).chromaticNumber :=
  sorry

/--
Nguyen–Scott–Seymour (page-confirmed, SOLVED [NSS24]): if t, c ≥ 1 then there
exists d ≥ 1 such that if χ(G) ≥ d and ω(G) < t then there are anticomplete
sets A, B with χ(G[B]) ≥ c and such that the minimum degree of the induced
graph on A is at least c.

"Minimum degree of G[A] at least c" is encoded as: A is nonempty and every
a ∈ A has at least c neighbours inside A (a Finset of c distinct G-neighbours
of a contained in A; adjacency within A coincides with adjacency in the induced
graph). The explicit `A.Nonempty` is essential: without it A = ∅ satisfies the
minimum-degree condition vacuously and (∅, B) is anticomplete for any B, which
would trivialize the statement.
-/
theorem erdos_problem_1111.variants.nguyen_scott_seymour (t c : ℕ)
    (ht : 1 ≤ t) (hc : 1 ≤ c) :
    ∃ d : ℕ, 1 ≤ d ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (d : ℕ∞) ≤ G.chromaticNumber →
        G.CliqueFree t →
        ∃ (A B : Set (Fin n)),
          Anticomplete G A B ∧
          A.Nonempty ∧
          (∀ a ∈ A, ∃ T : Finset (Fin n), ↑T ⊆ A ∧ T.card = c ∧ ∀ b ∈ T, G.Adj a b) ∧
          (c : ℕ∞) ≤ (G.induce B).chromaticNumber :=
  sorry

end Erdos1111
