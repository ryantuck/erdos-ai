import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph

/-!
# Erdős Problem #81

*Reference:* [erdosproblems.com/81](https://www.erdosproblems.com/81)
(accessed 2026-02-22, page edition 28 December 2025; content recovered from
archived session-log captures — the live site is unreachable from the review
container).

Statement (verbatim from the site): "Let $G$ be a chordal graph on $n$
vertices - that is, $G$ has no induced cycles of length greater than $3$.
Can the edges of $G$ be partitioned into $n^2/6+O(n)$ many cliques?"

Status: **OPEN** ("This is open, and cannot be resolved with a finite
computation."). The teorth/erdosproblems metadata mirror
(`data/problems.yaml`, commit a09c7a2, 2026-08-14) agrees: state "open",
last update 2025-08-31; no prize; OEIS "possible" (no specific sequence);
tags: graph theory; not formalized upstream (no
`FormalConjectures/ErdosProblems/81.lean` exists at upstream HEAD dd1c2be,
2026-08-16, which does contain 80 and 82).

Remarks (from the page): asked by Erdős, Ordman, and Zalcstein [EOZ93], who
proved an upper bound of $(1/4-\epsilon)n^2$ many cliques (for some very
small $\epsilon > 0$). The example of all edges between a complete graph on
$n/3$ vertices and an empty graph on $2n/3$ vertices shows that
$n^2/6 + O(n)$ is sometimes necessary. A split graph is one where the
vertices can be split into a clique and an independent set; every split
graph is chordal, and Chen, Erdős, and Ordman [CEO94] have shown that any
split graph can be partitioned into $\frac{3}{16}n^2 + O(n)$ many cliques.
See also Erdős Problem [1017] (general clique partition numbers).

References (provenance per entry; the `/latex/81` bibliography survives in
the session logs only as a WebFetch summary, which lists exactly the two
entries [CEO94] and [EOZ93]; nothing fabricated):

- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165-186. (The page's
  problem-source key; bibliographic data is the shared-site-global-key
  expansion established by earlier recoveries of the same key — verification
  against `/latex/81` itself is DEFERRED, since that extraction covers only
  the two remark citations below.)
- [EOZ93] Erdős, P., Ordman, E.T., and Zalcstein, Y., _Clique partitions of
  chordal graphs_. Combinatorics, Probability and Computing (1993), 409-415.
  (From the `/latex/81` WebFetch summary; the journal volume number was not
  captured there and is therefore omitted — DEFERRED.)
- [CEO94] Chen, G., Erdős, P., and Ordman, E.T., _Clique partitions of split
  graphs_. In: Combinatorics, graph theory, algorithms and applications
  (Beijing, 1993). 1994, 21-30. (From the `/latex/81` WebFetch summary.)

NOTE (review pipeline): the `IsSplitGraph` definition and the three
`variants` theorems below were added by the Fable review from page-confirmed
content, using only constructs already present in the original file; they are
NOT compile-verified. The two original `def`s and the main theorem are
unchanged from `conjectures/81.lean`, which the original pipeline session
built successfully with `lake build` (only the expected `sorry` warning); the
`IsChordal`/`HasInducedCycle` pair was additionally verified in this review by
brute-force simulation against the standard chordality definition on all
33,868 graphs with at most 6 vertices (no mismatches).
-/

/--
An induced cycle of length k in a simple graph G: an injective map f : Fin k → V
such that G.Adj (f i) (f j) holds if and only if i and j are consecutive modulo k.
This captures the notion that f traces out a cycle with no chords.
-/
def HasInducedCycle {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : Fin k → V, Function.Injective f ∧
    ∀ i j : Fin k, i ≠ j →
      (G.Adj (f i) (f j) ↔ (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val)

/--
A graph is chordal if it contains no induced cycle of length ≥ 4.
Equivalently, every cycle of length ≥ 4 has a chord.
-/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, 4 ≤ k → ¬HasInducedCycle G k

/--
Erdős Problem #81 (asked by Erdős, Ordman, Zalcstein [EOZ93]; source [Er95]):

Let G be a chordal graph on n vertices — that is, G has no induced cycles of
length greater than 3. Can the edges of G be partitioned into n²/6 + O(n)
many cliques?

The example of all edges between a complete graph on n/3 vertices and an empty
graph on 2n/3 vertices shows that n²/6 + O(n) is sometimes necessary.

Formalized as: there exists a constant C > 0 such that for all n and all
chordal graphs G on n vertices, there exists a collection P of cliques
(vertex sets, each pairwise adjacent in G) that partition the edges of G,
with |P| ≤ n²/6 + C·n.

Status: OPEN (page edition 28 December 2025; mirror-confirmed current as of
2026-08-14). Encoding note: the source poses an open yes/no question; per
this corpus's convention (no `answer()` elaborator with Mathlib-only
imports), the statement asserts the affirmative direction — the direction
suggested by the lower-bound example above and by [EOZ93]'s (1/4−ε)n² upper
bound. If the question is ever resolved negatively, this statement must be
negated. Note also that the quantifier order (∃ C before ∀ n) is essential:
the reversed order would be trivially true.
-/
theorem erdos_problem_81 :
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      IsChordal G →
      ∃ P : Finset (Finset (Fin n)),
        -- Each set in P is a clique in G
        (∀ S ∈ P, G.IsClique (↑S : Set (Fin n))) ∧
        -- Every edge of G is covered by some clique in P
        (∀ u v : Fin n, G.Adj u v → ∃ S ∈ P, u ∈ S ∧ v ∈ S) ∧
        -- No edge belongs to two distinct cliques (partition, not just cover)
        (∀ S₁ ∈ P, ∀ S₂ ∈ P, S₁ ≠ S₂ →
          ∀ u v : Fin n, u ∈ S₁ → v ∈ S₁ → u ∈ S₂ → v ∈ S₂ → ¬G.Adj u v) ∧
        -- The number of cliques is at most n²/6 + C·n
        (P.card : ℝ) ≤ (n : ℝ) ^ 2 / 6 + C * (n : ℝ) :=
  sorry

/--
A graph is a split graph if its vertex set can be split into a clique K and an
independent set (the complement of K). Either part may be empty. Every split
graph is chordal.
-/
def IsSplitGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ K : Set V, G.IsClique K ∧ ∀ u v : V, u ∉ K → v ∉ K → ¬G.Adj u v

/--
Erdős Problem #81, upper bound (page-confirmed known result, [EOZ93]):
Erdős, Ordman, and Zalcstein proved that the edges of any chordal graph on n
vertices can be partitioned into at most (1/4 − ε)n² many cliques, for some
very small ε > 0.

Small-parameter caveat: read literally for *all* n, the page's bound is
false — at n = 2 the complete graph K₂ is chordal and needs one clique to
cover its edge, while (1/4 − ε)·2² = 1 − 4ε < 1. The bound is therefore
formalized in eventual form (for all sufficiently large n), which is the
intended asymptotic reading.
-/
theorem erdos_problem_81.variants.eoz_upper_bound :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ G : SimpleGraph (Fin n),
      IsChordal G →
      ∃ P : Finset (Finset (Fin n)),
        (∀ S ∈ P, G.IsClique (↑S : Set (Fin n))) ∧
        (∀ u v : Fin n, G.Adj u v → ∃ S ∈ P, u ∈ S ∧ v ∈ S) ∧
        (∀ S₁ ∈ P, ∀ S₂ ∈ P, S₁ ≠ S₂ →
          ∀ u v : Fin n, u ∈ S₁ → v ∈ S₁ → u ∈ S₂ → v ∈ S₂ → ¬G.Adj u v) ∧
        (P.card : ℝ) ≤ (1 / 4 - ε) * (n : ℝ) ^ 2 :=
  sorry

/--
Erdős Problem #81, split graph variant (page-confirmed known result, [CEO94]):
Chen, Erdős, and Ordman proved that the edges of any split graph on n vertices
can be partitioned into at most (3/16)n² + O(n) many cliques. (Every split
graph is chordal, so this improves the n²/4 regime of [EOZ93] on a subclass;
here the additive C·n slack absorbs all small-n boundary cases.)
-/
theorem erdos_problem_81.variants.split_graph :
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      IsSplitGraph G →
      ∃ P : Finset (Finset (Fin n)),
        (∀ S ∈ P, G.IsClique (↑S : Set (Fin n))) ∧
        (∀ u v : Fin n, G.Adj u v → ∃ S ∈ P, u ∈ S ∧ v ∈ S) ∧
        (∀ S₁ ∈ P, ∀ S₂ ∈ P, S₁ ≠ S₂ →
          ∀ u v : Fin n, u ∈ S₁ → v ∈ S₁ → u ∈ S₂ → v ∈ S₂ → ¬G.Adj u v) ∧
        (P.card : ℝ) ≤ 3 / 16 * (n : ℝ) ^ 2 + C * (n : ℝ) :=
  sorry

/--
Erdős Problem #81, lower bound (page-confirmed known result, [EOZ93]):
the example of all edges between a complete graph on n/3 vertices and an
empty graph on 2n/3 vertices shows that n²/6 + O(n) is sometimes necessary.

Formalized as: there is a constant C such that for infinitely many n there is
a chordal graph G on n vertices every edge-clique-partition of which has at
least n²/6 − C·n parts (i.e. the leading term n²/6 in the problem's bound
cannot be improved).
-/
theorem erdos_problem_81.variants.lower_bound :
    ∃ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    ∃ G : SimpleGraph (Fin n),
      IsChordal G ∧
      ∀ P : Finset (Finset (Fin n)),
        (∀ S ∈ P, G.IsClique (↑S : Set (Fin n))) →
        (∀ u v : Fin n, G.Adj u v → ∃ S ∈ P, u ∈ S ∧ v ∈ S) →
        (∀ S₁ ∈ P, ∀ S₂ ∈ P, S₁ ≠ S₂ →
          ∀ u v : Fin n, u ∈ S₁ → v ∈ S₁ → u ∈ S₂ → v ∈ S₂ → ¬G.Adj u v) →
        (n : ℝ) ^ 2 / 6 - C * (n : ℝ) ≤ (P.card : ℝ) :=
  sorry
