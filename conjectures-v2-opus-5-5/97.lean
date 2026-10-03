-- [AI - Claude Opus 5.5]: Erdős Problem 97 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #97

*Source:* [erdosproblems.com/97](https://www.erdosproblems.com/97) (status **FALSIFIABLE**,
\$100: "Open, but could be disproved with a finite counterexample."; page last edited
27 October 2025, captured 2026-03-05). [Er46b] [Er61] [Er75f, p.100] [Er87b, p.175] [Er90]
[Er92e] [Er95] [Er97e]

Does every convex polygon have a vertex with no other $4$ vertices equidistant from it?

Remarks recorded on the page:
* Erdős originally conjectured this in [Er46b] with no $3$ vertices equidistant. Danzer found
  a convex polygon on 9 points in which every vertex has three vertices equidistant from it,
  the distance depending on the vertex. Danzer's construction is explained in [Er87b].
  Fishburn and Reeds [FiRe92] found a convex polygon on 20 points in which every vertex has
  three vertices equidistant from it, with the same distance for all vertices.
* If this fails for $4$, perhaps there is some constant for which it holds? In [Er75f]
  Erdős claimed that Danzer proved it false for every constant. Since the claim was not
  repeated later, presumably Erdős was mistaken.
* Erdős suggested this as an approach to Problem #96: if this problem holds for $k + 1$
  vertices then, by induction, it implies an upper bound of $kn$ for #96.
* The answer is no without convexity (pointed out to the site by Boris Alexeev and Dustin
  Mixon). For any $d$ there are graphs of minimum degree $d$ embedded in the plane with all
  edges of length one, e.g. the $d$-dimensional hypercube graph.

The polygon is encoded by its vertex set in convex position. "No other 4 vertices
equidistant from p" means that for every radius $r$ at most 3 other vertices lie at
distance $r$ from $p$.

Tags: geometry, distances, convex.

## References

* [Er46b] Erdős, P., _On sets of distances of $n$ points_. Amer. Math. Monthly (1946),
  248–250.
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl.
  (1961), 221–254.
* [Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_. Ann. Mat.
  Pura Appl. (4) (1975), 99–108.
* [Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_. Intuitive
  geometry (Siófok, 1985) (1987), 167–177.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős
  (1990), 467–478.
* [Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
  Eureka (1992), 44–48.
* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997),
  527–537.
* [FiRe92] Fishburn, P. C. and Reeds, J. A., _Unit distances between vertices of a convex
  polygon_. Comput. Geom. (1992), 81–91.

(Provenance: the eight Erdős keys come from the original pipeline's `/latex` extractions for
sibling problems (91, 93, 94, 1088/1090 and others). They agree with upstream
formal-conjectures at `df3f12d`. [FiRe92] comes from upstream `ErdosProblems/97.lean` only.)
-/

/--
A finite set of points in ℝ² is in convex position if no point lies in the
convex hull of the remaining points. Equivalently, the points are the vertices
of a convex polygon.
-/
def ConvexPosition (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ P, p ∉ convexHull ℝ (↑(P.erase p) : Set (EuclideanSpace ℝ (Fin 2)))

/--
The set of other vertices in P that are at a given distance r from a point p.
-/
noncomputable def equidistantVertices
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2))
    (r : ℝ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  (P.erase p).filter (fun q => dist p q = r)

/--
Erdős Problem #97 [Er46b, Er61, Er75f, Er87b, Er90, Er92e, Er95, Er97e] (FALSIFIABLE, \$100):

Does every convex polygon have a vertex with no other 4 vertices equidistant
from it? That is, for every nonempty finite set P of points in ℝ² in convex position,
there exists a vertex p ∈ P such that for every distance r, the number of
other vertices at distance r from p is at most 3.

The hypothesis `P.Nonempty` is necessary. The empty set is vacuously in convex position and
has no vertex, so without it the statement is false at `P = ∅`. One- and two-point sets
satisfy the conclusion trivially.

Erdős originally conjectured this with "3" in place of "4", but Danzer found a
convex 9-gon where every vertex has 3 other vertices equidistant from it.
The conjecture with "4" remains open and carries a $100 prize.
-/
theorem erdos_problem_97 :
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      P.Nonempty →
      ConvexPosition P →
      ∃ p ∈ P, ∀ (r : ℝ), (equidistantVertices P p r).card ≤ 3 := by
  sorry

/--
Danzer (PROVED; see [Er87b]): the "3" version fails. There is a convex 9-gon in which every
vertex has 3 other vertices at a common distance from it, the distance depending on the
vertex. Upstream formal-conjectures records explicit coordinates:
$(\mp\sqrt3,-1)$, $(0,2)$,
$(-\tfrac{8991}{10927}\sqrt3,-\tfrac{26503}{10927})$,
$(\tfrac{17747}{10927}\sqrt3,-\tfrac{235}{10927})$,
$(-\tfrac{8756}{10927}\sqrt3,\tfrac{26738}{10927})$,
$(-\tfrac{10753}{18529}\sqrt3,-\tfrac{44665}{18529})$,
$(\tfrac{27709}{18529}\sqrt3,\tfrac{6203}{18529})$,
$(-\tfrac{16956}{18529}\sqrt3,\tfrac{38462}{18529})$.
-/
theorem erdos_problem_97.variants.danzer :
    ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = 9 ∧ ConvexPosition P ∧
      ∀ p ∈ P, ∃ r : ℝ, 3 ≤ (equidistantVertices P p r).card := by
  sorry

/--
Fishburn and Reeds [FiRe92] (PROVED): there is a convex 20-gon in which every vertex has 3
other vertices at the same distance, scaled to 1, for all vertices.
-/
theorem erdos_problem_97.variants.fishburn_reeds :
    ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = 20 ∧ ConvexPosition P ∧
      ∀ p ∈ P, 3 ≤ (equidistantVertices P p 1).card := by
  sorry

/--
"Perhaps there is some constant for which it holds?" (OPEN): there is a `k` such that every
nonempty convex polygon has a vertex with fewer than `k` other vertices at any single
distance. The main problem is the case `k = 4`.
-/
theorem erdos_problem_97.variants.some_constant :
    ∃ k : ℕ, ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      P.Nonempty → ConvexPosition P →
      ∃ p ∈ P, ∀ (r : ℝ), (equidistantVertices P p r).card < k := by
  sorry

/--
Convexity is essential (PROVED; Alexeev–Mixon, via unit-distance embeddings such as the
hypercube graph). For every `k` there is a nonempty finite point set in which every point has
at least `k` other points at distance 1. This is the point-set core of the page's remark; the
cyclic ordering into a non-self-intersecting polygon is not encoded.
-/
theorem erdos_problem_97.variants.nonconvex :
    ∀ k : ℕ, ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.Nonempty ∧ ∀ p ∈ P, k ≤ (equidistantVertices P p 1).card := by
  sorry

/--
The reduction to Problem #96 (PROVED, by induction). If every nonempty convex polygon has a
vertex with at most `k` other vertices at each distance, then every convex polygon has at
most `k n` unit-distance pairs, i.e. at most `2 k n` ordered ones. Remove such a vertex and
recurse; subsets of a set in convex position are in convex position.
-/
theorem erdos_problem_97.variants.implies_linear_unit_distances (k : ℕ)
    (h : ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      P.Nonempty → ConvexPosition P →
      ∃ p ∈ P, ∀ (r : ℝ), (equidistantVertices P p r).card ≤ k) :
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      ConvexPosition P →
      (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card ≤ 2 * k * P.card := by
  sorry
