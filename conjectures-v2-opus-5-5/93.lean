-- [AI - Claude Opus 5.5]: Erdős Problem 93 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic

noncomputable section

open scoped Classical

/-!
# Erdős Problem #93

*Source:* [erdosproblems.com/93](https://www.erdosproblems.com/93) (status **PROVED (LEAN)**:
"This has been solved in the affirmative and the proof verified in Lean."; page last edited
19 October 2025, captured 2026-02-22). [Er46b] [Er57] [Er61] [Er75f, p.100] [Er82e]
[Er87b, p.175] [Er90] [Er92e] [Er95] [Er97e] [Er97f]

If $n$ distinct points in $\mathbb{R}^2$ form a convex polygon then they determine at least
$\lfloor n/2 \rfloor$ distinct distances.

Remarks recorded on the page:
* Solved by Altman [Al63].
* The stronger variant asking for one point that determines at least $\lfloor n/2 \rfloor$
  distinct distances (Problem #982) is still open.
* Fishburn conjectures that, if $R(x)$ counts the distinct distances from $x$, then
  $\sum_{x \in A} R(x) \ge \binom{n}{2}$.
* Szemerédi conjectured a stronger form in which convexity is replaced by the assumption
  that no three points are on a line (Problem #1082). See also Problem #660.

"Form a convex polygon" is encoded as `InConvexPosition` (no point lies in the convex hull of
the others), the standard meaning. For $n \ge 3$ these are exactly the vertex sets of
strictly convex $n$-gons. The bound is attained by the regular $n$-gon.

Tags: geometry, convex, distances.

## References

* [Er46b] Erdős, P., _On sets of distances of $n$ points_. Amer. Math. Monthly (1946),
  248–250.
* [Er57] Erdős, P., _Some unsolved problems_. Michigan Math. J. (1957), 291–300.
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl.
  (1961), 221–254.
* [Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_. Ann. Mat.
  Pura Appl. (4) (1975), 99–108.
* [Er82e] Erdős, P., _Some of my favourite problems which recently have been solved_.
  (1982), 59–79.
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
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.
* [Al63] Altman, E., _On a problem of P. Erdős_. Amer. Math. Monthly (1963), 148–157.

(Provenance: the reference block of upstream formal-conjectures
`FormalConjectures/ErdosProblems/93.lean` at `df3f12d`. [Er75f], [Er87b], [Er90], [Er95] and
[Er97e] agree with the original pipeline's `/latex` extractions for sibling problems.)
-/

/--
A finite set of points in ℝ² is in convex position if no point lies in the
convex hull of the remaining points. Equivalently, the points are the vertices
of a convex polygon.
-/
def InConvexPosition (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ A, p ∉ convexHull ℝ ((↑A : Set (EuclideanSpace ℝ (Fin 2))) \ {p})

/--
The set of distinct pairwise distances between distinct points in a finite
point set in ℝ².
-/
def distinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  A.offDiag.image (fun pq => dist pq.1 pq.2)

/--
Erdős Problem #93 (PROVED):
If n distinct points in ℝ² form a convex polygon, then they determine at least
⌊n/2⌋ distinct distances. Proved by Altman [Al63].
-/
theorem erdos_problem_93
    (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hconv : InConvexPosition A)
    (hn : 2 ≤ A.card) :
    A.card / 2 ≤ (distinctDistances A).card :=
  sorry

/--
The distinct distances from the point `x` to the other points of `A`.
-/
def distinctDistancesFrom (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) : Finset ℝ :=
  (A.erase x).image (fun y => dist x y)

/--
The stronger one-point form (OPEN; this is Problem #982): some point of a convex polygon
has at least ⌊n/2⌋ distinct distances to the other vertices.
-/
theorem erdos_problem_93.variants.one_point
    (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hconv : InConvexPosition A)
    (hn : 2 ≤ A.card) :
    ∃ x ∈ A, A.card / 2 ≤ (distinctDistancesFrom A x).card :=
  sorry

/--
Fishburn's conjecture (OPEN): for a convex polygon, the numbers $R(x)$ of distinct distances
from each vertex satisfy $\sum_{x \in A} R(x) \ge \binom{n}{2}$. Averaging shows it implies
`erdos_problem_93.variants.one_point`, since some $R(x) \ge \lceil (n-1)/2 \rceil =
\lfloor n/2 \rfloor$.
-/
theorem erdos_problem_93.variants.fishburn
    (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hconv : InConvexPosition A) :
    A.card.choose 2 ≤ ∑ x ∈ A, (distinctDistancesFrom A x).card :=
  sorry
