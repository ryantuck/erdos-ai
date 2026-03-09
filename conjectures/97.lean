import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

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
Erdős Problem #97 [Er46b, Er61, Er75f, Er87b, Er90, Er92e, Er95, Er97e]:

Does every convex polygon have a vertex with no other 4 vertices equidistant
from it? That is, for every finite set P of points in ℝ² in convex position,
there exists a vertex p ∈ P such that for every distance r > 0, the number of
other vertices at distance r from p is at most 3.

Erdős originally conjectured this with "3" in place of "4", but Danzer found a
convex 9-gon where every vertex has 3 other vertices equidistant from it.
The conjecture with "4" remains open and carries a $100 prize.
-/
theorem erdos_problem_97 :
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      ConvexPosition P →
      ∃ p ∈ P, ∀ (r : ℝ), (equidistantVertices P p r).card ≤ 3 := by
  sorry
