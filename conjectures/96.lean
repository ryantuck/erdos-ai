import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic

/--
A finite set of points in ℝ² is in convex position if no point lies in the
convex hull of the remaining points. Equivalently, the points are the vertices
of a convex polygon.
-/
def ConvexPosition (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ P, p ∉ convexHull ℝ (↑(P.erase p) : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of ordered pairs of distinct points in P that are at unit distance.
(Using ordered pairs; the number of unordered pairs is exactly half this,
so the O(n) bound is equivalent.)
-/
noncomputable def unitDistancePairCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card

/--
Erdős Problem #96 (Erdős–Moser conjecture):
If n points in ℝ² form a convex polygon (are in convex position), then there
are O(n) many pairs which are distance 1 apart.

Formally: there exists an absolute constant C > 0 such that for every finite
set P of points in ℝ² in convex position, the number of (ordered) pairs at
unit distance is at most C · |P|.
-/
theorem erdos_problem_96 :
    ∃ C : ℝ, C > 0 ∧
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      ConvexPosition P →
      (unitDistancePairCount P : ℝ) ≤ C * (P.card : ℝ) := by
  sorry
