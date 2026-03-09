import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic

/--
A finite set of points in ℝ² is in convex position if no point lies in the
convex hull of the remaining points.
-/
def ConvexPosition (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ P, p ∉ convexHull ℝ (↑(P.erase p) : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of distinct distances from a point p to the other points in P.
-/
noncomputable def numDistinctDistances
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  ((P.erase p).image (fun q => dist p q)).card

/--
Erdős Problem #982 [Er46b, Er75f, Er87b, ErFi94]:

If n distinct points in ℝ² form a convex polygon then some vertex has at least
⌊n/2⌋ different distances to other vertices.

The regular polygon shows that ⌊n/2⌋ is the best possible.
-/
theorem erdos_problem_982 :
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      ConvexPosition P →
      ∃ p ∈ P, P.card / 2 ≤ numDistinctDistances P p := by
  sorry
