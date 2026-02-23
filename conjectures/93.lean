import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic

noncomputable section

open scoped Classical

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
Erdős Problem #93:
If n distinct points in ℝ² form a convex polygon, then they determine at least
⌊n/2⌋ distinct distances. Proved by Altman [Al63].
-/
theorem erdos_problem_93
    (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hconv : InConvexPosition A)
    (hn : 2 ≤ A.card) :
    A.card / 2 ≤ (distinctDistances A).card :=
  sorry
