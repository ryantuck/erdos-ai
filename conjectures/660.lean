import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# Erdős Problem #660

Let x₁, ..., xₙ ∈ ℝ³ be the vertices of a convex polyhedron. Are there at
least (1-o(1))n/2 many distinct distances between the xᵢ?

For the similar problem in ℝ² there are always at least n/2 distances,
as proved by Altman [Al63] (see [93]).

Tags: geometry | distances | convex
-/

/-- Points in ℝ³ are in convex position if every point is a vertex of the
    convex hull, i.e., no point lies in the convex hull of the remaining points. -/
def InConvexPosition3d (P : Finset (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ p ∈ P, p ∉ convexHull ℝ (↑(P.erase p) : Set (EuclideanSpace ℝ (Fin 3)))

/-- The number of distinct pairwise distances determined by a finite point set in ℝ³. -/
noncomputable def distinctDistanceCount3d (P : Finset (EuclideanSpace ℝ (Fin 3))) : ℕ :=
  Set.ncard {d : ℝ | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ d = dist p q}

/--
**Erdős Problem #660** [Er97e, p.531]:

Let x₁, ..., xₙ ∈ ℝ³ be the vertices of a convex polyhedron. Then the number
of distinct distances determined by these points is at least (1 - o(1)) · n/2,
i.e., for every ε > 0 there exists N such that for all n ≥ N, the number of
distinct distances is at least (1 - ε) · n/2.
-/
theorem erdos_problem_660 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset (EuclideanSpace ℝ (Fin 3)),
          P.card = n →
          InConvexPosition3d P →
          (distinctDistanceCount3d P : ℝ) ≥ (1 - ε) * (n : ℝ) / 2 :=
  sorry
