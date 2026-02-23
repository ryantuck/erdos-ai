import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/--
A finite set of points in ℝ² is in convex position if no point lies in
the convex hull of the remaining points. Equivalently, all points are
vertices of their convex hull (they form a convex polygon).
-/
def ConvexPosition (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ A, p ∉ convexHull ℝ ((A : Set (EuclideanSpace ℝ (Fin 2))) \ {p})

/--
The count of ordered quadruples (a, b, c, d) from A with a ≠ b, c ≠ d,
and dist(a, b) = dist(c, d). This equals 4 · ∑ᵢ f(uᵢ)² where f(uᵢ)
counts unordered pairs at distance uᵢ.
-/
noncomputable def distSqSum (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  let E := EuclideanSpace ℝ (Fin 2)
  Set.ncard {x : E × E × E × E |
    x.1 ∈ (A : Set E) ∧ x.2.1 ∈ (A : Set E) ∧
    x.2.2.1 ∈ (A : Set E) ∧ x.2.2.2 ∈ (A : Set E) ∧
    x.1 ≠ x.2.1 ∧ x.2.2.1 ≠ x.2.2.2 ∧
    dist x.1 x.2.1 = dist x.2.2.1 x.2.2.2}

/--
Erdős Problem #94:
Suppose n points in ℝ² are in convex position (they form the vertices of
a convex polygon). Let {u₁, ..., uₜ} be the set of distinct pairwise
distances, and let f(uᵢ) denote the number of pairs at distance uᵢ. Then
  ∑ᵢ f(uᵢ)² ≪ n³.

This was proved by Lefmann and Theile [LeTh95] under the weaker
assumption that no three points are collinear.
-/
theorem erdos_problem_94 :
    ∃ C : ℝ, C > 0 ∧
    ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
      ConvexPosition A →
      (distSqSum A : ℝ) ≤ C * (A.card : ℝ) ^ 3 :=
  sorry
