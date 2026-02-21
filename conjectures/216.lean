import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Topology.Basic

open Set

/-- A point in the Euclidean plane ℝ². -/
abbrev Point216 := EuclideanSpace ℝ (Fin 2)

/--
A finite set of points in ℝ² is in general position if no three distinct
points are collinear (i.e., for any three distinct points, the third does
not lie on the affine line through the other two).
-/
def InGeneralPosition (S : Finset Point216) : Prop :=
  ∀ p₁ ∈ S, ∀ p₂ ∈ S, ∀ p₃ ∈ S,
    p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
    p₃ ∉ (affineSpan ℝ ({p₁, p₂} : Set Point216) : Set Point216)

/--
A finite set of points is in convex position if no point lies in the
convex hull of the remaining points.
-/
def InConvexPosition (S : Finset Point216) : Prop :=
  ∀ p ∈ S, p ∉ convexHull ℝ (↑(S.erase p) : Set Point216)

/--
A point set S contains an empty convex k-gon if there exists a subset T ⊆ S
of exactly k points such that:
1. T is in convex position (the k points form the vertices of a convex polygon), and
2. no other point of S lies in the interior of the convex hull of T.
-/
def HasEmptyConvexKGon (S : Finset Point216) (k : ℕ) : Prop :=
  ∃ T : Finset Point216, T ⊆ S ∧ T.card = k ∧
    InConvexPosition T ∧
    ∀ p ∈ S, p ∉ T → p ∉ interior (convexHull ℝ (↑T : Set Point216))

/--
Erdős Problem #216 (Empty Convex Polygon Problem):

Let g(k) be the smallest integer N (if it exists) such that any set of N
points in general position in ℝ² contains an empty convex k-gon (a convex
k-gon with no point of the set in its interior). The conjecture asks whether
g(k) exists for all k ≥ 3.

Known results:
- g(3) = 3 (trivial) and g(4) = 5 (Erdős).
- g(5) = 10 (Harborth [Ha78]).
- g(6) exists (Nicolás [Ni07], Gerken [Ge08]), and g(6) = 30
  (Heule–Scheucher [HeSc24]).
- DISPROVED for k ≥ 7: Horton [Ho83] constructed arbitrarily large point
  sets in general position with no empty convex 7-gon, so g(k) does not
  exist for k ≥ 7.
-/
theorem erdos_problem_216 :
    ∀ k : ℕ, 3 ≤ k →
      ∃ N : ℕ, ∀ (S : Finset Point216),
        InGeneralPosition S → N ≤ S.card →
        HasEmptyConvexKGon S k :=
  sorry
