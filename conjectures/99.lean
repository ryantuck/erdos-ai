import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open scoped NNReal

/--
The minimum pairwise distance of a finite set of points.
-/
noncomputable def minPairwiseDist {α : Type*} [Dist α] (A : Finset α) : ℝ :=
  (A.offDiag.image (fun p => dist p.1 p.2)).min'
    (by sorry) -- nonemptiness obligation, assumed for |A| ≥ 2

/--
The diameter of a finite set of points (maximum pairwise distance).
-/
noncomputable def diameter {α : Type*} [Dist α] (A : Finset α) : ℝ :=
  (A.offDiag.image (fun p => dist p.1 p.2)).max'
    (by sorry) -- nonemptiness obligation

/--
Three points form an equilateral triangle of side length s.
-/
def IsEquilateralTriangle (a b c : EuclideanSpace ℝ (Fin 2)) (s : ℝ) : Prop :=
  dist a b = s ∧ dist b c = s ∧ dist a c = s

/--
A finite set A achieves the minimum diameter among all n-point subsets of ℝ²
with minimum pairwise distance at least 1.
-/
def MinimisesDiameter (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  minPairwiseDist A ≥ 1 ∧
  ∀ B : Finset (EuclideanSpace ℝ (Fin 2)),
    B.card = A.card →
    minPairwiseDist B ≥ 1 →
    diameter A ≤ diameter B

/--
Erdős Problem #99 [Er94b, Er95, Er97e]:

Let A ⊆ ℝ² be a set of n points with minimum distance equal to 1, chosen to
minimise the diameter of A. If n is sufficiently large then must there be three
points in A which form an equilateral triangle of side length 1?

Thue proved that the minimal diameter is achieved (asymptotically) by points in
a triangular lattice intersected with a circle. Erdős believed such a set must
have very large intersection with the triangular lattice.

The conjecture is false for small n (e.g., n = 4 with square vertices).
-/
theorem erdos_problem_99 :
    ∃ N₀ : ℕ, ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      A.card ≥ N₀ →
      MinimisesDiameter A →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
        a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
        IsEquilateralTriangle a b c 1 :=
  sorry
