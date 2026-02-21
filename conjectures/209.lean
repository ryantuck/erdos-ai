import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Finset.Basic

noncomputable section
open Classical

/-- Points in the Euclidean plane ℝ² -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

/-- An affine subspace of ℝ² is a line if it has dimension 1 -/
def IsLine (L : AffineSubspace ℝ Point2) : Prop :=
  Module.finrank ℝ L.direction = 1

/-- Two affine subspaces are parallel if they have the same direction -/
def AreParallel (L₁ L₂ : AffineSubspace ℝ Point2) : Prop :=
  L₁.direction = L₂.direction

/-- The number of lines from A passing through a point p -/
def pointMultiplicity (A : Finset (AffineSubspace ℝ Point2)) (p : Point2) : ℕ :=
  (A.filter (fun L => (p : Point2) ∈ L)).card

/-- A point is ordinary if exactly 2 lines from A pass through it -/
def IsOrdinaryPoint (A : Finset (AffineSubspace ℝ Point2)) (p : Point2) : Prop :=
  pointMultiplicity A p = 2

/-- A Gallai (ordinary) triangle: three lines forming a triangle with
    all three vertices being ordinary points -/
def HasGallaiTriangle (A : Finset (AffineSubspace ℝ Point2)) : Prop :=
  ∃ L₁ ∈ A, ∃ L₂ ∈ A, ∃ L₃ ∈ A,
    L₁ ≠ L₂ ∧ L₂ ≠ L₃ ∧ L₁ ≠ L₃ ∧
    ∃ p₁₂ p₂₃ p₁₃ : Point2,
      (p₁₂ : Point2) ∈ L₁ ∧ (p₁₂ : Point2) ∈ L₂ ∧
      (p₂₃ : Point2) ∈ L₂ ∧ (p₂₃ : Point2) ∈ L₃ ∧
      (p₁₃ : Point2) ∈ L₁ ∧ (p₁₃ : Point2) ∈ L₃ ∧
      p₁₂ ≠ p₂₃ ∧ p₂₃ ≠ p₁₃ ∧ p₁₂ ≠ p₁₃ ∧
      IsOrdinaryPoint A p₁₂ ∧ IsOrdinaryPoint A p₂₃ ∧ IsOrdinaryPoint A p₁₃

/--
Erdős Problem #209 (Disproved):
Let A be a finite collection of d ≥ 4 non-parallel lines in ℝ² such that no
point has 4 or more lines from A passing through it. The conjecture asked whether
there must exist a 'Gallai triangle' (ordinary triangle): three lines from A
which intersect in three points, each being an ordinary point (exactly two lines
from A meet there).

Disproved by Füredi-Palásti for d not divisible by 9, and by Escudero for all d ≥ 4.
-/
theorem erdos_problem_209 :
    ∀ d : ℕ, d ≥ 4 →
      ∃ A : Finset (AffineSubspace ℝ Point2),
        A.card = d ∧
        (∀ L ∈ A, IsLine L) ∧
        (∀ L₁ ∈ A, ∀ L₂ ∈ A, L₁ ≠ L₂ → ¬AreParallel L₁ L₂) ∧
        (∀ p : Point2, pointMultiplicity A p ≤ 3) ∧
        ¬HasGallaiTriangle A :=
  sorry
