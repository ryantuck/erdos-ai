import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Classical

/-!
# Erdős Problem #657

Is it true that if A ⊆ ℝ² is a set of n points such that every subset of
3 points determines 3 distinct distances (i.e. A has no isosceles triangles)
then A must determine at least f(n)·n distinct distances, for some f(n) → ∞?

A problem of Erdős and Davies [Er73, Er75f, ErPa90, Er97e].

Tags: geometry | distances
-/

/-- The number of distinct pairwise distances in a finite point set A ⊆ ℝ². -/
noncomputable def Erdos657.numDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2)).card

/-- A finite point set A ⊆ ℝ² has no isosceles triangles if every 3-element
    subset determines 3 distinct pairwise distances. -/
def Erdos657.NoIsoscelesTriangles (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ A → S.card = 3 → Erdos657.numDistances S = 3

/--
**Erdős Problem #657** [Er73, Er75f, ErPa90, Er97e]:

Let A ⊆ ℝ² be a set of n points such that every 3-point subset determines
3 distinct distances (no isosceles triangles). Must the number of distinct
distances determined by A be at least f(n)·n for some f(n) → ∞?

Equivalently: for every constant C > 0, there exists N₀ such that every
set of n ≥ N₀ points in ℝ² with no isosceles triangles determines at least
C·n distinct distances.
-/
theorem erdos_problem_657 :
    ∀ C : ℝ, 0 < C →
      ∃ N₀ : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
        Erdos657.NoIsoscelesTriangles A →
        N₀ ≤ A.card →
        C * (A.card : ℝ) ≤ (Erdos657.numDistances A : ℝ) :=
  sorry
