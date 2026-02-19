import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/--
A finite point set in ℝ² has no five collinear if every five-element subset
is not collinear (i.e., no line contains five or more of the points).
-/
def NoFiveCollinear (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 5 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of 4-rich lines: the number of distinct affine lines in ℝ² that
contain at least four points from P.

An affine line is a 1-dimensional affine subspace (Module.finrank of its
direction submodule equals 1).
-/
noncomputable def fourRichLineCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    4 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}}

/--
Erdős Problem #101:
Given n points in ℝ², no five of which are collinear, the number of lines
containing at least four of the points is o(n²).

Formally: for every ε > 0 there exists N such that for all n ≥ N and every
set P of n points in ℝ² with no five collinear, the count of 4-rich lines
is at most ε · n².
-/
theorem erdos_problem_101 :
  ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        NoFiveCollinear P →
        (fourRichLineCount P : ℝ) ≤ ε * (n : ℝ) ^ 2 :=
  sorry
