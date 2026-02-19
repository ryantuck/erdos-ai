import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/--
The number of distinct unit circles in ℝ² that contain at least three points
from P. A unit circle is uniquely determined by its center (since the radius
is fixed at 1), so two unit circles are distinct iff they have different centers.
-/
noncomputable def threeRichUnitCircleCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {c : EuclideanSpace ℝ (Fin 2) |
    3 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ dist p c = 1}}

/--
Erdős Problem #104:
Given n points in ℝ², the number of distinct unit circles containing at least
three points is o(n²).

Formally: for every ε > 0 there exists N such that for all n ≥ N and every
set P of n points in ℝ², the number of unit circles (of radius 1) that each
contain at least 3 points of P is at most ε · n².
-/
theorem erdos_problem_104 :
  ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        (threeRichUnitCircleCount P : ℝ) ≤ ε * (n : ℝ) ^ 2 :=
  sorry
