import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-- Four points in ℝ² are concyclic if they all lie on a common circle. -/
def Concyclic213 (a b c d : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ (center : EuclideanSpace ℝ (Fin 2)) (radius : ℝ),
    0 < radius ∧
    dist a center = radius ∧
    dist b center = radius ∧
    dist c center = radius ∧
    dist d center = radius

/-- A finite set of points in ℝ² is in Erdős general position: no three collinear,
    no four concyclic. -/
def ErdosGeneralPosition213 (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (∀ p q r : EuclideanSpace ℝ (Fin 2),
    p ∈ S → q ∈ S → r ∈ S →
    p ≠ q → p ≠ r → q ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
  (∀ p q r s : EuclideanSpace ℝ (Fin 2),
    p ∈ S → q ∈ S → r ∈ S → s ∈ S →
    p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
    ¬Concyclic213 p q r s)

/-- All pairwise distances in a finite set are integers. -/
def AllPairwiseDistancesInteger (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ n : ℤ, dist p q = (n : ℝ)

/--
Erdős Problem #213 [Er75f, Er83c, Er87b]:

Let n ≥ 4. Are there n points in ℝ², no three on a line and no four on a circle,
such that all pairwise distances are integers?

This conjecture asserts that for every n ≥ 4, such a configuration exists.
The best construction known is due to Kreisel and Kurz (2008) with n = 7.
Anning and Erdős proved that no infinite such set exists.
-/
theorem erdos_problem_213 :
    ∀ n : ℕ, 4 ≤ n →
      ∃ S : Finset (EuclideanSpace ℝ (Fin 2)),
        S.card = n ∧
        ErdosGeneralPosition213 S ∧
        AllPairwiseDistancesInteger S :=
  sorry
