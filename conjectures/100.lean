import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/--
A finite set of points in ℝ² has "1-separated distances" if:
1. All pairwise distances between distinct points are at least 1.
2. Any two distinct pairwise distance values differ by at least 1.
-/
def HasSeparatedDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (∀ p ∈ A, ∀ q ∈ A, p ≠ q → dist p q ≥ 1) ∧
  (∀ p₁ ∈ A, ∀ q₁ ∈ A, ∀ p₂ ∈ A, ∀ q₂ ∈ A,
    p₁ ≠ q₁ → p₂ ≠ q₂ → dist p₁ q₁ ≠ dist p₂ q₂ →
    |dist p₁ q₁ - dist p₂ q₂| ≥ 1)

/--
The diameter of a finite set of points in ℝ²: the supremum of all pairwise distances.
-/
noncomputable def finiteDiameter (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sSup {d : ℝ | ∃ p ∈ A, ∃ q ∈ A, d = dist p q}

/--
Erdős's conjecture (Problem #100):
If A is a set of n ≥ 2 points in ℝ² such that all pairwise distances are at
least 1 and any two distinct pairwise distances differ by at least 1, then the
diameter of A is ≫ n. That is, there exists an absolute constant c > 0 such
that diam(A) ≥ c * n for all such A.
-/
theorem erdos_problem_100 :
  ∃ c : ℝ, c > 0 ∧
  ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
    1 < A.card →
    HasSeparatedDistances A →
    finiteDiameter A ≥ c * (A.card : ℝ) :=
sorry
