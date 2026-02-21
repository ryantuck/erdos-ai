import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Finset.Basic

noncomputable section

/--
The angle at point y determined by three points x, y, z in ℝ²:
the angle between vectors (x - y) and (z - y), computed as
arccos of their normalized inner product. Returns a value in [0, π].
-/
def angleAt (x y z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  let u := x - y
  let v := z - y
  Real.arccos (@inner ℝ _ _ u v / (‖u‖ * ‖v‖))

/--
α_N: the maximum guaranteed angle for N-point planar sets.
The supremum of all α ∈ [0, π] such that every set of N points in ℝ²
contains three distinct points x, y, z with angle at y at least α.
-/
def maxGuaranteedAngle (N : ℕ) : ℝ :=
  sSup {α : ℝ | 0 ≤ α ∧ α ≤ Real.pi ∧
    ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      A.card = N →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
        angleAt x y z ≥ α}

/--
Erdős Problem #504 (Blumenthal's problem, solved by Sendov):

Let α_N be the supremum of all 0 ≤ α ≤ π such that in every set A ⊂ ℝ²
of size N there exist three distinct points x, y, z ∈ A such that the
angle at y (between rays yx and yz) is at least α. Determine α_N.

Sendov (1993) proved that for n ≥ 3 and 2^(n-1) < N ≤ 2^n:
  α_N = π(1 - 1/n)       when N > 2^(n-1) + 2^(n-3)
  α_N = π(1 - 1/(2n-1))  when N ≤ 2^(n-1) + 2^(n-3)
-/
theorem erdos_problem_504 (N : ℕ) (hN : 4 < N) (n : ℕ) (hn : 3 ≤ n)
    (hn_lb : 2 ^ (n - 1) < N) (hn_ub : N ≤ 2 ^ n) :
    maxGuaranteedAngle N =
      if 2 ^ (n - 1) + 2 ^ (n - 3) < N
      then Real.pi * (1 - 1 / (n : ℝ))
      else Real.pi * (1 - 1 / (2 * (n : ℝ) - 1)) :=
  sorry
