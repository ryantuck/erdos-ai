import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Archimedean

/-!
# Erdős Problem #466

Let N(X,δ) denote the maximum number of points P₁,...,Pₙ which can be chosen
in a disk of radius X in ℝ² such that ‖|Pᵢ-Pⱼ|‖ ≥ δ for all 1 ≤ i < j ≤ n,
where ‖x‖ denotes the distance from x to the nearest integer.

Is there some δ > 0 such that lim_{X→∞} N(X,δ) = ∞?

This was proved by Graham, who showed N(X, 1/10) > (log X)/10.
-/

/-- The distance of a real number from the nearest integer. -/
noncomputable def distNearestInt466 (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/--
Erdős Problem #466 (Proved by Graham):

There exists δ > 0 such that N(X,δ) → ∞ as X → ∞. Formalized as:
there exists δ > 0 such that for every M, for sufficiently large X,
one can find at least M points in a disk of radius X in ℝ² whose
pairwise distances all satisfy ‖d‖ ≥ δ.
-/
theorem erdos_problem_466 :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ M : ℕ, ∃ X₀ : ℝ, 0 < X₀ ∧
    ∀ (X : ℝ), X₀ ≤ X →
    ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      M ≤ A.card ∧
      (∀ p ∈ A, dist p 0 ≤ X) ∧
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → distNearestInt466 (dist p q) ≥ δ) :=
  sorry
