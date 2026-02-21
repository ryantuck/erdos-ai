import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Archimedean

/-!
# Erdős Problem #465

Let N(X,δ) denote the maximum number of points P₁,...,Pₙ which can be chosen
in a disk of radius X in ℝ² such that ‖|Pᵢ-Pⱼ|‖ ≥ δ for all 1 ≤ i < j ≤ n,
where ‖x‖ denotes the distance from x to the nearest integer.

Two conjectures (both proved):
1. (Weak, Sárközy [Sa76]) For any 0 < δ < 1/2, N(X,δ) = o(X).
   Sárközy showed N(X,δ) ≪ δ⁻³ X/(log log X).
2. (Strong, Konyagin [Ko01]) For any fixed δ > 0, N(X,δ) ≪_δ X^{1/2}.
-/

/-- The distance of a real number from the nearest integer. -/
noncomputable def distNearestInt465 (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/--
Erdős Problem #465, weak form (Proved by Sárközy [Sa76]):

For any 0 < δ < 1/2, N(X,δ) = o(X). Formalized as: for any ε > 0, for
sufficiently large X, any finite set of points in a closed disk of radius X
in ℝ² with all pairwise distances satisfying ‖d‖ ≥ δ has at most ε·X points.
-/
theorem erdos_problem_465_weak (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1 / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
    ∀ (X : ℝ), X₀ ≤ X →
    ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ A, dist p 0 ≤ X) →
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → distNearestInt465 (dist p q) ≥ δ) →
      (A.card : ℝ) ≤ ε * X :=
  sorry

/--
Erdős Problem #465, strong form (Proved by Konyagin [Ko01]):

For any fixed δ > 0, N(X,δ) ≪_δ X^{1/2}. Formalized as: there exists C > 0
(depending on δ) such that any finite set of points in a closed disk of radius X
in ℝ² with all pairwise distances satisfying ‖d‖ ≥ δ has at most C·√X points.
-/
theorem erdos_problem_465_strong (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (X : ℝ), 0 < X →
    ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ A, dist p 0 ≤ X) →
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → distNearestInt465 (dist p q) ≥ δ) →
      (A.card : ℝ) ≤ C * Real.sqrt X :=
  sorry
