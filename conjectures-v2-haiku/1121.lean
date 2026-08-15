import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

noncomputable section
open scoped BigOperators
open Classical

namespace Erdos1121

/--
Erdős Problem #1121 (proved by Goodman and Goodman [GoGo45]):

If C₁, ..., Cₙ are circles in ℝ² with radii r₁, ..., rₙ such that no line
disjoint from all the circles divides them into two non-empty sets, then the
circles can be covered by a circle of radius r = ∑ rᵢ.

A line in ℝ² is parameterized by a unit normal vector v and offset d, defining
ℓ = {x : ⟨x, v⟩ = d}. The closed disk B̄(cᵢ, rᵢ) is disjoint from ℓ when
|⟨cᵢ, v⟩ − d| > rᵢ. The non-separability condition says that whenever all
disks are disjoint from a line, they all lie on the same side.

The Goodman–Goodman proof generalizes to ℝᵈ: circles become balls, lines become
hyperplanes, and the same non-separability and covering radius conditions hold.

## Bibliography

[GoGo45] Goodman, A. W. and Goodman, R. E., *A circle covering theorem*.
         American Mathematical Monthly 52 (1945), pp. 494–498.
-/
theorem erdos_problem_1121
    (n : ℕ)
    (center : Fin n → EuclideanSpace ℝ (Fin 2))
    (radius : Fin n → ℝ)
    (hr : ∀ i, 0 < radius i)
    (hns : ∀ (v : EuclideanSpace ℝ (Fin 2)) (d : ℝ),
      ‖v‖ = 1 →
      (∀ i, |@inner ℝ _ _ (center i) v - d| > radius i) →
      (∀ i j, @inner ℝ _ _ (center i) v > d ↔ @inner ℝ _ _ (center j) v > d)) :
    ∃ p : EuclideanSpace ℝ (Fin 2),
      ∀ i, dist (center i) p + radius i ≤ ∑ j : Fin n, radius j :=
  sorry

end Erdos1121
