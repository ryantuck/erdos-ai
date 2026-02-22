import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open Classical

noncomputable section

/-!
# Erdős Problem #755

The number of equilateral triangles of size 1 formed by any set of n points
in ℝ⁶ is at most (1/27 + o(1))n³.

A problem of Erdős and Purdy [ErPu75]. Erdős believed the bound should hold
even for equilateral triangles of any size. This was proved in a strong form
by Clemen, Dumitrescu, and Liu [CDL25b].
-/

/-- The number of unit equilateral triangles determined by a finite point set
    in d-dimensional Euclidean space: the number of 3-element subsets where
    all pairwise distances are 1. -/
noncomputable def unitEquilateralTriangleCount {d : ℕ}
    (A : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  Set.ncard {T : Finset (EuclideanSpace ℝ (Fin d)) |
    T ⊆ A ∧ T.card = 3 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → dist x y = 1}

/--
Erdős Problem #755 [ErPu75][Er94b]:

The number of unit equilateral triangles determined by n points in ℝ⁶ is
at most (1/27 + o(1))n³.

Formulated as: for every ε > 0, there exists N₀ such that for all n ≥ N₀
and every set of n points in ℝ⁶, the number of unit equilateral triangles
is at most (1/27 + ε) · n³.
-/
theorem erdos_problem_755 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        ∀ A : Finset (EuclideanSpace ℝ (Fin 6)),
          A.card = n →
          (unitEquilateralTriangleCount A : ℝ) ≤ (1 / 27 + ε) * (n : ℝ) ^ 3 :=
  sorry

end
