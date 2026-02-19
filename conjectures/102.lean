import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/--
The number of distinct affine lines in ℝ² that contain at least 4 points from P
(i.e., more than 3 points, as in the problem statement).
-/
noncomputable def fourPlusRichLineCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    4 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}}

/--
Erdős Problem #102 (Erdős–Purdy):

For fixed c > 0, let h_c(n) denote the largest integer h such that: for every
n-point set P in ℝ² with at least c·n² lines each containing more than 3 points
of P, some line contains at least h points of P. (In other words, h_c(n) is the
minimum, over all such configurations P, of the maximum collinearity.)

The conjecture is that h_c(n) → ∞ as n → ∞, i.e., for each fixed c > 0 and
each M : ℕ, there exists N such that for all n ≥ N, every n-point configuration
with at least c·n² four-rich lines must contain some line with at least M points.
-/
theorem erdos_problem_102 :
  ∀ c : ℝ, c > 0 →
    ∀ M : ℕ,
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
          P.card = n →
          c * (n : ℝ) ^ 2 ≤ (fourPlusRichLineCount P : ℝ) →
          ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
            Module.finrank ℝ L.direction = 1 ∧
            M ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L} :=
  sorry
