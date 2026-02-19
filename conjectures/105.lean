import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/--
Erdős Problem #105 (Erdős–Purdy):
Let A, B ⊂ ℝ² be disjoint finite sets with |A| = n and |B| = n - 3,
with not all of A contained on a single line. The conjecture asks whether
there must exist a line containing at least two points from A and no points
from B.

Note: This conjecture has been DISPROVED. Xichuan found three explicit
counterexamples. It remains open whether the result holds with n - 4 (or
more generally with n - O(1) or (1 - o(1))n points in B).
The condition n - 2 is known to fail via a construction of Hickerson.
-/
theorem erdos_problem_105 :
    ∀ n : ℕ, 3 ≤ n →
    ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = n →
      B.card = n - 3 →
      Disjoint A B →
      ¬ Collinear ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) →
      ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
        Module.finrank ℝ L.direction = 1 ∧
        2 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (A : Set _) ∧ p ∈ L} ∧
        ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ (B : Set _) → p ∉ L :=
  sorry
