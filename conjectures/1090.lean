import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/--
Erdős Problem #1090 (proved):
Let k ≥ 3. Does there exist a finite set A ⊂ ℝ² such that, in any 2-colouring
of A, there exists a line which contains at least k points from A, and all the
points of A on the line have the same colour?

The answer is yes. Erdős [Er75f] notes that Graham and Selfridge proved the
case k = 3. Hunter observed that for sufficiently large n, a generic projection
of [k]^n into ℝ² has this property, by the Hales–Jewett theorem.
-/
theorem erdos_problem_1090 (k : ℕ) (hk : k ≥ 3) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      ∀ c : EuclideanSpace ℝ (Fin 2) → Fin 2,
        ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
          Module.finrank ℝ L.direction = 1 ∧
          k ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (A : Set _) ∧ p ∈ L} ∧
          ∃ color : Fin 2, ∀ p ∈ (A : Set _), p ∈ L → c p = color :=
  sorry
