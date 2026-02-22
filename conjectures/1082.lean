import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# Erdős Problem #1082

Let A ⊂ ℝ² be a set of n points with no three on a line. Does A determine
at least ⌊n/2⌋ distinct distances?

A conjecture of Szemerédi, who proved this with n/2 replaced by n/3. More
generally, Szemerédi gave a simple proof that if there are no k points on a
line then some point determines ≫ n/k distinct distances.

Tags: geometry | distances
-/

noncomputable section

/-- No three points in the finite set are collinear. -/
def NoThreeCollinear (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, p ≠ q → p ≠ r → q ≠ r →
    ¬Collinear ℝ ({(p : EuclideanSpace ℝ (Fin 2)), q, r} : Set (EuclideanSpace ℝ (Fin 2)))

/-- The number of distinct pairwise distances determined by a finite point set in ℝ². -/
noncomputable def distinctDistanceCount2d (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {d : ℝ | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ d = dist p q}

/--
**Erdős Problem #1082** [Er75f, p.101]:

Let A ⊂ ℝ² be a set of n points with no three on a line. Then A determines
at least ⌊n/2⌋ distinct distances.
-/
theorem erdos_problem_1082
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (hP : NoThreeCollinear P) :
    distinctDistanceCount2d P ≥ P.card / 2 :=
  sorry

end
