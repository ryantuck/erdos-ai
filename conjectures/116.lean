import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped ENNReal
open Polynomial MeasureTheory

/-- The lemniscate interior of a complex polynomial p:
    the open sublevel set {z ∈ ℂ : |p(z)| < 1}. -/
def lemniscateInterior (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ < 1}

/-- The 2D area of a subset of ℂ, given by the 2-dimensional Hausdorff measure. -/
noncomputable def area (S : Set ℂ) : ℝ≥0∞ :=
  Measure.hausdorffMeasure 2 S

/--
Erdős–Herzog–Piranian Conjecture (Problem #116) [EHP58, Er61, Er82e, Er90, Er97c]:

Let p(z) = ∏ᵢ (z - zᵢ) be a polynomial of degree n ≥ 1 with all roots zᵢ
in the closed unit disk (|zᵢ| ≤ 1). Then the 2D Lebesgue measure (area) of
the lemniscate interior {z ∈ ℂ : |p(z)| < 1} satisfies

  |{z : |p(z)| < 1}| ≫ n^{-O(1)}.

That is, there exist universal constants κ > 0 and δ > 0 such that for all n ≥ 1
and all such polynomials, the area is at least δ · n^{-κ}.

The lower bound ≫ n^{-4} follows from a result of Pommerenke [Po61].
The stronger lower bound ≫ (log n)^{-1} was proved by Krishnapur, Lundberg,
and Ramachandran [KLR25], which in particular settles this conjecture.

Pólya [Po28] showed the area is always at most π, with equality only when all
roots are equal.
-/
theorem erdos_problem_116 :
    ∃ (κ δ : ℝ), 0 < δ ∧ 0 < κ ∧
    ∀ (n : ℕ), 1 ≤ n →
    ∀ (roots : Fin n → ℂ), (∀ i, ‖roots i‖ ≤ 1) →
    ENNReal.ofReal (δ * (n : ℝ) ^ (-κ)) ≤
      area (lemniscateInterior (∏ i : Fin n, (X - C (roots i)))) :=
  sorry
